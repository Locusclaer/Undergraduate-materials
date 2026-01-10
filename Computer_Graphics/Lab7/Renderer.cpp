//
// Created by goksu on 2/25/20.
//

#include "Renderer.hpp"

#include <chrono>
#include <mutex>
#include <thread>
#include "Scene.hpp"

#ifndef THREAD_MODE
#define THREAD_MODE 0  // 默认单线程
#endif

using namespace std::chrono_literals;

inline float deg2rad(const float &deg) { return deg * M_PI / 180.0; }

const float EPSILON = 0.00001;

// The main render function. This where we iterate over all pixels in the image,
// generate primary rays and cast these rays into the scene. The content of the
// framebuffer is saved to a file.
void Renderer::Render(const Scene &scene) {
    std::vector<Vector3f> framebuffer(scene.width * scene.height);

    float scale = tan(deg2rad(scene.fov * 0.5));
    float imageAspectRatio = scene.width / (float) scene.height;
    Vector3f eye_pos(278, 273, -800);
    // change the spp value to change sample ammount
    constexpr int spp = 128;
    std::cout << "SPP: " << spp << "\n";

#if THREAD_MODE == 1
    const int total_pixels = scene.width * scene.height;
    std::atomic_int completed_pixels(0);
    const auto num_threads = std::max(1U, std::thread::hardware_concurrency());

    std::condition_variable cv;
    std::mutex cv_mutex;
    bool all_done = false;
    std::vector<std::thread> workers;

    std::thread progress_thread([&] {
            std::unique_lock lock(cv_mutex);
            while (!all_done) {
                cv.wait_for(lock, 100ms);
                const auto completed = static_cast<float>(completed_pixels.load());
                UpdateProgress(completed / static_cast<float>(total_pixels));
            }
        }
    );

    auto worker = [&](const int start, const int end) {
        for (int index = start; index < end; ++index) {
            const int i = index % scene.width;
            const int j = index / scene.width;

            // generate primary ray direction
            const float x = (2.f * (static_cast<float>(i) + 0.5f) / static_cast<float>(scene.width) - 1) * imageAspectRatio * scale;
            const float y = (1.f - 2.f * (static_cast<float>(j) + 0.5f) / static_cast<float>(scene.height)) * scale;

            Vector3f color{};
            Vector3f dir = normalize(Vector3f(-x, y, 1));
            for (int k = 0; k < spp; k++) {
                color += scene.castRay(Ray(eye_pos, dir), 0);
            }
            color = color / static_cast<float>(spp);
            framebuffer[index] = color;

            if (completed_pixels.fetch_add(1, std::memory_order_relaxed) % 100 == 0) {
                cv.notify_one();
            }
        }
    };
    workers.reserve(num_threads);
    const int size = total_pixels / num_threads;
    for (int t = 0; t < num_threads; ++t) {
        int start = t * size;
        int end = (t == num_threads - 1) ? total_pixels : start + size;
        workers.emplace_back(worker, start, end);
    }

    for (auto &thread : workers) {
        thread.join();
    } {
        std::lock_guard lock(cv_mutex);
        all_done = true;
    }
    cv.notify_one();
    progress_thread.join();
    UpdateProgress(1.f);
#endif

#if THREAD_MODE == 0
    int m{};
    for (uint32_t j = 0; j < scene.height; ++j) {
        for (uint32_t i = 0; i < scene.width; ++i) {
            // generate primary ray direction
            float x = (2 * (i + 0.5) / (float) scene.width - 1) *
                imageAspectRatio * scale;
            float y = (1 - 2 * (j + 0.5) / (float) scene.height) * scale;

            Vector3f dir = normalize(Vector3f(-x, y, 1));
            for (int k = 0; k < spp; k++) {
                framebuffer[m] += scene.castRay(Ray(eye_pos, dir), 0) / spp;
            }
            m++;
        }
        UpdateProgress(j / (float) scene.height);
    }
    UpdateProgress(1.f);
#endif

    // save framebuffer to file
    FILE *fp = fopen("binary.ppm", "wb");
    (void) fprintf(fp, "P6\n%d %d\n255\n", scene.width, scene.height);
    for (auto i = 0; i < scene.height * scene.width; ++i) {
        static unsigned char color[3];
        color[0] = (unsigned char) (255 * std::pow(clamp(0, 1, framebuffer[i].x), 0.6f));
        color[1] = (unsigned char) (255 * std::pow(clamp(0, 1, framebuffer[i].y), 0.6f));
        color[2] = (unsigned char) (255 * std::pow(clamp(0, 1, framebuffer[i].z), 0.6f));
        fwrite(color, 1, 3, fp);
    }
    fclose(fp);
}
