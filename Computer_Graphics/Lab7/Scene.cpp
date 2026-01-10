//
// Created by Göksu Güvendiren on 2019-05-14.
//

#include "Scene.hpp"


void Scene::buildBVH() {
    printf(" - Generating BVH...\n\n");
    this->bvh = new BVHAccel(objects, 1, BVHAccel::SplitMethod::NAIVE);
}

Intersection Scene::intersect(const Ray &ray) const {
    return this->bvh->Intersect(ray);
}

void Scene::sampleLight(Intersection &pos, float &pdf) const {
    float emit_area_sum = 0;
    for (uint32_t k = 0; k < objects.size(); ++k) {
        if (objects[k]->hasEmit()) {
            emit_area_sum += objects[k]->getArea();
        }
    }
    float p = get_random_float() * emit_area_sum;
    emit_area_sum = 0;
    for (uint32_t k = 0; k < objects.size(); ++k) {
        if (objects[k]->hasEmit()) {
            emit_area_sum += objects[k]->getArea();
            if (p <= emit_area_sum) {
                objects[k]->Sample(pos, pdf);
                break;
            }
        }
    }
}

bool Scene::trace(
    const Ray &ray,
    const std::vector<Object*> &objects,
    float &tNear, uint32_t &index, Object **hitObject) {
    *hitObject = nullptr;
    for (uint32_t k = 0; k < objects.size(); ++k) {
        float tNearK = kInfinity;
        uint32_t indexK;
        Vector2f uvK;
        if (objects[k]->intersect(ray, tNearK, indexK) && tNearK < tNear) {
            *hitObject = objects[k];
            tNear = tNearK;
            index = indexK;
        }
    }


    return (*hitObject != nullptr);
}

// Implementation of Path Tracing
Vector3f Scene::castRay(const Ray &ray, int depth) const {
    // TO DO Implement Path Tracing Algorithm here
    Intersection p_inter = intersect(ray);
    // 没有交点返回黑色
    if (!p_inter.happened) {
        return {};
    }
    // 打到光源，返回光源颜色
    if (p_inter.m->hasEmission()) {
        return p_inter.m->getEmission();
    }

    Vector3f L_dir;
    Intersection x_inter;
    float pdf{};
    // 对光源进行采样
    sampleLight(x_inter, pdf);

    Vector3f p = p_inter.coords;
    Vector3f x = x_inter.coords;
    Vector3f Np = p_inter.normal;
    Vector3f Nx = x_inter.normal;
    Vector3f emit = x_inter.emit;
    Vector3f ws_dir = (x - p).normalized();
    float ws_dis = (x - p).norm();

    // 从 p 点向光源采样点 x 发射一条光线
    Ray ws_ray(p, ws_dir);
    // 如果光线没有被遮挡
    if (Intersection ws_inter = intersect(ws_ray);
        ws_inter.distance - ws_dis > -EPSILON) {
        L_dir = emit * p_inter.m->eval(ray.direction, ws_ray.direction, Np)
            * dotProduct(ws_ray.direction, Np) * dotProduct(-ws_ray.direction, Nx)
            / (ws_dis * ws_dis) / pdf;
    }
    // 俄罗斯轮盘赌
    if (get_random_float() > RussianRoulette) {
        return L_dir;
    }

    Vector3f L_indir;
    Vector3f wi_dir = p_inter.m->sample(ray.direction, Np).normalized();
    Ray wi_ray(p, wi_dir);
    // 如果射线 r 在 q 处撞击一个物体
    if (Intersection wi_inter = intersect(wi_ray);
        wi_inter.happened && !wi_inter.m->hasEmission()) {
        L_indir = castRay(wi_ray, depth + 1)
            * p_inter.m->eval(ray.direction, wi_ray.direction, Np)
            * dotProduct(wi_ray.direction, Np)
            / p_inter.m->pdf(ray.direction, wi_ray.direction, Np)
            / RussianRoulette;
    }

    return L_dir + L_indir;
}
