#include <chrono>
#include <iostream>
#include <opencv2/opencv.hpp>
#include <cmath>

std::vector<cv::Point2f> control_points;

void mouse_handler(int event, int x, int y, int flags, void *userdata) 
{
    if (event == cv::EVENT_LBUTTONDOWN && control_points.size() < 4) 
    {
        std::cout << "Left button of the mouse is clicked - position (" << x << ", "
        << y << ")" << '\n';
        control_points.emplace_back(x, y);
    }     
}

void naive_bezier(const std::vector<cv::Point2f> &points, cv::Mat &window) 
{
    auto &p_0 = points[0];
    auto &p_1 = points[1];
    auto &p_2 = points[2];
    auto &p_3 = points[3];

    for (double t = 0.0; t <= 1.0; t += 0.001) 
    {
        auto point = std::pow(1 - t, 3) * p_0 + 3 * t * std::pow(1 - t, 2) * p_1 +
                 3 * std::pow(t, 2) * (1 - t) * p_2 + std::pow(t, 3) * p_3;

        window.at<cv::Vec3b>(point.y, point.x)[2] = 255;
    }
}

cv::Point2f recursive_bezier(const std::vector<cv::Point2f> &control_points, float t) 
{
    // 实现 de Casteljau 算法
    if (control_points.size() == 1) {
        return control_points[0];
    }
    
    std::vector<cv::Point2f> new_control_points;
    
    for (size_t i = 0; i < control_points.size() - 1; ++i) {
        cv::Point2f p1 = control_points[i];
        cv::Point2f p2 = control_points[i + 1];
        cv::Point2f new_point = (1 - t) * p1 + t * p2;
        new_control_points.push_back(new_point);
    }
    
    return recursive_bezier(new_control_points, t);
}

void bezier(const std::vector<cv::Point2f> &control_points, cv::Mat &window) 
{
    // TODO: Iterate through all t = 0 to t = 1 with small steps, and call de Casteljau's 
    // recursive Bezier algorithm.

    // 检查控制点数量是否足够
    if (control_points.size() < 2) {
        return;
    }
    
    // 遍历 t 从 0 到 1
    for (double t = 0.0; t <= 1.0; t += 0.001) {
        // 调用递归函数计算贝塞尔曲线上的点
        cv::Point2f point = recursive_bezier(control_points, t);
        
        // 确保点在图像范围内
        if (point.x >= 0 && point.x < window.cols && point.y >= 0 && point.y < window.rows) {
            // 将点绘制为绿色（BGR格式，绿色在中间通道）
            window.at<cv::Vec3b>(point.y, point.x)[1] = 255;
        }
    }
}

void bezier_antialiased(const std::vector<cv::Point2f> &control_points, cv::Mat &window) 
{
    if (control_points.size() < 2) {
        return;
    }
    
    for (double t = 0.0; t <= 1.0; t += 0.001) {
        cv::Point2f point = recursive_bezier(control_points, t);
        
        // 反走样处理：考虑3x3邻域内的像素
        int x = std::round(point.x);
        int y = std::round(point.y);
        
        for (int dx = -1; dx <= 1; dx++) {
            for (int dy = -1; dy <= 1; dy++) {
                int nx = x + dx;
                int ny = y + dy;
                
                if (nx >= 0 && nx < window.cols && ny >= 0 && ny < window.rows) {
                    cv::Point2f pixel_center(nx + 0.5f, ny + 0.5f);
                    float distance = cv::norm(point - pixel_center);
                    
                    float max_distance = std::sqrt(2.0f);
                    float weight = std::max(0.0f, 1.0f - distance / max_distance);
                    
                    uchar& green_channel = window.at<cv::Vec3b>(ny, nx)[1];
                    green_channel = std::max(green_channel, static_cast<uchar>(255 * weight));
                }
            }
        }
    }
}

int main() 
{
    cv::Mat window = cv::Mat(700, 700, CV_8UC3, cv::Scalar(0));
    cv::cvtColor(window, window, cv::COLOR_BGR2RGB);
    cv::namedWindow("Bezier Curve", cv::WINDOW_AUTOSIZE);

    cv::setMouseCallback("Bezier Curve", mouse_handler, nullptr);

    int key = -1;
    while (key != 27) 
    {
        for (auto &point : control_points) 
        {
            cv::circle(window, point, 3, {255, 255, 255}, 3);
        }

        if (control_points.size() == 4) 
        {
            // naive_bezier(control_points, window);
            // bezier(control_points, window);
            
            // 使用反走样
            bezier_antialiased(control_points, window);

            cv::imshow("Bezier Curve", window);
            cv::imwrite("my_bezier_curve.png", window);
            key = cv::waitKey(0);

            return 0;
        }

        cv::imshow("Bezier Curve", window);
        key = cv::waitKey(20);
    }

    return 0;
}