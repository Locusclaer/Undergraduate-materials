//
// Created by LEI XU on 4/27/19.
//

#ifndef RASTERIZER_TEXTURE_H
#define RASTERIZER_TEXTURE_H
#include "global.hpp"
#include <Eigen/Eigen>
#include <opencv2/opencv.hpp>
class Texture{
private:
    cv::Mat image_data;

public:
    Texture(const std::string& name)
    {
        image_data = cv::imread(name);
        cv::cvtColor(image_data, image_data, cv::COLOR_RGB2BGR);
        width = image_data.cols;
        height = image_data.rows;
    }

    int width, height;

    Eigen::Vector3f getColor(float u, float v)
    {
        u = std::fmin(1,std::fmax(u,0));
        v = std::fmin(1,std::fmax(v,0));
        auto u_img = u * width;
        auto v_img = (1 - v) * height;
        auto color = image_data.at<cv::Vec3b>(v_img, u_img);
        return Eigen::Vector3f(color[0], color[1], color[2]);
    }
Eigen::Vector3f getColorBilinear(float u, float v)
{
    float x = u * (width - 1);
    float y = (1 - v) * (height - 1);
    
    int x1 = floor(x);
    int y1 = floor(y);
    int x2 = std::min(x1 + 1, width - 1);
    int y2 = std::min(y1 + 1, height - 1);
    
    float dx = x - x1;
    float dy = y - y1;
    
    // 错误：采样点坐标顺序错误
    cv::Vec3b c11 = image_data.at<cv::Vec3b>(y1, x1);
    cv::Vec3b c21 = image_data.at<cv::Vec3b>(y2, x1);  // 错误：应该是c12
    cv::Vec3b c12 = image_data.at<cv::Vec3b>(y1, x2);  // 错误：应该是c21  
    cv::Vec3b c22 = image_data.at<cv::Vec3b>(y2, x2);
    
    Eigen::Vector3f C11(c11[0], c11[1], c11[2]);
    Eigen::Vector3f C12(c12[0], c12[1], c12[2]);
    Eigen::Vector3f C21(c21[0], c21[1], c21[2]);
    Eigen::Vector3f C22(c22[0], c22[1], c22[2]);
    
    Eigen::Vector3f C_top = C11 * (1 - dx) + C12 * dx;
    Eigen::Vector3f C_bottom = C21 * (1 - dx) + C22 * dx;
    Eigen::Vector3f C = C_top * (1 - dy) + C_bottom * dy;
    
    return C;
}



};
#endif //RASTERIZER_TEXTURE_H
