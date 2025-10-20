#include "Triangle.hpp"
#include "rasterizer.hpp"
#include <Eigen/Eigen>
#include <iostream>
#include <opencv2/opencv.hpp>

constexpr double MY_PI = 3.1415926;

Eigen::Matrix4f get_view_matrix(Eigen::Vector3f eye_pos)
{
    Eigen::Matrix4f view = Eigen::Matrix4f::Identity();

    Eigen::Matrix4f translate;
    translate << 1, 0, 0, -eye_pos[0], 0, 1, 0, -eye_pos[1], 0, 0, 1,
        -eye_pos[2], 0, 0, 0, 1;

    view = translate * view;

    return view;
}

Eigen::Matrix4f get_model_matrix(float rotation_angle)
{
    Eigen::Matrix4f model = Eigen::Matrix4f::Identity();

    rotation_angle = rotation_angle * MY_PI / 180.f;

    model << cos(rotation_angle), -sin(rotation_angle), 0, 0,
             sin(rotation_angle),  cos(rotation_angle), 0, 0,
                        0,             0, 1, 0,
                        0,             0, 0, 1;

    return model;
}

Eigen::Matrix4f get_projection_matrix(float eye_fov, float aspect_ratio,
                                      float zNear, float zFar)
{
    Eigen::Matrix4f projection = Eigen::Matrix4f::Identity();

    eye_fov = eye_fov * MY_PI / 180.f;
    float tan_half_fov = tan(eye_fov / 2);

    // 透视投影矩阵转正交投影矩阵
    Eigen::Matrix4f persp_to_ortho;
    persp_to_ortho << zNear, 0,     0,           0,
                      0,     zNear, 0,           0,
                      0,     0,     zNear + zFar, -zNear * zFar,
                      0,     0,     1,           0;

    
    // 正交投影
    float top = tan_half_fov * zNear;
    float bottom = -top;
    float right = top * aspect_ratio;
    float left = -right;
    
    Eigen::Matrix4f ortho_translate = Eigen::Matrix4f::Identity();
    ortho_translate << 1, 0, 0, -(right + left)/2,
                       0, 1, 0, -(top + bottom)/2,
                       0, 0, 1, -(zNear + zFar)/2,
                       0, 0, 0, 1;
    
    Eigen::Matrix4f ortho_scale = Eigen::Matrix4f::Identity();
    ortho_scale << 2/(right - left), 0, 0, 0,
                   0, 2/(top - bottom), 0, 0,
                   0, 0, 2/(zNear - zFar), 0,
                   0, 0, 0, 1;
    
    Eigen::Matrix4f ortho = ortho_scale * ortho_translate;
    
    projection = ortho * persp_to_ortho;

    return projection;
}

Eigen::Matrix4f get_rotation(Eigen::Vector3f axis, float angle) {
    Eigen::Matrix4f rotation = Eigen::Matrix4f::Identity();

    // 归一化旋转轴
    axis.normalize();
    
    angle = angle * MY_PI / 180.f;
    
    // 罗德里格斯旋转公式
    rotation << cos(angle) + (1 - cos(angle)) * axis[0] * axis[0],
                (1 - cos(angle)) * axis[0] * axis[1] - axis[2] * sin(angle),
                (1 - cos(angle)) * axis[0] * axis[2] + axis[1] * sin(angle), 0,
                (1 - cos(angle)) * axis[0] * axis[1] + axis[2] * sin(angle),
                cos(angle) + (1 - cos(angle)) * axis[1] * axis[1],
                (1 - cos(angle)) * axis[1] * axis[2] - axis[0] * sin(angle), 0,
                (1 - cos(angle)) * axis[0] * axis[2] - axis[1] * sin(angle),
                (1 - cos(angle)) * axis[1] * axis[2] + axis[0] * sin(angle),
                cos(angle) + (1 - cos(angle)) * axis[2] * axis[2], 0,
                0, 0, 0, 1;
    
    return rotation;
}

int main(int argc, const char** argv)
{
    float angle = 0;
    bool command_line = false;
    std::string filename = "output.png";
    
    // 添加绕任意轴旋转的参数
    bool use_axis_rotation = false;
    Eigen::Vector3f rotation_axis(1.0f, 1.0f, 1.0f); // 默认旋转轴

    if (argc >= 3) {
        command_line = true;
        angle = std::stof(argv[2]); // -r by default
        if (argc == 4) {
            filename = std::string(argv[3]);
        }
        else if (argc >= 7) {
            // 命令行模式下也支持绕任意轴旋转
            use_axis_rotation = true;
            rotation_axis = Eigen::Vector3f(
                std::stof(argv[4]), 
                std::stof(argv[5]), 
                std::stof(argv[6])
            );
        }
    }

    rst::rasterizer r(700, 700);

    Eigen::Vector3f eye_pos = {0, 0, 5};

    std::vector<Eigen::Vector3f> pos{{2, 0, -2}, {0, 2, -2}, {-2, 0, -2}};

    std::vector<Eigen::Vector3i> ind{{0, 1, 2}};

    auto pos_id = r.load_positions(pos);
    auto ind_id = r.load_indices(ind);

    int key = 0;
    int frame_count = 0;

    if (command_line) {
        r.clear(rst::Buffers::Color | rst::Buffers::Depth);

        Eigen::Matrix4f model;
        if (use_axis_rotation) {
            model = get_rotation(rotation_axis, angle);
        } else {
            model = get_model_matrix(angle);
        }
        
        r.set_model(model);
        r.set_view(get_view_matrix(eye_pos));
        r.set_projection(get_projection_matrix(45, 1, 0.1, 50));

        r.draw(pos_id, ind_id, rst::Primitive::Triangle);
        cv::Mat image(700, 700, CV_32FC3, r.frame_buffer().data());
        image.convertTo(image, CV_8UC3, 1.0f);

        cv::imwrite(filename, image);

        return 0;
    }

    while (key != 27) {
        r.clear(rst::Buffers::Color | rst::Buffers::Depth);

        Eigen::Matrix4f model;
        if (use_axis_rotation) {
            model = get_rotation(rotation_axis, angle);
        } else {
            model = get_model_matrix(angle);
        }
        
        r.set_model(model);
        r.set_view(get_view_matrix(eye_pos));
        r.set_projection(get_projection_matrix(45, 1, 0.1, 50));

        r.draw(pos_id, ind_id, rst::Primitive::Triangle);

        cv::Mat image(700, 700, CV_32FC3, r.frame_buffer().data());
        image.convertTo(image, CV_8UC3, 1.0f);
        cv::imshow("image", image);
        key = cv::waitKey(10);

        std::cout << "frame count: " << frame_count++ << '\n';
        std::cout << "angle: " << angle << '\n';
        if (use_axis_rotation) {
            std::cout << "rotation axis: (" << rotation_axis[0] << ", " 
                      << rotation_axis[1] << ", " << rotation_axis[2] << ")\n";
        }

        if (key == 'a') {
            angle += 10;
        }
        else if (key == 'd') {
            angle -= 10;
        }
        else if (key == 'r') {
            // 切换旋转模式：绕Z轴 vs 绕任意轴
            use_axis_rotation = !use_axis_rotation;
            std::cout << "Switched rotation mode: " 
                      << (use_axis_rotation ? "Axis rotation" : "Z-axis rotation") 
                      << std::endl;
        }
        else if (key == 'x') {
            // 绕X轴旋转
            use_axis_rotation = true;
            rotation_axis = Eigen::Vector3f(1.0f, 0.0f, 0.0f);
            std::cout << "Rotation axis set to X-axis" << std::endl;
        }
        else if (key == 'y') {
            // 绕Y轴旋转
            use_axis_rotation = true;
            rotation_axis = Eigen::Vector3f(0.0f, 1.0f, 0.0f);
            std::cout << "Rotation axis set to Y-axis" << std::endl;
        }
        else if (key == 'z') {
            // 绕Z轴旋转
            use_axis_rotation = true;
            rotation_axis = Eigen::Vector3f(0.0f, 0.0f, 1.0f);
            std::cout << "Rotation axis set to Z-axis" << std::endl;
        }
        else if (key == 'v') {
            // 绕对角线轴旋转
            use_axis_rotation = true;
            rotation_axis = Eigen::Vector3f(1.0f, 1.0f, 1.0f).normalized();
            std::cout << "Rotation axis set to diagonal axis" << std::endl;
        }
    }

    return 0;
}