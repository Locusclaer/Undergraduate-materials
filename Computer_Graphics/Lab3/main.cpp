#include <iostream>
#include <opencv2/opencv.hpp>

#include "global.hpp"
#include "rasterizer.hpp"
#include "Triangle.hpp"
#include "Shader.hpp"
#include "Texture.hpp"
#include "OBJ_Loader.h"

Eigen::Matrix4f get_view_matrix(Eigen::Vector3f eye_pos)
{
    Eigen::Matrix4f view = Eigen::Matrix4f::Identity();

    Eigen::Matrix4f translate;
    translate << 1,0,0,-eye_pos[0],
                 0,1,0,-eye_pos[1],
                 0,0,1,-eye_pos[2],
                 0,0,0,1;

    view = translate*view;

    return view;
}

Eigen::Matrix4f get_model_matrix(float angle)
{
    Eigen::Matrix4f rotation;
    angle = angle * MY_PI / 180.f;
    rotation << cos(angle), 0, sin(angle), 0,
                0, 1, 0, 0,
                -sin(angle), 0, cos(angle), 0,
                0, 0, 0, 1;

    Eigen::Matrix4f scale;
    scale << 2.5, 0, 0, 0,
              0, 2.5, 0, 0,
              0, 0, 2.5, 0,
              0, 0, 0, 1;

    Eigen::Matrix4f translate;
    translate << 1, 0, 0, 0,
            0, 1, 0, 0,
            0, 0, 1, 0,
            0, 0, 0, 1;

    return translate * rotation * scale;
}

Eigen::Matrix4f get_projection_matrix(float eye_fov, float aspect_ratio, float zNear, float zFar)
{
    Eigen::Matrix4f projection = Eigen::Matrix4f::Identity();

    // 修正：使用 -zNear 因为相机看向 -z 方向
    float fov_rad = eye_fov * M_PI / 180.0f;
    float top = tan(fov_rad / 2.0f) * (-zNear);
    float bottom = -top;
    float right = top * aspect_ratio;
    float left = -right;

    // 透视到正交投影矩阵
    Eigen::Matrix4f persp_to_ortho;
    persp_to_ortho << zNear, 0, 0, 0,
                      0, zNear, 0, 0,
                      0, 0, zNear + zFar, -zNear * zFar,
                      0, 0, 1, 0;

    // 正交投影矩阵
    Eigen::Matrix4f ortho;
    ortho << 2.0f/(right-left), 0, 0, -(right+left)/(right-left),
             0, 2.0f/(top-bottom), 0, -(top+bottom)/(top-bottom),
             0, 0, 2.0f/(zNear-zFar), -(zNear+zFar)/(zNear-zFar),
             0, 0, 0, 1;

    projection = ortho * persp_to_ortho;
    return projection;
}

Eigen::Vector3f vertex_shader(const vertex_shader_payload& payload)
{
    return payload.position;
}

Eigen::Vector3f normal_fragment_shader(const fragment_shader_payload& payload)
{
    Eigen::Vector3f return_color = (payload.normal.head<3>().normalized() + Eigen::Vector3f(1.0f, 1.0f, 1.0f)) / 2.f;
    Eigen::Vector3f result;
    result << return_color.x() * 255, return_color.y() * 255, return_color.z() * 255;
    return result;
}

static Eigen::Vector3f reflect(const Eigen::Vector3f& vec, const Eigen::Vector3f& axis)
{
    auto costheta = vec.dot(axis);
    return (2 * costheta * axis - vec).normalized();
}

struct light
{
    Eigen::Vector3f position;
    Eigen::Vector3f intensity;
};

Eigen::Vector3f texture_fragment_shader(const fragment_shader_payload& payload)
{
    Eigen::Vector3f texture_color = Eigen::Vector3f(0, 0, 0);

    if (payload.texture)
    {
        // 使用双线性插值
        texture_color =
            payload.texture->getColorBilinear(payload.tex_coords.x(),
                                              payload.tex_coords.y()) / 255.f;
    }

    Eigen::Vector3f ka = Eigen::Vector3f(0.005, 0.005, 0.005);
    Eigen::Vector3f kd = texture_color;
    Eigen::Vector3f ks = Eigen::Vector3f(0.7937, 0.7937, 0.7937);

    auto l1 = light{{20, 20, 20}, {500, 500, 500}};
    auto l2 = light{{-20, 20, 0}, {500, 500, 500}};
    std::vector<light> lights = {l1, l2};

    Eigen::Vector3f amb_light_intensity{10, 10, 10};
    Eigen::Vector3f eye_pos{0, 0, 10};
    float p = 150;

    Eigen::Vector3f point = payload.view_pos;
    Eigen::Vector3f normal = payload.normal;

    Eigen::Vector3f result_color = ka.cwiseProduct(amb_light_intensity);

    for (auto& light : lights)
    {
        Eigen::Vector3f light_dir = (light.position - point).normalized();
        Eigen::Vector3f view_dir = (eye_pos - point).normalized();
        Eigen::Vector3f h = (light_dir + view_dir).normalized();

        float r2 = (light.position - point).squaredNorm();

        float diff = std::max(0.0f, normal.dot(light_dir));
        float spec = std::pow(std::max(0.0f, normal.dot(h)), p);

        Eigen::Vector3f diffuse = kd.cwiseProduct(light.intensity / r2) * diff;
        Eigen::Vector3f specular = ks.cwiseProduct(light.intensity / r2) * spec;

        result_color += diffuse + specular;
    }

    return result_color * 255.f;
}

Eigen::Vector3f phong_fragment_shader(const fragment_shader_payload& payload)
{
    Eigen::Vector3f ka = Eigen::Vector3f(0.005, 0.005, 0.005);
    Eigen::Vector3f kd = payload.color;
    Eigen::Vector3f ks = Eigen::Vector3f(0.7937, 0.7937, 0.7937);

    auto l1 = light{{20, 20, 20}, {500, 500, 500}};
    auto l2 = light{{-20, 20, 0}, {500, 500, 500}};

    std::vector<light> lights = {l1, l2};
    Eigen::Vector3f amb_light_intensity{10, 10, 10};
    Eigen::Vector3f eye_pos{0, 0, 10};

    float p = 150;

    Eigen::Vector3f color = payload.color;
    Eigen::Vector3f point = payload.view_pos;
    Eigen::Vector3f normal = payload.normal;

    Eigen::Vector3f result_color = {0, 0, 0};
    
    // 环境光分量 (与光源位置无关)
    Eigen::Vector3f ambient = ka.cwiseProduct(amb_light_intensity);
    result_color += ambient;

    for (auto& light : lights)
    {
        // TODO: For each light source in the code, calculate what the *ambient*, *diffuse*, and *specular* 
        // components are. Then, accumulate that result on the *result_color* object.
        
        // 计算光线方向 (从表面点到光源)
        Eigen::Vector3f light_dir = (light.position - point).normalized();
        // 计算视线方向 (从表面点到相机)
        Eigen::Vector3f view_dir = (eye_pos - point).normalized();
        // 计算半程向量 (Blinn-Phong 的关键)
        Eigen::Vector3f half_vector = (light_dir + view_dir).normalized();
        
        // 计算光线距离的平方 (用于衰减)
        float r_square = (light.position - point).squaredNorm();
        
        // 漫反射分量
        float diff_coeff = std::max(0.0f, normal.dot(light_dir));
        Eigen::Vector3f diffuse = kd.cwiseProduct(light.intensity / r_square) * diff_coeff;
        
        // 高光分量 (Blinn-Phong 模型)
        float spec_coeff = std::pow(std::max(0.0f, normal.dot(half_vector)), p);
        Eigen::Vector3f specular = ks.cwiseProduct(light.intensity / r_square) * spec_coeff;
        
        // 累加到最终颜色
        result_color += diffuse + specular;
    }

    return result_color * 255.f;
}



Eigen::Vector3f displacement_fragment_shader(const fragment_shader_payload& payload)
{
    Eigen::Vector3f ka = Eigen::Vector3f(0.005, 0.005, 0.005);
    Eigen::Vector3f kd = payload.color;
    Eigen::Vector3f ks = Eigen::Vector3f(0.7937, 0.7937, 0.7937);

    auto l1 = light{{20, 20, 20}, {500, 500, 500}};
    auto l2 = light{{-20, 20, 0}, {500, 500, 500}};

    std::vector<light> lights = {l1, l2};
    Eigen::Vector3f amb_light_intensity{10, 10, 10};
    Eigen::Vector3f eye_pos{0, 0, 10};

    float p = 150;

    Eigen::Vector3f color = payload.color; 
    Eigen::Vector3f point = payload.view_pos;
    Eigen::Vector3f normal = payload.normal.normalized(); // 确保法线归一化

    float kh = 0.2, kn = 0.1;
    
    // 安全的纹理采样函数，防止越界
    auto safe_get_height = [&](float u_val, float v_val) -> float {
        u_val = std::min(1.0f, std::max(0.0f, u_val));
        v_val = std::min(1.0f, std::max(0.0f, v_val));
        return payload.texture->getColor(u_val, v_val).norm();
    };

    // 获取纹理坐标
    float u = payload.tex_coords.x();
    float v = payload.tex_coords.y();
    
    // 获取纹理尺寸
    float w = payload.texture->width;
    float h = payload.texture->height;

    // 安全地获取高度值
    float huv = safe_get_height(u, v);
    float hu1v = safe_get_height(u + 1.0f/w, v);
    float huv1 = safe_get_height(u, v + 1.0f/h);

    // 计算切线向量 t
    float x = normal.x();
    float y = normal.y();
    float z = normal.z();
    Eigen::Vector3f t;
    float sqrt_xx_zz = sqrt(x*x + z*z);
    t << x*y/sqrt_xx_zz, sqrt_xx_zz, z*y/sqrt_xx_zz;
    t.normalize(); // 归一化切线向量

    // 计算副切线向量 b
    Eigen::Vector3f b = normal.cross(t);
    b.normalize(); // 归一化副切线向量

    // 构造 TBN 矩阵
    Eigen::Matrix3f TBN;
    TBN.col(0) = t;
    TBN.col(1) = b;
    TBN.col(2) = normal;

    // 计算高度图的偏导数
    float dU = kh * kn * (hu1v - huv);
    float dV = kh * kn * (huv1 - huv);

    // 计算切线空间的法线扰动
    Eigen::Vector3f ln(-dU, -dV, 1.0f);
    ln.normalize();

    // 应用位移映射：移动顶点位置
    Eigen::Vector3f displaced_point = point + kn * normal * huv;

    // 计算扰动后的法线
    Eigen::Vector3f perturbed_normal = (TBN * ln).normalized();

    // 光照计算
    Eigen::Vector3f result_color = {0, 0, 0};
    
    // 环境光分量
    Eigen::Vector3f ambient = ka.cwiseProduct(amb_light_intensity);
    result_color += ambient;

    for (auto& light : lights)
    {
        // 使用位移后的点计算光照
        Eigen::Vector3f light_dir = (light.position - displaced_point).normalized();
        Eigen::Vector3f view_dir = (eye_pos - displaced_point).normalized();
        Eigen::Vector3f half_vector = (light_dir + view_dir).normalized();
        
        float r_square = (light.position - displaced_point).squaredNorm();
        
        // 漫反射分量使用扰动后的法线
        float diff_coeff = std::max(0.0f, perturbed_normal.dot(light_dir));
        Eigen::Vector3f diffuse = kd.cwiseProduct(light.intensity / r_square) * diff_coeff;
        
        // 高光分量使用扰动后的法线
        float spec_coeff = std::pow(std::max(0.0f, perturbed_normal.dot(half_vector)), p);
        Eigen::Vector3f specular = ks.cwiseProduct(light.intensity / r_square) * spec_coeff;
        
        result_color += diffuse + specular;
    }

    return result_color * 255.f;
}

Eigen::Vector3f bump_fragment_shader(const fragment_shader_payload& payload)
{
    Eigen::Vector3f normal = payload.normal.normalized();

    float kh = 0.2, kn = 0.1;

    // TBN 构造
    float x = normal.x(), y = normal.y(), z = normal.z();
    Eigen::Vector3f t;
    if (fabs(x) > fabs(z))
        t = Eigen::Vector3f(-y, x, 0).normalized();
    else
        t = Eigen::Vector3f(0, -z, y).normalized();
    Eigen::Vector3f b = normal.cross(t);
    Eigen::Matrix3f TBN;
    TBN << t, b, normal;

    // 纹理坐标
    float u = payload.tex_coords.x();
    float v = payload.tex_coords.y();

    float w = payload.texture->width;
    float h = payload.texture->height;

    // 取高度 h(u,v)
    float huv   = payload.texture->getColor(u, v).norm();
    float hu1v  = payload.texture->getColor(std::min(u + 1.0f/w, 1.0f), v).norm();
    float huv1  = payload.texture->getColor(u, std::min(v + 1.0f/h, 1.0f)).norm();

    float dU = kh * kn * (hu1v - huv);
    float dV = kh * kn * (huv1 - huv);

    // 局部扰动法线
    Eigen::Vector3f ln(-dU, -dV, 1.0f);

    // 计算扰动后的世界空间 normal
    Eigen::Vector3f perturbed = (TBN * ln).normalized();

    // ⭐ 映射到 0~1，再乘 255，输出 RGB 可视化法线图 ⭐
    Eigen::Vector3f visualize;
    visualize = (perturbed + Eigen::Vector3f(1,1,1)) * 0.5f * 255.0f;

    return visualize;
}

int main(int argc, const char** argv)
{
    std::vector<Triangle*> TriangleList;

    float angle = 140.0;
    bool command_line = false;

    std::string filename = "output.png";
    objl::Loader Loader;
    std::string obj_path = "../models/spot/";

    // Load .obj File
    bool loadout = Loader.LoadFile("../models/spot/spot_triangulated_good.obj");
    for(auto mesh:Loader.LoadedMeshes)
    {
        for(int i=0;i<mesh.Vertices.size();i+=3)
        {
            Triangle* t = new Triangle();
            for(int j=0;j<3;j++)
            {
                t->setVertex(j,Vector4f(mesh.Vertices[i+j].Position.X,mesh.Vertices[i+j].Position.Y,mesh.Vertices[i+j].Position.Z,1.0));
                t->setNormal(j,Vector3f(mesh.Vertices[i+j].Normal.X,mesh.Vertices[i+j].Normal.Y,mesh.Vertices[i+j].Normal.Z));
                t->setTexCoord(j,Vector2f(mesh.Vertices[i+j].TextureCoordinate.X, mesh.Vertices[i+j].TextureCoordinate.Y));
            }
            TriangleList.push_back(t);
        }
    }

    rst::rasterizer r(700, 700);

    auto texture_path = "hmap.jpg";
    r.set_texture(Texture(obj_path + texture_path));

    std::function<Eigen::Vector3f(fragment_shader_payload)> active_shader = phong_fragment_shader;

    if (argc >= 2)
    {
        command_line = true;
        filename = std::string(argv[1]);

        if (argc == 3 && std::string(argv[2]) == "texture")
        {
            std::cout << "Rasterizing using the texture shader\n";
            active_shader = texture_fragment_shader;
            texture_path = "spot_texture.png";
            r.set_texture(Texture(obj_path + texture_path));
        }
        else if (argc == 3 && std::string(argv[2]) == "normal")
        {
            std::cout << "Rasterizing using the normal shader\n";
            active_shader = normal_fragment_shader;
        }
        else if (argc == 3 && std::string(argv[2]) == "phong")
        {
            std::cout << "Rasterizing using the phong shader\n";
            active_shader = phong_fragment_shader;
        }
        else if (argc == 3 && std::string(argv[2]) == "bump")
        {
            std::cout << "Rasterizing using the bump shader\n";
            active_shader = bump_fragment_shader;
        }
        else if (argc == 3 && std::string(argv[2]) == "displacement")
        {
            std::cout << "Rasterizing using the displacement shader\n";
            active_shader = displacement_fragment_shader;
        }
    }

    Eigen::Vector3f eye_pos = {0,0,10};

    r.set_vertex_shader(vertex_shader);
    r.set_fragment_shader(active_shader);

    int key = 0;
    int frame_count = 0;

    if (command_line)
    {
        r.clear(rst::Buffers::Color | rst::Buffers::Depth);
        r.set_model(get_model_matrix(angle));
        r.set_view(get_view_matrix(eye_pos));
        r.set_projection(get_projection_matrix(45.0, 1, 0.1, 50));

        r.draw(TriangleList);
        cv::Mat image(700, 700, CV_32FC3, r.frame_buffer().data());
        image.convertTo(image, CV_8UC3, 1.0f);
        cv::cvtColor(image, image, cv::COLOR_RGB2BGR);

        cv::imwrite(filename, image);

        return 0;
    }

    while(key != 27)
    {
        r.clear(rst::Buffers::Color | rst::Buffers::Depth);

        r.set_model(get_model_matrix(angle));
        r.set_view(get_view_matrix(eye_pos));
        r.set_projection(get_projection_matrix(45.0, 1, 0.1, 50));

        //r.draw(pos_id, ind_id, col_id, rst::Primitive::Triangle);
        r.draw(TriangleList);
        cv::Mat image(700, 700, CV_32FC3, r.frame_buffer().data());
        image.convertTo(image, CV_8UC3, 1.0f);
        cv::cvtColor(image, image, cv::COLOR_RGB2BGR);

        cv::imshow("image", image);
        cv::imwrite(filename, image);
        key = cv::waitKey(10);

        if (key == 'a' )
        {
            angle -= 0.1;
        }
        else if (key == 'd')
        {
            angle += 0.1;
        }

    }
    return 0;
}
