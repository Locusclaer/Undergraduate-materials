//
// Created by goksu on 4/6/19.
//

#include <algorithm>
#include <vector>
#include "rasterizer.hpp"
#include <opencv2/opencv.hpp>
#include <math.h>


rst::pos_buf_id rst::rasterizer::load_positions(const std::vector<Eigen::Vector3f> &positions)
{
    auto id = get_next_id();
    pos_buf.emplace(id, positions);

    return {id};
}

rst::ind_buf_id rst::rasterizer::load_indices(const std::vector<Eigen::Vector3i> &indices)
{
    auto id = get_next_id();
    ind_buf.emplace(id, indices);

    return {id};
}

rst::col_buf_id rst::rasterizer::load_colors(const std::vector<Eigen::Vector3f> &cols)
{
    auto id = get_next_id();
    col_buf.emplace(id, cols);

    return {id};
}

auto to_vec4(const Eigen::Vector3f& v3, float w = 1.0f)
{
    return Vector4f(v3.x(), v3.y(), v3.z(), w);
}


static bool insideTriangle(float x, float y, const Vector3f* _v)
{   
    // 使用叉积法判断点是否在三角形内
    Vector3f p(x, y, 0);
    
    Vector3f v0 = _v[0];
    Vector3f v1 = _v[1];
    Vector3f v2 = _v[2];
    
    Vector3f edge0 = v1 - v0;
    Vector3f edge1 = v2 - v1;
    Vector3f edge2 = v0 - v2;
    
    Vector3f c0 = p - v0;
    Vector3f c1 = p - v1;
    Vector3f c2 = p - v2;
    
    // 计算叉积
    float cross0 = edge0.x() * c0.y() - edge0.y() * c0.x();
    float cross1 = edge1.x() * c1.y() - edge1.y() * c1.x();
    float cross2 = edge2.x() * c2.y() - edge2.y() * c2.x();
    
    // 如果三个叉积同号，则在三角形内
    return (cross0 > 0 && cross1 > 0 && cross2 > 0) || 
           (cross0 < 0 && cross1 < 0 && cross2 < 0);
}

static std::tuple<float, float, float> computeBarycentric2D(float x, float y, const Vector3f* v)
{
    float c1 = (x*(v[1].y() - v[2].y()) + (v[2].x() - v[1].x())*y + v[1].x()*v[2].y() - v[2].x()*v[1].y()) / (v[0].x()*(v[1].y() - v[2].y()) + (v[2].x() - v[1].x())*v[0].y() + v[1].x()*v[2].y() - v[2].x()*v[1].y());
    float c2 = (x*(v[2].y() - v[0].y()) + (v[0].x() - v[2].x())*y + v[2].x()*v[0].y() - v[0].x()*v[2].y()) / (v[1].x()*(v[2].y() - v[0].y()) + (v[0].x() - v[2].x())*v[1].y() + v[2].x()*v[0].y() - v[0].x()*v[2].y());
    float c3 = (x*(v[0].y() - v[1].y()) + (v[1].x() - v[0].x())*y + v[0].x()*v[1].y() - v[1].x()*v[0].y()) / (v[2].x()*(v[0].y() - v[1].y()) + (v[1].x() - v[0].x())*v[2].y() + v[0].x()*v[1].y() - v[1].x()*v[0].y());
    return {c1,c2,c3};
}

void rst::rasterizer::draw(pos_buf_id pos_buffer, ind_buf_id ind_buffer, col_buf_id col_buffer, Primitive type)
{
    auto& buf = pos_buf[pos_buffer.pos_id];
    auto& ind = ind_buf[ind_buffer.ind_id];
    auto& col = col_buf[col_buffer.col_id];

    float f1 = (50 - 0.1) / 2.0;
    float f2 = (50 + 0.1) / 2.0;

    Eigen::Matrix4f mvp = projection * view * model;
    for (auto& i : ind)
    {
        Triangle t;
        Eigen::Vector4f v[] = {
                mvp * to_vec4(buf[i[0]], 1.0f),
                mvp * to_vec4(buf[i[1]], 1.0f),
                mvp * to_vec4(buf[i[2]], 1.0f)
        };
        //Homogeneous division
        for (auto& vec : v) {
            vec /= vec.w();
        }
        //Viewport transformation
        for (auto & vert : v)
        {
            vert.x() = 0.5*width*(vert.x()+1.0);
            vert.y() = 0.5*height*(vert.y()+1.0);
            vert.z() = vert.z() * f1 + f2;
        }

        for (int i = 0; i < 3; ++i)
        {
            t.setVertex(i, v[i].head<3>());
            t.setVertex(i, v[i].head<3>());
            t.setVertex(i, v[i].head<3>());
        }

        auto col_x = col[i[0]];
        auto col_y = col[i[1]];
        auto col_z = col[i[2]];

        t.setColor(0, col_x[0], col_x[1], col_x[2]);
        t.setColor(1, col_y[0], col_y[1], col_y[2]);
        t.setColor(2, col_z[0], col_z[1], col_z[2]);

        rasterize_triangle(t);
    }
    
    // 在所有三角形绘制完成后，解析超级采样结果
    resolve_supersampling();
}

//Screen space rasterization
void rst::rasterizer::rasterize_triangle(const Triangle& t) {
    auto v = t.toVector4();
    
    // TODO : Find out the bounding box of current triangle.
    // 1. 创建三角形的2维bounding box
    float min_x = std::min(v[0].x(), std::min(v[1].x(), v[2].x()));
    float max_x = std::max(v[0].x(), std::max(v[1].x(), v[2].x()));
    float min_y = std::min(v[0].y(), std::min(v[1].y(), v[2].y()));
    float max_y = std::max(v[0].y(), std::max(v[1].y(), v[2].y()));
    
    // 将bounding box转换为像素坐标
    int min_pixel_x = static_cast<int>(std::floor(min_x));
    int max_pixel_x = static_cast<int>(std::ceil(max_x));
    int min_pixel_y = static_cast<int>(std::floor(min_y));
    int max_pixel_y = static_cast<int>(std::ceil(max_y));
    
    // 确保在屏幕范围内
    min_pixel_x = std::max(0, min_pixel_x);
    max_pixel_x = std::min(width - 1, max_pixel_x);
    min_pixel_y = std::max(0, min_pixel_y);
    max_pixel_y = std::min(height - 1, max_pixel_y);
    
    // 2. 遍历bounding box内的所有像素
    for (int x = min_pixel_x; x <= max_pixel_x; x++) {
        for (int y = min_pixel_y; y <= max_pixel_y; y++) {
            
            // 对每个像素进行2x2超级采样
            for (int sample_id = 0; sample_id < TOTAL_SAMPLES; sample_id++) {
                // 计算采样点的偏移
                float offset_x, offset_y;
                switch(sample_id) {
                    case 0: offset_x = 0.25f; offset_y = 0.25f; break; // 左下
                    case 1: offset_x = 0.75f; offset_y = 0.25f; break; // 右下
                    case 2: offset_x = 0.25f; offset_y = 0.75f; break; // 左上
                    case 3: offset_x = 0.75f; offset_y = 0.75f; break; // 右上
                    default: offset_x = 0.5f; offset_y = 0.5f; break;
                }
                
                float sample_x = x + offset_x;
                float sample_y = y + offset_y;
                
                // 检查采样点是否在三角形内
                if (insideTriangle(sample_x, sample_y, t.v)) {
                    // 计算插值深度值
                    auto[alpha, beta, gamma] = computeBarycentric2D(sample_x, sample_y, t.v);
                    float w_reciprocal = 1.0f / (alpha / v[0].w() + beta / v[1].w() + gamma / v[2].w());
                    float z_interpolated = alpha * v[0].z() / v[0].w() + beta * v[1].z() / v[1].w() + gamma * v[2].z() / v[2].w();
                    z_interpolated *= w_reciprocal;
                    
                    // 获取采样点索引
                    int sample_index = get_sample_index(x, y, sample_id);
                    
                    // 深度测试
                    if (z_interpolated < sample_depth_buf[sample_index]) {
                        // 更新采样点的颜色和深度
                        sample_depth_buf[sample_index] = z_interpolated;
                        sample_color_buf[sample_index] = t.getColor();
                    }
                }
            }
        }
    }
}

void rst::rasterizer::resolve_supersampling() {
    // 将超级采样结果解析到最终帧缓冲区
    for (int x = 0; x < width; x++) {
        for (int y = 0; y < height; y++) {
            Eigen::Vector3f final_color = Eigen::Vector3f::Zero();
            float min_depth = std::numeric_limits<float>::infinity();
            
            // 对每个像素的4个采样点进行平均
            for (int sample_id = 0; sample_id < TOTAL_SAMPLES; sample_id++) {
                int sample_index = get_sample_index(x, y, sample_id);
                final_color += sample_color_buf[sample_index];
                min_depth = std::min(min_depth, sample_depth_buf[sample_index]);
            }
            
            // 计算平均颜色
            final_color /= 4.0f;
            
            // 更新最终帧缓冲区和深度缓冲区
            int pixel_index = get_index(x, y);
            frame_buf[pixel_index] = final_color;
            depth_buf[pixel_index] = min_depth;
        }
    }
}

void rst::rasterizer::set_model(const Eigen::Matrix4f& m)
{
    model = m;
}

void rst::rasterizer::set_view(const Eigen::Matrix4f& v)
{
    view = v;
}

void rst::rasterizer::set_projection(const Eigen::Matrix4f& p)
{
    projection = p;
}

void rst::rasterizer::clear(rst::Buffers buff)
{
    if ((buff & rst::Buffers::Color) == rst::Buffers::Color)
    {
        std::fill(frame_buf.begin(), frame_buf.end(), Eigen::Vector3f{0, 0, 0});
        std::fill(sample_color_buf.begin(), sample_color_buf.end(), Eigen::Vector3f{0, 0, 0});
    }
    if ((buff & rst::Buffers::Depth) == rst::Buffers::Depth)
    {
        std::fill(depth_buf.begin(), depth_buf.end(), std::numeric_limits<float>::infinity());
        std::fill(sample_depth_buf.begin(), sample_depth_buf.end(), std::numeric_limits<float>::infinity());
    }
}

rst::rasterizer::rasterizer(int w, int h) : width(w), height(h)
{
    frame_buf.resize(w * h);
    depth_buf.resize(w * h);
    
    // 初始化超级采样缓冲区
    sample_color_buf.resize(w * h * TOTAL_SAMPLES);
    sample_depth_buf.resize(w * h * TOTAL_SAMPLES, std::numeric_limits<float>::infinity());
}

int rst::rasterizer::get_index(int x, int y)
{
    return (height-1-y)*width + x;
}

int rst::rasterizer::get_sample_index(int x, int y, int sample_id)
{
    return ((height-1-y)*width + x) * TOTAL_SAMPLES + sample_id;
}

void rst::rasterizer::set_pixel(const Eigen::Vector3f& point, const Eigen::Vector3f& color)
{
    //old index: auto ind = point.y() + point.x() * width;
    auto ind = (height-1-point.y())*width + point.x();
    frame_buf[ind] = color;
}

void rst::rasterizer::draw_line(Eigen::Vector3f begin, Eigen::Vector3f end)
{
    // 线框绘制实现（简单版本）
    auto x1 = begin.x();
    auto y1 = begin.y();
    auto x2 = end.x();
    auto y2 = end.y();

    Eigen::Vector3f line_color = {255, 255, 255};

    int x,y,dx,dy,dx1,dy1,px,py,xe,ye,i;

    dx=x2-x1;
    dy=y2-y1;
    dx1=fabs(dx);
    dy1=fabs(dy);
    px=2*dy1-dx1;
    py=2*dx1-dy1;

    if(dy1<=dx1)
    {
        if(dx>=0)
        {
            x=x1;
            y=y1;
            xe=x2;
        }
        else
        {
            x=x2;
            y=y2;
            xe=x1;
        }
        Eigen::Vector3f point = Eigen::Vector3f(x, y, 1.0f);
        set_pixel(point,line_color);
        for(i=0;x<xe;i++)
        {
            x=x+1;
            if(px<0)
            {
                px=px+2*dy1;
            }
            else
            {
                if((dx<0 && dy<0) || (dx>0 && dy>0))
                {
                    y=y+1;
                }
                else
                {
                    y=y-1;
                }
                px=px+2*(dy1-dx1);
            }
            Eigen::Vector3f point = Eigen::Vector3f(x, y, 1.0f);
            set_pixel(point,line_color);
        }
    }
    else
    {
        if(dy>=0)
        {
            x=x1;
            y=y1;
            ye=y2;
        }
        else
        {
            x=x2;
            y=y2;
            ye=y1;
        }
        Eigen::Vector3f point = Eigen::Vector3f(x, y, 1.0f);
        set_pixel(point,line_color);
        for(i=0;y<ye;i++)
        {
            y=y+1;
            if(py<=0)
            {
                py=py+2*dx1;
            }
            else
            {
                if((dx<0 && dy<0) || (dx>0 && dy>0))
                {
                    x=x+1;
                }
                else
                {
                    x=x-1;
                }
                py=py+2*(dx1-dy1);
            }
            Eigen::Vector3f point = Eigen::Vector3f(x, y, 1.0f);
            set_pixel(point,line_color);
        }
    }
}

// clang-format on