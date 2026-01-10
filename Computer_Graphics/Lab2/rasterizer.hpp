//
// Created by goksu on 4/6/19.
//

#pragma once

#include <Eigen/Eigen>
#include <algorithm>
#include "global.hpp"
#include "Triangle.hpp"
using namespace Eigen;

namespace rst
{
    enum class Buffers
    {
        Color = 1,
        Depth = 2
    };

    inline Buffers operator|(Buffers a, Buffers b)
    {
        return Buffers((int)a | (int)b);
    }

    inline Buffers operator&(Buffers a, Buffers b)
    {
        return Buffers((int)a & (int)b);
    }

    enum class Primitive
    {
        Line,
        Triangle
    };

    /*
     * For the curious : The draw function takes two buffer id's as its arguments. These two structs
     * make sure that if you mix up with their orders, the compiler won't compile it.
     * Aka : Type safety
     * */
    struct pos_buf_id
    {
        int pos_id = 0;
    };

    struct ind_buf_id
    {
        int ind_id = 0;
    };

    struct col_buf_id
    {
        int col_id = 0;
    };

    class rasterizer
    {
    public:
        rasterizer(int w, int h);
        pos_buf_id load_positions(const std::vector<Eigen::Vector3f>& positions);
        ind_buf_id load_indices(const std::vector<Eigen::Vector3i>& indices);
        col_buf_id load_colors(const std::vector<Eigen::Vector3f>& colors);

        void set_model(const Eigen::Matrix4f& m);
        void set_view(const Eigen::Matrix4f& v);
        void set_projection(const Eigen::Matrix4f& p);

        void set_pixel(const Eigen::Vector3f& point, const Eigen::Vector3f& color);

        void clear(Buffers buff);

        void draw(pos_buf_id pos_buffer, ind_buf_id ind_buffer, col_buf_id col_buffer, Primitive type);

        std::vector<Eigen::Vector3f>& frame_buffer() { return frame_buf; }

    private:
        void draw_line(Eigen::Vector3f begin, Eigen::Vector3f end);

        void rasterize_triangle(const Triangle& t);
        void resolve_supersampling(); // 新增：解析超级采样结果

        // VERTEX SHADER -> MVP -> Clipping -> /.W -> VIEWPORT -> DRAWLINE/DRAWTRI -> FRAGSHADER

    private:
        Eigen::Matrix4f model;
        Eigen::Matrix4f view;
        Eigen::Matrix4f projection;

        std::map<int, std::vector<Eigen::Vector3f>> pos_buf;
        std::map<int, std::vector<Eigen::Vector3i>> ind_buf;
        std::map<int, std::vector<Eigen::Vector3f>> col_buf;

        std::vector<Eigen::Vector3f> frame_buf;        // 最终帧缓冲区
        std::vector<float> depth_buf;                  // 最终深度缓冲区

        // 超级采样缓冲区
        std::vector<Eigen::Vector3f> sample_color_buf; // 采样点颜色缓冲区
        std::vector<float> sample_depth_buf;           // 采样点深度缓冲区

        int width, height;
        
        // 超级采样参数
        static const int SAMPLE_RATE = 2;             // 2x2 超级采样
        static const int TOTAL_SAMPLES = 4;           // 每个像素4个采样点

        int get_index(int x, int y);
        int get_sample_index(int x, int y, int sample_id); // 新增：获取采样点索引

        int next_id = 0;
        int get_next_id() { return next_id++; }
    };
}