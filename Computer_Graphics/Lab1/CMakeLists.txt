cmake_minimum_required(VERSION 3.10)
project(Rasterizer)

# 手动指定 Eigen 和 OpenCV 的路径
set(EIGEN3_INCLUDE_DIR "/opt/homebrew/opt/eigen/include/eigen3")
set(OpenCV_DIR "/opt/homebrew/opt/opencv/share/OpenCV")

find_package(OpenCV REQUIRED)
find_package(Eigen3 REQUIRED)  # 查找 Eigen

set(CMAKE_CXX_STANDARD 17)

# 添加头文件路径
include_directories(
    ${OpenCV_INCLUDE_DIRS}
    ${EIGEN3_INCLUDE_DIR}
    /opt/homebrew/opt/opencv/include/opencv4
)

add_executable(Rasterizer main.cpp rasterizer.hpp rasterizer.cpp Triangle.hpp Triangle.cpp)
target_link_libraries(Rasterizer ${OpenCV_LIBS})