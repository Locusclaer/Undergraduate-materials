cmake_minimum_required(VERSION 3.10)
project(BezierCurve)

# 设置 C++ 标准
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 手动设置 OpenCV 路径（根据你的安装）
set(OpenCV_DIR "/opt/homebrew/opt/opencv/lib/cmake/opencv4")

# 查找 OpenCV
find_package(OpenCV REQUIRED)

# 输出信息用于调试
message(STATUS "OpenCV version: ${OpenCV_VERSION}")
message(STATUS "OpenCV include dirs: ${OpenCV_INCLUDE_DIRS}")
message(STATUS "OpenCV libraries: ${OpenCV_LIBS}")

# 创建可执行文件
add_executable(BezierCurve main.cpp)

# 链接 OpenCV 库
target_link_libraries(BezierCurve ${OpenCV_LIBS})

# 包含头文件目录
target_include_directories(BezierCurve PRIVATE ${OpenCV_INCLUDE_DIRS})