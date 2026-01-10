cmake_minimum_required(VERSION 3.10)
project(RayTracing)

# 设置 C++ 标准
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 添加可执行文件 - 包含图中所有的源文件
add_executable(Raytracing
    main.cpp
    Renderer.cpp
    Scene.cpp
    # 注意：图中没有 Sphere.cpp 和 Triangle.cpp，只有头文件
    # 如果 Sphere 和 Triangle 的实现包含在头文件中，则不需要添加
)

# 包含当前目录（所有头文件都在当前目录）
target_include_directories(Raytracing PRIVATE .)

# 添加编译优化选项
target_compile_options(Raytracing PRIVATE -O2)

# 设置输出目录（可选）
set_target_properties(Raytracing PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)