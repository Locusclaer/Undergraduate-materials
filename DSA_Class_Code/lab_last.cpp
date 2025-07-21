#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

// 稀疏矩阵表示 (COO格式)
struct SparseMatrix {
    vector<int> row_indices;
    vector<int> col_indices;
    vector<float> values;
    int rows;
    int cols;

    SparseMatrix(int r, int c) : rows(r), cols(c) {}
};

// 图类声明
class Graph {
private:
    int num_nodes;
    SparseMatrix adj_matrix;

public:
    Graph(int n) : num_nodes(n), adj_matrix(n, n) {}
    void add_edge(int u, int v, float weight = 1.0f);
    const SparseMatrix& get_adj_matrix() const;
    bool is_connected();
    void print_adj_matrix();
};

// 图类方法实现
void Graph::add_edge(int u, int v, float weight) {
    if (u < 0 || u >= num_nodes || v < 0 || v >= num_nodes) {
        cerr << "Invalid node index!" << endl;
        return;
    }
    adj_matrix.row_indices.push_back(u);
    adj_matrix.col_indices.push_back(v);
    adj_matrix.values.push_back(weight);
}

const SparseMatrix& Graph::get_adj_matrix() const {
    return adj_matrix;
}

bool Graph::is_connected() {
    if (num_nodes == 0) return true;

    vector<vector<int>> adj_list(num_nodes);
    for (size_t i = 0; i < adj_matrix.row_indices.size(); ++i) {
        int u = adj_matrix.row_indices[i];
        int v = adj_matrix.col_indices[i];
        adj_list[u].push_back(v);
        adj_list[v].push_back(u);
    }

    vector<bool> visited(num_nodes, false);
    queue<int> q;
    q.push(0);
    visited[0] = true;
    int count = 1;

    while (!q.empty()) {
        int u = q.front();
        q.pop();

        for (int v : adj_list[u]) {
            if (!visited[v]) {
                visited[v] = true;
                count++;
                q.push(v);
            }
        }
    }

    return count == num_nodes;
}

void Graph::print_adj_matrix() {
    vector<vector<float>> dense(num_nodes, vector<float>(num_nodes, 0));
    for (size_t i = 0; i < adj_matrix.row_indices.size(); ++i) {
        int row = adj_matrix.row_indices[i];
        int col = adj_matrix.col_indices[i];
        dense[row][col] = adj_matrix.values[i];
    }

    cout << "\nAdjacency Matrix:" << endl;
    for (int i = 0; i < num_nodes; ++i) {
        for (int j = 0; j < num_nodes; ++j) {
            cout << dense[i][j] << " ";
        }
        cout << endl;
    }
}

vector<vector<float>> dense_matmul(const vector<vector<float>>& A, const vector<vector<float>>& B) {
    int a_rows = A.size();
    int a_cols = A[0].size();
    int b_cols = B[0].size();

    vector<vector<float>> result(a_rows, vector<float>(b_cols, 0));

    for (int i = 0; i < a_rows; ++i) {
        for (int j = 0; j < b_cols; ++j) {
            for (int k = 0; k < a_cols; ++k) {
                result[i][j] += A[i][k] * B[k][j];
            }
        }
    }

    return result;
}

vector<vector<float>> relu(const vector<vector<float>>& X) {
    vector<vector<float>> result = X;
    for (auto& row : result) {
        for (auto& val : row) {
            val = max(0.0f, val);
        }
    }
    return result;
}

class GCNLayer {
private:
    int input_dim;
    int output_dim;
    vector<vector<float>> weights;

public:
    GCNLayer(int in_dim, int out_dim);
    vector<vector<float>> forward(const vector<vector<float>>& X, const SparseMatrix& adj_norm);
    void print_weights();
};

GCNLayer::GCNLayer(int in_dim, int out_dim) : input_dim(in_dim), output_dim(out_dim) {
    random_device rd;
    mt19937 gen(42);
    normal_distribution<float> dist(0.0f, sqrt(2.0f / (in_dim + out_dim)));

    weights.resize(input_dim, vector<float>(output_dim));
    for (int i = 0; i < input_dim; ++i) {
        for (int j = 0; j < output_dim; ++j) {
            weights[i][j] = dist(gen);
        }
    }
}

vector<vector<float>> GCNLayer::forward(const vector<vector<float>>& X, const SparseMatrix& adj_norm) {
    vector<vector<float>> AX(X.size(), vector<float>(X[0].size(), 0));

    for (size_t i = 0; i < adj_norm.row_indices.size(); ++i) {
        int row = adj_norm.row_indices[i];
        int col = adj_norm.col_indices[i];
        float val = adj_norm.values[i];

        for (size_t j = 0; j < X[col].size(); ++j) {
            AX[row][j] += val * X[col][j];
        }
    }

    vector<vector<float>> output = dense_matmul(AX, weights);

    return relu(output);
}

void GCNLayer::print_weights() {
    cout << "\nWeights (" << input_dim << "x" << output_dim << "):" << endl;
    for (int i = 0; i < input_dim; ++i) {
        for (int j = 0; j < output_dim; ++j) {
            cout << fixed << setprecision(4) << weights[i][j] << " ";
        }
        cout << endl;
    }
}

SparseMatrix normalize_adjacency(const SparseMatrix& adj) {
    int n = adj.rows;

    SparseMatrix adj_self_loop = adj;
    for (int i = 0; i < n; ++i) {
        adj_self_loop.row_indices.push_back(i);
        adj_self_loop.col_indices.push_back(i);
        adj_self_loop.values.push_back(1.0f);
    }

    vector<float> degrees(n, 0);
    for (size_t i = 0; i < adj_self_loop.row_indices.size(); ++i) {
        degrees[adj_self_loop.row_indices[i]] += adj_self_loop.values[i];
    }

    vector<float> sqrt_degrees(n);
    for (int i = 0; i < n; ++i) {
        sqrt_degrees[i] = (degrees[i] == 0) ? 0 : 1.0f / sqrt(degrees[i]);
    }

    SparseMatrix adj_norm(n, n);
    for (size_t i = 0; i < adj_self_loop.row_indices.size(); ++i) {
        int row = adj_self_loop.row_indices[i];
        int col = adj_self_loop.col_indices[i];
        float val = adj_self_loop.values[i];

        float normalized_val = sqrt_degrees[row] * val * sqrt_degrees[col];
        adj_norm.row_indices.push_back(row);
        adj_norm.col_indices.push_back(col);
        adj_norm.values.push_back(normalized_val);
        
    }

    return adj_norm;
}

int main() {
    // 示例图
    Graph g(4);
    g.add_edge(0, 1);
    g.add_edge(1, 2);
    g.add_edge(2, 3);
    g.add_edge(3, 0);

    cout << "\nIs graph connected? " << (g.is_connected() ? "Yes" : "No") << endl;
    g.print_adj_matrix();

    SparseMatrix adj_norm = normalize_adjacency(g.get_adj_matrix());

    // 初始化节点特征矩阵
    vector<vector<float>> X = {
        {1.0f, 0.0f},
        {0.0f, 1.0f},
        {1.0f, 1.0f},
        {0.0f, 0.0f}
    };

    // 创建GCN层
    GCNLayer layer1(2, 2);
    layer1.print_weights();

    // 前向传播
    vector<vector<float>> output = layer1.forward(X, adj_norm);

    cout << "\nOutput Features:" << endl;
    for (const auto& row : output) {
        for (float val : row) {
            cout << fixed << setprecision(4) << val << " ";
        }
        cout << endl;
    }

    return 0;
}