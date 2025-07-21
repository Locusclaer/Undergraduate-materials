#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

struct edge {
    int f, t, cost, build;
    bool operator< (const edge& b) const {
        return cost < b.cost;
    }
};

class Unionfind {
    private:
    vector<int> parent;
    public:
    Unionfind(int n) : parent(n + 1) {
        for (int i = 1; i <= n; i++) {
            parent[i] = i;
        }
    }
    int find(int x);
    void Union(int x, int y);
    bool connect(int x, int y);
};

int Unionfind::find(int x) {
    if (parent[x] != x) {
        return(parent[x] = find(parent[x]));
    }
    else {
        return x;
    }
}

void Unionfind::Union(int x, int y) {
    x = find(x);
    y = find(y);
    if (x != y) {
        parent[y] = x;
    }
}

bool Unionfind::connect(int x, int y) {
    return find(x) == find(y);
}

int kruskal(int N, vector<edge> list) {
    sort(list.begin(), list.end());
    Unionfind uf(N);
    int totalcost = 0;
    for (const auto& edge : list) {
        if (edge.build == 1 && !uf.connect(edge.f, edge.t)) {
            uf.Union(edge.f, edge.t);
        }
    }
    for (const auto& edge : list) {
        if (edge.build == 0 && !uf.connect(edge.f, edge.t)) {
            uf.Union(edge.f, edge.t);
            totalcost += edge.cost;
        }
    }
    int root = uf.find(1);
    for (int i = 2; i <= N; i++) {
        if (uf.find(i) != root) {
            return -1;
        }
    }
    return totalcost;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int N;
    while (cin >> N && N != 0) {
        int M = N * (N - 1) / 2;
        vector<edge> list(M);
        for (int i = 0; i < M; i++) {
            cin >> list[i].f >> list[i].t >> list[i].cost >> list[i].build;
            if (list[i].build == 1) {
                list[i].cost = 0;
            }
        }
        int result = kruskal(N, list);
        cout << result << endl;
    }

    return 0;
}