#include <bits/stdc++.h>
using namespace std;

void solve() {
    int n, m, s, t;
    cin >> n >> m >> s >> t;

    vector<vector<pair<int, int>>> adj(n + 1);
    for (int i = 0; i < m; i++) {
        int u, v, w;
        cin >> u >> v >> w;
        adj[u].emplace_back(v, w);
        adj[v].emplace_back(u, w);
    }

    vector<long long> dist(n + 1, LLONG_MAX);
    dist[s] = 0;
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;
    pq.emplace(0, s);

    while (!pq.empty()) {
        int u = pq.top().second;
        long long current_dist = pq.top().first;
        pq.pop();

        if (u == t) {
            break;
        }
        if (current_dist > dist[u]) {
            continue;
        }
        for (const auto& edge : adj[u]) {
            int v = edge.first;
            int w = edge.second;
            if (dist[v] > dist[u] + w) {
                dist[v] = dist[u] + w;
                pq.emplace(dist[v], v);
            }
        }
    }

    cout << dist[t] << endl;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    solve();
    return 0;
}