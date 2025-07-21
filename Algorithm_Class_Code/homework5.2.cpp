#include <bits/stdc++.h>
using namespace std;
const int MAX = 200000;
const int INF = 0x3f3f3f3f;

int N, K;
vector<int> dist(MAX + 1, INF);
queue<int> q;

void bfs() {
    dist[N] = 0;
    q.push(N);

    while (!q.empty()) {
        int pos = q.front();
        q.pop();

        if (pos == K) {
            cout << dist[pos] << endl;
            return;
        }

        if (pos + 1 <= MAX && dist[pos + 1] > dist[pos] + 1) {
            dist[pos + 1] = dist[pos] + 1;
            q.push(pos + 1);
        }
        if (pos - 1 >= 0 && dist[pos - 1] > dist[pos] + 1) {
            dist[pos - 1] = dist[pos] + 1;
            q.push(pos - 1);
        }
        if (pos * 2 <= MAX && dist[pos * 2] > dist[pos] + 1) {
            dist[pos * 2] = dist[pos] + 1;
            q.push(pos * 2);
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> N >> K;
    bfs();
    
    return 0;
}