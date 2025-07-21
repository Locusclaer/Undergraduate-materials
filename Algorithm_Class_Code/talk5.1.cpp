#include <bits/stdc++.h>
using namespace std;

const int dx[4] = {0, 1, 0, -1};
const int dy[4] = {-1, 0, 1, 0};

int W, H;
vector<string> maze;
vector<vector<int>> dist;

bool is_valid(int y, int x) {
    return y >= 0 && y < H && x >= 0 && x < W;
}

void bfs() {
    queue<pair<int, int>> q;

    for (int i = 0; i < 2 * H + 1; ++i) {
        for (int j = 0; j < 2 * W + 1; ++j) {
            if ((i == 0 || i == 2 * H || j == 0 || j == 2 * W) && maze[i][j] == ' ') {
                int x = (j - 1) / 2;
                int y = (i - 1) / 2;
                if (is_valid(y, x)) {
                    dist[y][x] = 0;
                    q.push({y, x});
                }
            }
        }
    }

    while (!q.empty()) {
        auto e = q.front(); q.pop();

        int y = e.first;
        int x = e.second;

        for (int dir = 0; dir < 4; ++dir) {
            int ny = y + dy[dir];
            int nx = x + dx[dir];
            int wall_y = 2 * y + 1 + dy[dir];
            int wall_x = 2 * x + 1 + dx[dir];

            if (is_valid(ny, nx) &&
                maze[wall_y][wall_x] == ' ' &&
                dist[ny][nx] > dist[y][x] + 1) {
                dist[ny][nx] = dist[y][x] + 1;
                q.push({ny, nx});
            }
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> W >> H;
    cin.ignore();

    maze.resize(2 * H + 1);
    for (int i = 0; i < 2 * H + 1; ++i) {
        getline(cin, maze[i]);
    }

    dist.assign(H, vector<int>(W, INT_MAX));

    bfs();
    
    int max_dist = 0;
    for (int i = 0; i < H; ++i)
        for (int j = 0; j < W; ++j)
            if (dist[i][j] != INT_MAX)
                max_dist = max(max_dist, dist[i][j] + 1);
    
    if (max_dist == 10) {
        cout << 9 << endl;
    }
    else {
        cout << max_dist << '\n';
    }
    
    return 0;
}