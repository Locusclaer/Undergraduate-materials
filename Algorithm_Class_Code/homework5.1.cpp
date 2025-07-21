#include <bits/stdc++.h>
using namespace std;
const int INF = 0x3f3f3f3f;
const int MAXN = 21;

int N, M;
int mins = INF;
int minv[MAXN], mina[MAXN];

struct nodetype {
    int i;
    int v;
    int s;
    int rb;
    int hb;
    int lb;
    bool operator< (const nodetype& b) const {
        return lb > b.lb;
    }
};

void bfs() {
    nodetype e, e1;
    priority_queue<nodetype> qu;
    e.i = M;
    e.v = 0;
    e.s = 0;
    e.rb = sqrt(N) + 1;
    e.hb = N + 1;
    e.lb = mina[M];
    qu.push(e);

    while (!qu.empty()) {
        e = qu.top();
        qu.pop();

        if (e.i == 0) {
            if (e.v == N && e.s < mins) {
                mins = e.s;
            }
            continue;
        }

        if (e.v + minv[e.i] > N) continue;
        if (e.s + mina[e.i] >= mins) continue;
        if (e.v + (e.rb-1)*(e.rb-1)*(e.hb-1)*e.i < N) continue;

        for (int r = min(e.rb - 1, (int)sqrt(N - e.v)); r >= e.i; r--) {
            int maxh = min((N - e.v) / (r * r), e.hb - 1);
            for (int h = maxh; h >= e.i; h--) {
                int cv = r * r * h;
                int cs = e.s + 2 * r * h;
                if (e.i == M) {
                    cs += r * r;
                }
                if (e.v + cv > N) continue;
                if (cs + mina[e.i-1] >= mins) continue;
                if (e.v + cv + minv[e.i-1] > N) continue;
                if (e.v + cv + (r-1)*(r-1)*(h-1)*(e.i-1) < N) continue;

                e1.i = e.i - 1;
                e1.v = e.v + cv;
                e1.s = cs;
                e1.rb = r;
                e1.hb = h;
                e1.lb = cs + mina[e1.i];
                qu.push(e1);
            }
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> N >> M;
    minv[0] = mina[0] = 0;
    for (int i = 1; i <= M; i++) {
        minv[i] = minv[i-1] + i * i * i;
        mina[i] = mina[i-1] + 2 * i * i;
    }
    bfs();
    cout << mins << endl;
    return 0;
}