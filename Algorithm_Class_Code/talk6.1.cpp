#include<bits/stdc++.h>
using namespace std;

int N, m;

void solve() {
    cin >> N >> m;
    vector<int> v(N), w(m);
    for (int i = 0; i < m; i++) {
        cin >> v[i] >> w[i];
    }
    vector<int> dp(N + 1, 0);

    for (int i = 0; i < m; i++) {
        for (int j = N; j >= v[i]; j--) {
            dp[j] = max(dp[j], dp[j - v[i]] + v[i] * w[i]);
        }
    }
    cout << dp[N] << endl;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    solve();

    return 0;
}