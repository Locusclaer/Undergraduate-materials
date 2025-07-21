#include <bits/stdc++.h>
using namespace std;

const int INF = 0x3f3f3f3f;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int n;
    cin >> n;
    vector<int> steps(n);
    for (int i = 0; i < n; i++) {
        cin >> steps[i];
    }

    vector<int> dp(n + 1, INF);
    dp[0] = 0;
    for (int i = 0; i < n; i++) {
        if (dp[i] == INF) continue;
        int temp = steps[i];
        for (int j = 1; j <= temp && i + j < n; j++) {
            if (dp[i + j] > dp[i] + 1) {
                dp[i + j] = dp[i] + 1;
            }
        }
    }

    cout << (dp[n - 1] == INF ? -1 : dp[n - 1]) << endl;

    return 0;
}