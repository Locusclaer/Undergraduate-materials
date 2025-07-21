#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int n, alltime;
    cin >> n;
    vector<int> length(n);
    for (int i = 0; i < n; i++) {
        cin >> length[i];
        length[i] /= 1024;
        alltime += length[i];
    }

    int maxtime = alltime >> 1;
    vector<bool> dp(maxtime + 1, false);
    dp[0] = true;
    for (int l : length) {
        for (int i = maxtime; i >= l; i--) {
            dp[i] = dp[i] || dp[i - l];
        }
    }
    for (int i = maxtime; i >= 0; i--) {
        if (dp[i]) {
            int last = alltime - i;
            cout << max(last, i) * 1024 << endl;
            break;
        }
    }

    return 0;
}