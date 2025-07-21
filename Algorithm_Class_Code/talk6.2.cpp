#include <bits/stdc++.h>
using namespace std;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int n, m;
    while ((cin >> n >> m)) {
        vector<int> a(n);
        for (int i = 0; i < n; i++) {
            cin >> a[i];
        }
        if (m >= n) {
            cout << n << endl;
            continue;
        }

        sort(a.begin(), a.end());

        vector<int> gaps;
        gaps.reserve(n - 1);
        for (int i = 1; i < n; i++) {
            gaps.push_back(a[i] - a[i-1] - 1);
        }

        sort(gaps.begin(), gaps.end(), greater<int>());

        long long extra = 0;
        for (int i = m-1; i < (int)gaps.size(); i++) {
            extra += gaps[i];
        }

        cout << (n + extra) << endl;
    }

    return 0;
}