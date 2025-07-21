#include <bits/stdc++.h>
using namespace std;

long long closestElement(long long a[], int n, long long target) {
    auto it = lower_bound(a, a + n, target);
    if (it != a + n && *it == target) {
        return target;
    }
    if (it == a) {
        return a[0];
    }
    if (it == a + n) {
        return a[n - 1];
    }
    long long next = *it;
    long long pre = *(it - 1);
    return (abs(next - target) < abs(pre - target)) ? next : pre;
}

void solution(long long a[], long long b[], int n, int m) {
    sort(a, a + n);
    for (int i = 0; i < m; i++) {
        b[i] = closestElement(a, n, b[i]);
    }
}

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

    int n, m;
    cin >> n;
    long long* a = new long long[n];
    for (int i = 0; i < n; i++) {
        cin >> a[i];
    }

    cin >> m;
    long long* b = new long long[m];
    for (int i = 0; i < m; i++) {
        cin >> b[i];
    }

    solution(a, b, n, m);

    for (int i = 0; i < m; i++) {
        cout << b[i] << endl;
    }

    delete[] b;
    delete[] a;

    return 0;
}