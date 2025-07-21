#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

int N, K;
int allnum = 0;

bool isprime(int n) {
    if (n <= 1) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;
    for (int i = 3; i * i <= n; i += 2) {
        if (n % i == 0) return false;
    }
    return true;
}

void dfs(int i, int cur_sum, int cur_num, const vector<int>& array) {
    if (cur_num == K && isprime(cur_sum)) {
            allnum++;
            return;
    }
    else {
        for (int j = i; j < N; j++) {
            dfs(j + 1, cur_sum + array[j], cur_num + 1, array);
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> N >> K;
    vector<int> array(N);
    for (int i = 0; i < N; i++) {
        cin >> array[i];
    }
    dfs(0, 0, 0, array);
    cout << allnum << endl;

    return 0;
}