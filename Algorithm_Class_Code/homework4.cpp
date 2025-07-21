#include<bits/stdc++.h>
using namespace std;

const int MAXN = 20;
int nums[MAXN];
bool op[MAXN];
int current_sum = 0;
int current_count = 0;
int min_count = MAXN;
bool flag = false;
vector<int> result;
int n, k;

void dfs(int i) {
    if (i == n) {
        if (current_sum == k && current_count < min_count) {
            min_count = current_count;
            result.clear();
            for (int j = 0; j < n; j++) {
                if (op[j]) {
                    result.push_back(nums[j]);
                }
            }
            flag = true;
        }
        return;
    }
    else {
        if (current_sum > k) return;

        op[i] = true;
        current_sum += nums[i];
        current_count++;
        dfs(i + 1);
        current_sum -= nums[i];
        current_count--;

        op[i] = false;
        dfs(i + 1);
    }
}

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

    cin >> n >> k;
    for (int i = 0; i < n; i++) {
        cin >> nums[i];
    }
    dfs(0);

    if (flag) {
        for (int i = 0; i < result.size(); i++) {
            if (i > 0) cout << ' ';
            cout << result[i];
        }
        cout << endl;
    }
    else {
        cout << -1 << endl;
    }
    
    return 0;
}