#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

string max_result;

int my_pow(int num, int exp) {
    int result = 1;
    while (exp--) {
        result *= num;
    }
    return result;
}

void solve(string& str, int N, int i, vector<char> &path) {
    if (path.size() == 5) {
        vector<char> sorted = path;
        sort(sorted.begin(), sorted.end());
        do {
            int V = sorted[0] - 'A' + 1;
            int W = sorted[1] - 'A' + 1;
            int X = sorted[2] - 'A' + 1;
            int Y = sorted[3] - 'A' + 1;
            int Z = sorted[4] - 'A' + 1;
            int sum = V - my_pow(W, 2) + my_pow(X, 3) - my_pow(Y, 4) + my_pow(Z, 5);
            if (sum == N) {
                auto temp = string(sorted.begin(), sorted.end());
                if (temp > max_result)
                    max_result = std::move(temp);
            }
        } while (next_permutation(sorted.begin(), sorted.end()));
        return;
    }
    for (int j = i; j < str.size(); j++) {
        path.push_back(str[j]);
        solve(str, N, j + 1, path);
        path.pop_back();
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int N;
    string str;

    while (cin >> N && N != 0) {
        cin >> str;
        max_result = "";
        vector<char> path;
        solve(str, N, 0, path);
        if (!max_result.empty()) {
            cout << max_result << endl;
        } else {
            cout << "no solution" << endl;
        }
    }

    return 0;
}