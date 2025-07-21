#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

void solve(const string& digits, int cur_flag, string cur_expression, int cur_sum, int last_num, vector<string>& solutions) {
    if (cur_flag == digits.size()) {
        if (cur_sum == 100) {
            solutions.push_back(cur_expression);
        }
        return;
    }

    char next_num = digits[cur_flag];
    int next = next_num - '0';

    solve(digits, cur_flag + 1, cur_expression + '+' + next_num, cur_sum + next, next, solutions);

    solve(digits, cur_flag + 1, cur_expression + '-' + next_num, cur_sum - next, -next, solutions);

    int connection = (last_num > 0) ? last_num * 10 + next : last_num * 10 - next;
    solve(digits, cur_flag + 1, cur_expression + next_num, cur_sum - last_num + connection, connection, solutions);
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string digits = "123456789";
    vector<string> solutions;
    solve(digits, 1, digits.substr(0, 1), digits[0] - '0', digits[0] - '0', solutions);

    for (auto& s : solutions) {
        cout << s << "=100" << endl;
    }

    return 0;
}