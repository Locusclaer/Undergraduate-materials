#include<bits/stdc++.h>
using namespace std;

void backtrack(vector<int>& nums, int start, string& current, vector<string>& result) {
    if (!current.empty()) {
        result.push_back(current);
    }

    for (int i = start; i < nums.size(); ++i) {
        current.push_back(nums[i] + '0');
        backtrack(nums, i + 1, current, result);
        current.pop_back();
    }
}

int main() {
    int n;
    cin >> n;

    vector<int> nums;
    for (int i = 1; i <= n; ++i) {
        nums.push_back(i);
    }
    vector<string> subsets;
    string current;
    backtrack(nums, 0, current, subsets);

    subsets.push_back("0");
    sort(subsets.begin(), subsets.end(), [](const string& a, const string& b) {
        return stoi(a) < stoi(b);
    });

    for (const string& s : subsets) {
        cout << s << endl;
    }

    return 0;
}
