#include <stdio.h>
#include <vector>
using namespace std;
struct NodeType {
    int p;
    int pc;
    NodeType(int x, int y) : p(x), pc(y) {}
};
void solve(int n,vector<NodeType> &v) {
    if (n <= 1) return;
    if (n % 2 == 0) {
        int count = 0;
        while (n % 2 == 0) {
            count++;
            n /= 2;
        }
        v.emplace_back(2, count);
    }
    for (int i = 3; i * i <= n; i += 2) {
        if (n % i == 0) {
            int count = 0;
            while (n % i == 0) {
                count++;
                n /= i;
            }
            v.emplace_back(i, count);
        }
    }
    if (n > 1) {
        v.emplace_back(n, 1);
    }
}
void disp(vector<NodeType> &v) {
    vector<NodeType>::iterator it=v.begin();
    printf("%d %d",it->p,it->pc);
    for (it++;it!=v.end();++it)
        printf(" %d %d",it->p,it->pc);
    printf("\n");
}
int main() {
    int n;
    while (scanf("%d", &n) != EOF) {
        vector<NodeType> v;
        solve(n,v);
        disp(v);    
    }
    return 0;
}