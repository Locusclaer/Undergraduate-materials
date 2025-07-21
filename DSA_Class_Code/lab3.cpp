#include <iostream>
#include <string>
using namespace std;

struct node {
    char value;
    node* left;
    node* right;
    node() : value(0), left(nullptr), right(nullptr) {}
    node(char data) : value(data), left(nullptr), right(nullptr) {}
};

node* creat_tree(string preorder, int& index) {
    if (index >= preorder.size() || preorder[index] == '#') {
        index++;
        return nullptr;
    }

    node* root = new node(preorder[index++]);
    root->left = creat_tree(preorder, index);
    root->right = creat_tree(preorder, index);

    return root;
}

void pretraverse(node* tree) {
    if (tree == nullptr) return;
    cout << tree->value << ' ';
    pretraverse(tree->left);
    pretraverse(tree->right);
}

void intraverse(node* tree) {
    if (tree == nullptr) return;
    intraverse(tree->left);
    cout << tree->value << ' ';
    intraverse(tree->right);
}

void posttraverse(node* tree) {
    if (tree == nullptr) return;
    posttraverse(tree->left);
    posttraverse(tree->right);
    cout << tree->value << ' ';
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string preorder;
    // cin >> preorder;
    preorder = "ABD##E##CF##G##";
    int index = 0;
    node* tree = creat_tree(preorder, index);

    cout << "先序遍历：";
    pretraverse(tree);
    cout << endl;

    cout << "中序遍历：";
    intraverse(tree);
    cout << endl;

    cout << "后序遍历：";
    posttraverse(tree);
    cout << endl;

    return 0;
}