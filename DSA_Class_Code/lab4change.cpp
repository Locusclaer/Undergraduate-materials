#include<bits/stdc++.h>
using namespace std;

struct nodetype {
    char data;
    int freq;
    nodetype* left;
    nodetype* right;
    nodetype(char data, int freq) : data(data), freq(freq), left(nullptr), right(nullptr) {}
    bool operator< (const nodetype& b) const {
        return freq < b.freq;
    }
};

unordered_map<char, int> countcharactor(string intext) {
    unordered_map<char, int> mp;
    for (char ch : intext) {
        mp[ch]++;
    }
    return mp;
}

nodetype* buildHuffmanTree(const unordered_map<char, int>& freqmp) {
    priority_queue<nodetype*> qu;
    for (auto& [x, y] : freqmp) {
        qu.push(new nodetype(x, y));
    }

    while (qu.size() != 1) {
        nodetype* left = qu.top();
        qu.pop();
        nodetype* right = qu.top();
        qu.pop();
        nodetype* newnode = new nodetype('\0', left->freq + right->freq);
        newnode->left = left;
        newnode->right = right;
        qu.push(newnode);
    }

    return qu.top();
}

void creatHuffmanCode(nodetype* root, unordered_map<char, string>& HuffmanCode, string code) {
    if (root == nullptr) return;
    if (root->left == nullptr && root->right == nullptr) {
        HuffmanCode[root->data] = code;
    }
    creatHuffmanCode(root->left, HuffmanCode, code + "0");
    creatHuffmanCode(root->right, HuffmanCode, code + "1");
}

string changetocode(unordered_map<char, string> HuffmanCode, string& intext) {
    string intextcode;
    for (char ch : intext) {
        intextcode += HuffmanCode[ch];
    }
    return intextcode;
}

string translate(nodetype* root, string intextcode) {
    string outtext;
    nodetype* curnode = root;
    for (char ch : intextcode) {
        if (ch == '0') {
            curnode = curnode->left;
        }
        else {
            curnode = curnode->right;
        }
        if (curnode->left == nullptr && curnode->right == nullptr) {
            outtext += curnode->data;
            curnode = root;
        }
    }
    return outtext;
}

void writetofile(const string& filename, string intext) {
    ofstream outfile(filename);
    if (outfile.is_open()) {
        outfile << intext;
        outfile.close();
        cout << endl << "已成功写入" << endl;
    }
    else {
        cerr << "文件打开失败！" << endl;
    }
}

string readfromfile(string filename) {
    ifstream infile(filename);
    string outtext;
    char ch;
    if (infile.is_open()) {
        while (infile.get(ch)) {
            outtext += ch;  // 直接读取所有字符
        }
        infile.close();
        cout << endl << "已成功读取" << endl;
    }
    else {
        cerr << "文件打开失败！" << endl;
    }
    return outtext;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string intext;
    cout << "请输入文本：" << endl;
    getline(cin, intext);
    if (intext.empty()) {
        intext = "The New Jersey guy said that the Unix solution was right because the design philosophy "
        "of Unix was simplicity and that the right thing was too complex. Besides, programmers could easily" 
        "insert this extra test and loop. The MIT guy pointed out that the implementation was simple but the "
        "interface to the functionality was complex. The New Jersey guy said that the right tradeoff has been "
        "selected in Unix namely, implementation simplicity was more important than interface simplicity.";
    }
    writetofile("a.txt", intext);

    unordered_map<char, int> freqmp = countcharactor(intext);
    int n = freqmp.size();
    cout << endl << "输入的文本中共" << n << "种字符，它们分别是：" << endl;
    for (auto& [x, y] : freqmp) {
        cout << x << ": " << y << " 次" << endl; 
    }

    nodetype* root = buildHuffmanTree(freqmp);
    unordered_map<char, string> HuffmanCode;
    creatHuffmanCode(root, HuffmanCode, "");
    cout << endl << "字符的哈夫曼编码表为：" << endl;
    for (auto& [x, y] : HuffmanCode) {
        cout << x << ": " << y << endl;
    }

    string intextcode = changetocode(HuffmanCode, intext);
    writetofile("b.txt", intextcode);

    string outtext = translate(root, intextcode);
    writetofile("c.txt", outtext);

    string bresult = readfromfile("a.txt");
    string eresult = readfromfile("c.txt");
    cout << endl << "比较结果如下：" << endl;
    cout << "输入的原始文本的长度：" << intext.size() << "字符" << endl;
    cout << "编码长度：" << intextcode.size() << "位" << endl;
    // cout << "压缩率：" << (1 - (double)intextcode.size() / (intext.size() * 8)) * 100 << '%' << endl;
    if (bresult == eresult) {
        cout << "a.txt与c.txt内容一致" << endl;
    }
    else {
        cout << "a.txt与c.txt内容不一致" << endl;
    }

    return 0;
}