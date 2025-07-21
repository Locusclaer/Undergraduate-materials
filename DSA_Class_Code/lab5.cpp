#include<bits/stdc++.h>
using namespace std;

#define COLOR_RED "\033[31m"
#define COLOR_GREEN "\033[32m"
#define COLOR_YELLOW "\033[33m"
#define COLOR_BLUE "\033[34m"
#define COLOR_MAGENTA "\033[35m"
#define COLOR_CYAN "\033[36m"
#define COLOR_RESET "\033[0m"

typedef pair<int, int> pii;

// 景点 struct
struct ScenicSpot {
    int id;
    string name;
    string intro;
};

// 路径 struct
struct Edge {
    int to;
    int length;
    string intro;
    Edge(int t, int l, const string& i) : to(t), length(l), intro(i) {}
};

// 地图 class
class SchoolMap {
    private:
    vector<ScenicSpot> spots;
    vector<vector<Edge>> adjlist;
    unordered_map<string, int> nametoid;
    public:
    void AddSpot(int id, const string& name, const string& intro);
    void AddPath(int from, int to, int distance, const string& intro);
    void SearchSpotIntro(const string& name);
    void SearchShortestPath(const string& from, const string& to);
    void PrintPath(const vector<int>& pre, int end);
};

// 添加景点函数
void SchoolMap::AddSpot(int id, const string& name, const string& intro) {
    if (id >= spots.size()) {
        spots.resize(id + 1);
        adjlist.resize(id + 1);
    }
    spots[id] = {id, name, intro};
    nametoid[name] = id;
}

// 添加路径函数
void SchoolMap::AddPath(int from, int to, int distance, const string& intro) {
    adjlist[from].emplace_back(to, distance, intro);
    adjlist[to].emplace_back(from, distance, intro);
}

// 寻找景点函数
void SchoolMap::SearchSpotIntro(const string& name) {
    unordered_map<string, int>::iterator it = nametoid.find(name);
    if (it == nametoid.end()) {
        cout << COLOR_RED << "不存在 " << name << " 景点" << COLOR_RESET << endl << endl;
        return;
    }
    else {
        int id = it->second;
        cout << COLOR_GREEN << "成功找到 " << name << " 景点" << COLOR_RESET << endl;
        cout << COLOR_GREEN << "景点序号: " << spots[id].id << COLOR_RESET << endl;
        cout << COLOR_GREEN << "景点名称: " << spots[id].name << COLOR_RESET << endl;
        cout << COLOR_GREEN << "景点介绍: " << spots[id].intro << COLOR_RESET << endl << endl;
    }
}

// 景点间最短路径输出函数
void SchoolMap::PrintPath(const vector<int>& pre, int end) {
    if (pre[end] != -1) {
        PrintPath(pre, pre[end]);
        cout << " -> ";
    }
    cout << spots[end].name;
}

// 景点间最短路径搜索函数
void SchoolMap::SearchShortestPath(const string& from, const string& to) {
    unordered_map<string, int>::iterator it1 = nametoid.find(from);
    unordered_map<string, int>::iterator it2 = nametoid.find(to);
    if (it1 == nametoid.end() || it2 == nametoid.end()) {
        cout << COLOR_RED << "景点输入有误" << COLOR_RESET << endl << endl;
        return;
    }
    int start = it1->second;
    int end = it2->second;

    // Dijkstra 算法
    vector<long long> dist(spots.size() + 1, LLONG_MAX);
    vector<int> pre(spots.size(), -1);
    dist[start] = 0;
    priority_queue<pii, vector<pii>, greater<pii>> pq;
    pq.emplace(0, start);
    while (!pq.empty()) {
        int n = pq.top().second;
        long long current_dist = pq.top().first;
        pq.pop();

        if (n == end) {
            break;
        }
        if (current_dist > dist[n]) {
            continue;
        }
        for (const auto& edge : adjlist[n]) {
            int t = edge.to;
            int l = edge.length;
            if (dist[t] > dist[n] + l) {
                dist[t] = dist[n] + l;
                pre[t] = n;
                pq.emplace(dist[t], t);
            }
        }
    }

    // 输出结果
    if (dist[end] == LLONG_MAX) {
        cout << COLOR_RED << "无法从 " << from << " 到 " << to << COLOR_RESET << endl << endl;
        return;
    }

    cout << COLOR_GREEN << "从 " << from << " 到 " << to << " 的最短距离为：" << COLOR_RESET << dist[end] << endl;
    cout << COLOR_GREEN << "路径为：" << COLOR_RESET;
    PrintPath(pre, end);
    cout << endl << endl;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    SchoolMap school;

    // 景点
    school.AddSpot(1, "校门", "学校正门");
    school.AddSpot(2, "图书馆", "藏书丰富");
    school.AddSpot(3, "教学楼A", "主教学楼");
    school.AddSpot(4, "教学楼B", "理科教学楼");
    school.AddSpot(5, "实验楼", "实验室集中地");
    school.AddSpot(6, "体育馆", "运动场所");
    school.AddSpot(7, "食堂", "学生餐厅");
    school.AddSpot(8, "行政楼", "行政办公");
    school.AddSpot(9, "宿舍", "学生宿舍");
    school.AddSpot(10, "操场", "田径场");

    // 路径
    school.AddPath(1, 2, 200, "林荫道");
    school.AddPath(1, 8, 150, "行政大道");
    school.AddPath(2, 3, 100, "知识长廊");
    school.AddPath(2, 4, 120, "学术路");
    school.AddPath(3, 5, 80, "实验通道");
    school.AddPath(4, 5, 90, "科研走廊");
    school.AddPath(5, 6, 150, "运动路");
    school.AddPath(6, 7, 100, "美食街");
    school.AddPath(7, 9, 120, "生活区路");
    school.AddPath(8, 9, 180, "行政生活路");
    school.AddPath(9, 10, 200, "运动生活路");
    school.AddPath(6, 10, 50, "运动场连接路");

    cout << endl << COLOR_YELLOW << "校园导游系统" << COLOR_RESET << endl;
    cout << COLOR_BLUE << "1. 查询景点信息" << COLOR_RESET << endl;
    cout << COLOR_BLUE << "2. 查找最短路径" << COLOR_RESET << endl;
    cout << COLOR_BLUE << "3. 退出（请在下方输入你的选择）" << COLOR_RESET << endl;
    while (true) {
        int choice;
        cin >> choice;
        cin.ignore();
        if (choice == 1) {
            cout << COLOR_BLUE << "请输入要查询的景点名称: " << COLOR_RESET << endl;
            string spot;
            getline(cin, spot);
            school.SearchSpotIntro(spot);
        }
        else if (choice == 2) {
            cout << COLOR_BLUE << "请输入起点: " << COLOR_RESET << endl;
            string from, to;
            getline(cin, from);
            cout << COLOR_BLUE << "请输入终点: " << COLOR_RESET << endl;
            getline(cin, to);
            school.SearchShortestPath(from, to);
        }
        else if (choice == 3) {
            exit(0);
        }
        else {
            cout << COLOR_RED << "输入无效, 请重新输入" << COLOR_RESET << endl;
        }
    }

    return 0;
}