#include <iostream>
#include <vector>
#include <algorithm>
#include <queue>
using namespace std;

struct BNode {
    vector<int> keys;
    vector<BNode*> children;
    bool leaf;
    BNode(bool isLeaf = true) : leaf(isLeaf) {}
};

class BTree {
public:
    int m;
    int max_keys;
    int min_keys;
    BNode* root;

    BTree(int order) {
        m = order;
        max_keys = m - 1;
        min_keys = (m - 1) / 2;
        root = new BNode(true);
    }

    bool search(int key) {
        BNode* cur = root;
        while (true) {
            int i = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)i < cur->keys.size() && cur->keys[i] == key) return true;
            if (cur->leaf) return false;
            cur = cur->children[i];
        }
    }

    // 分裂节点
    void split_child(BNode* parent, int idx) {
        BNode* node = parent->children[idx];
        BNode* right = new BNode(node->leaf);
        int mid = (int)node->keys.size() / 2;
        int mid_key = node->keys[mid];

        right->keys.assign(node->keys.begin() + mid + 1, node->keys.end());
        node->keys.resize((size_t)mid);

        if (!node->leaf) {
            right->children.assign(node->children.begin() + mid + 1, node->children.end());
            node->children.resize((size_t)(mid + 1));
        }

        parent->keys.insert(parent->keys.begin() + idx, mid_key);
        parent->children.insert(parent->children.begin() + idx + 1, right);
    }

    void insert(int key) {
        BNode* cur = root;
        vector<pair<BNode*, int>> stack;
        while (!cur->leaf) {
            int i = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)i < cur->keys.size() && cur->keys[i] == key) {
                cout << "键已存在\n";
                return;
            }
            stack.emplace_back(cur, i);
            cur = cur->children[i];
        }
        int pos = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
        if ((size_t)pos < cur->keys.size() && cur->keys[pos] == key) {
            cout << "键已存在\n";
            return;
        }
        cur->keys.insert(cur->keys.begin() + pos, key);

        while ((int)cur->keys.size() > max_keys) {
            if (stack.empty()) {
                BNode* new_root = new BNode(false);
                new_root->children.push_back(cur);
                split_child(new_root, 0);
                root = new_root;
                break;
            }
            pair<BNode*, int> item = stack.back();
            stack.pop_back();
            BNode* p = item.first;
            int idx = item.second;
            split_child(p, idx);
            cur = p;
        }
    }

    // 从idx子树取最大前驱
    int get_pred(BNode* node, int idx) {
        BNode* cur = node->children[idx];
        while (!cur->leaf) cur = cur->children.back();
        return cur->keys.back();
    }

    void remove_from_leaf(BNode* node, int key) {
        auto it = lower_bound(node->keys.begin(), node->keys.end(), key);
        if (it != node->keys.end() && *it == key) node->keys.erase(it);
    }

    void merge(BNode* parent, int idx) {
        BNode* left = parent->children[idx];
        BNode* right = parent->children[idx + 1];
        int sep = parent->keys[idx];

        left->keys.push_back(sep);
        left->keys.insert(left->keys.end(), right->keys.begin(), right->keys.end());
        if (!left->leaf) {
            left->children.insert(left->children.end(), right->children.begin(), right->children.end());
        }
        delete right;
        parent->keys.erase(parent->keys.begin() + idx);
        parent->children.erase(parent->children.begin() + idx + 1);
    }

    void borrow_left(BNode* parent, int idx) {
        BNode* cur = parent->children[idx];
        BNode* sib = parent->children[idx - 1];
        int sep = parent->keys[idx - 1];

        cur->keys.insert(cur->keys.begin(), sep);
        parent->keys[idx - 1] = sib->keys.back();
        sib->keys.pop_back();
        if (!cur->leaf) {
            cur->children.insert(cur->children.begin(), sib->children.back());
            sib->children.pop_back();
        }
    }

    void borrow_right(BNode* parent, int idx) {
        BNode* cur = parent->children[idx];
        BNode* sib = parent->children[idx + 1];
        int sep = parent->keys[idx];

        cur->keys.push_back(sep);
        parent->keys[idx] = sib->keys[0];
        sib->keys.erase(sib->keys.begin());
        if (!cur->leaf) {
            cur->children.push_back(sib->children[0]);
            sib->children.erase(sib->children.begin());
        }
    }

    void fix_underflow(BNode* node, vector<pair<BNode*, int>>& stack) {
        while (node != root && (int)node->keys.size() < min_keys) {
            pair<BNode*, int> item = stack.back();
            stack.pop_back();
            BNode* parent = item.first;
            int idx = item.second;

            BNode* left_sib = (idx > 0) ? parent->children[idx - 1] : nullptr;
            BNode* right_sib = ((size_t)(idx + 1) < parent->children.size()) ? parent->children[idx + 1] : nullptr;

            bool left_ok = (left_sib != nullptr) && ((int)left_sib->keys.size() > min_keys);
            bool right_ok = (right_sib != nullptr) && ((int)right_sib->keys.size() > min_keys);

            if (left_ok) {
                borrow_left(parent, idx);
                break;
            } else if (right_ok) {
                borrow_right(parent, idx);
                break;
            } else if (left_sib) {
                merge(parent, idx - 1);
            } else {
                merge(parent, idx);
            }
            node = parent;
        }
        if (root->keys.empty() && !root->children.empty()) {
            BNode* new_root = root->children[0];
            delete root;
            root = new_root;
        }
    }

    void del(int key) {
        vector<pair<BNode*, int>> stack;
        BNode* cur = root;
        int pos;
        while (true) {
            pos = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)pos < cur->keys.size() && cur->keys[pos] == key) break;
            if (cur->leaf) { cout << "不存在\n"; return; }
            stack.emplace_back(cur, pos);
            cur = cur->children[pos];
        }
        if (cur->leaf) {
            remove_from_leaf(cur, key);
        } else {
            int pred = get_pred(cur, pos);
            cur->keys[pos] = pred;
            stack.emplace_back(cur, pos);
            cur = cur->children[pos];
            remove_from_leaf(cur, pred);
        }
        fix_underflow(cur, stack);
    }

    // 中序遍历
    void inorder(BNode* n, vector<int>& res) {
        if (!n) return;
        // 非叶子节点才递归子节点
        if (!n->leaf)
        {
            for (int i = 0; (size_t)i < n->keys.size(); i++)
            {
                inorder(n->children[i], res);
                res.push_back(n->keys[i]);
            }
            // 最后一个子节点
            inorder(n->children.back(), res);
        }
        else
        {
            // 叶子节点直接输出所有key，不访问children
            for (int k : n->keys)
                res.push_back(k);
        }
    }
    vector<int> traversal_in() {
        vector<int> r;
        inorder(root, r);
        return r;
    }

    void preorder(BNode* n, vector<int>& res) {
        if (!n) return;
        res.insert(res.end(), n->keys.begin(), n->keys.end());
        for (auto c : n->children) preorder(c, res);
    }
    vector<int> traversal_pre() {
        vector<int> r; preorder(root, r); return r;
    }

    void postorder(BNode* n, vector<int>& res) {
        if (!n) return;
        for (auto c : n->children) postorder(c, res);
        res.insert(res.end(), n->keys.begin(), n->keys.end());
    }
    vector<int> traversal_post() {
        vector<int> r; postorder(root, r); return r;
    }

    vector<int> traversal_level() {
        vector<int> r;
        queue<BNode*> q; q.push(root);
        while (!q.empty()) {
            auto u = q.front(); q.pop();
            r.insert(r.end(), u->keys.begin(), u->keys.end());
            for (auto c : u->children) q.push(c);
        }
        return r;
    }

    // 最小值
    int get_min() {
        BNode* cur = root;
        while (!cur->leaf) cur = cur->children[0];
        return cur->keys[0];
    }
    int get_max() {
        BNode* cur = root;
        while (!cur->leaf) cur = cur->children.back();
        return cur->keys.back();
    }

    // 区间查询
    void range_collect(BNode* n, int low, int high, vector<int>& res) {
        if (n->leaf) {
            for (int k : n->keys) if (k >= low && k <= high) res.push_back(k);
            return;
        }
        for (int i = 0; (size_t)i < n->keys.size(); i++) {
            range_collect(n->children[i], low, high, res);
            if (n->keys[i] >= low && n->keys[i] <= high) res.push_back(n->keys[i]);
        }
        range_collect(n->children.back(), low, high, res);
    }
    vector<int> range_query(int l, int r) {
        vector<int> res;
        range_collect(root, l, r, res);
        return res;
    }
};

int main()
{
	cout << "=============== B- 树（也称 B 树）的基本操作展示 ===============\n";
    // 1. 创建3阶B树 m=3，最大键2，非根最小键1
    BTree bt(3);
    vector<int> insert_seq = {60, 47, 69, 22, 90, 5, 64, 32, 15, 7};
    cout << "批量插入序列：";
    for (int num : insert_seq)
    {
        cout << num << " ";
        bt.insert(num);
    }
    cout << "\n\n";

    // 2. 四种遍历打印
    cout << "【前序遍历】：";
    vector<int> pre = bt.traversal_pre();
    for (int x : pre) cout << x << " ";
    cout << "\n";

    cout << "【中序遍历（有序）】：";
    vector<int> in = bt.traversal_in();
    for (int x : in) cout << x << " ";
    cout << "\n";

    cout << "【后序遍历】：";
    vector<int> post = bt.traversal_post();
    for (int x : post) cout << x << " ";
    cout << "\n";

    cout << "【层序遍历】：";
    vector<int> level = bt.traversal_level();
    for (int x : level) cout << x << " ";
    cout << "\n\n";

    // 3. 最值查询
    cout << "树最小值：" << bt.get_min() << "\n";
    cout << "树最大值：" << bt.get_max() << "\n\n";

    // 4. 查找测试
    int find1 = 32, find2 = 99;
    bool res1 = bt.search(find1);
    bool res2 = bt.search(find2);
    cout << "查找 " << find1 << "：" << (res1 ? "存在" : "不存在") << "\n";
    cout << "查找 " << find2 << "：" << (res2 ? "存在" : "不存在") << "\n\n";

    // 5. 区间查询 [10, 70]
    cout << "区间查询 [10,70]：";
    vector<int> range = bt.range_query(10, 70);
    for (int x : range) cout << x << " ";
    cout << "\n\n";

    // 6. 删除测试
    int del_key = 47;
    cout << "删除键 " << del_key << "\n";
    bt.del(del_key);
    cout << "删除后中序：";
    vector<int> after_del = bt.traversal_in();
    for (int x : after_del) cout << x << " ";
    cout << "\n\n";

    // 7. 重复插入测试
    cout << "重复插入60：";
    bt.insert(60);
    cout << "\n";

    return 0;
}
