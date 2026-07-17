#include <iostream>
#include <vector>
#include <algorithm>
#include <queue>
using namespace std;

struct BPlusNode {
    vector<int> keys;
    vector<BPlusNode*> children;
    bool leaf;
    BPlusNode *prev, *next;
    BPlusNode(bool isLeaf = true) : leaf(isLeaf), prev(nullptr), next(nullptr) {}
};

class BPlusTree {
public:
    int m;
    int max_keys;
    int min_keys;
    BPlusNode* root;
    BPlusNode* first_leaf;

    BPlusTree(int order) {
        m = order;
        max_keys = m - 1;
        min_keys = (m - 1) / 2;
        root = new BPlusNode(true);
        first_leaf = root;
    }

    BPlusNode* get_leftmost(BPlusNode* n) {
        while (!n->leaf) n = n->children[0];
        return n;
    }

    void link_leaf(BPlusNode* left, BPlusNode* right) {
        right->prev = left;
        right->next = left->next;
        if (left->next) left->next->prev = right;
        left->next = right;
    }

    void unlink_leaf(BPlusNode* node) {
        if (node->prev) node->prev->next = node->next;
        if (node->next) node->next->prev = node->prev;
        if (node == first_leaf) first_leaf = node->next;
        node->prev = node->next = nullptr;
    }

    bool search(int key) {
        BPlusNode* cur = root;
        while (!cur->leaf) {
            int i = 0;
            while ((size_t)i < cur->keys.size() && key >= cur->keys[i]) {
                i++;
            }
            cur = cur->children[i];
        }
        auto it = lower_bound(cur->keys.begin(), cur->keys.end(), key);
        return (it != cur->keys.end() && *it == key);
    }

    void split_child(BPlusNode* parent, int idx) {
        BPlusNode* node = parent->children[idx];
        BPlusNode* right = new BPlusNode(node->leaf);
        int mid;
        int up_key;
        if (node->leaf) {
            mid = (node->keys.size() + 1) / 2;
            right->keys.assign(node->keys.begin() + mid, node->keys.end());
            node->keys.resize(mid);
            up_key = right->keys[0];
            link_leaf(node, right);
        } else {
            mid = node->keys.size() / 2;
            up_key = node->keys[mid];
            right->keys.assign(node->keys.begin() + mid + 1, node->keys.end());
            node->keys.resize(mid);
            right->children.assign(node->children.begin() + mid + 1, node->children.end());
            node->children.resize(mid + 1);
        }
        parent->keys.insert(parent->keys.begin() + idx, up_key);
        parent->children.insert(parent->children.begin() + idx + 1, right);
    }

    void insert(int key) {
        BPlusNode* cur = root;
        vector<pair<BPlusNode*, int>> stack;
        // 修复：向下寻叶匹配规则
        while (!cur->leaf) {
            int i = 0;
            while ((size_t)i < cur->keys.size() && key >= cur->keys[i]) {
                i++;
            }
            stack.emplace_back(cur, i);
            cur = cur->children[i];
        }
        auto it = lower_bound(cur->keys.begin(), cur->keys.end(), key);
        if (it != cur->keys.end() && *it == key) {
            cout << "重复键\n";
            return;
        }
        cur->keys.insert(it, key);

        while ((int)cur->keys.size() > max_keys) {
            if (stack.empty()) {
                BPlusNode* new_root = new BPlusNode(false);
                new_root->children.push_back(cur);
                split_child(new_root, 0);
                root = new_root;
                first_leaf = get_leftmost(root);
                break;
            }
            pair<BPlusNode*, int> item = stack.back();
            stack.pop_back();
            BPlusNode* p = item.first;
            int idx = item.second;
            split_child(p, idx);
            cur = p;
        }
        first_leaf = get_leftmost(root);
    }

    void borrow_left_leaf(BPlusNode* parent, int idx) {
        BPlusNode* cur = parent->children[idx];
        BPlusNode* sib = parent->children[idx - 1];
        int val = sib->keys.back();
        sib->keys.pop_back();
        cur->keys.insert(cur->keys.begin(), val);
        parent->keys[idx - 1] = cur->keys[0];
    }
    void borrow_right_leaf(BPlusNode* parent, int idx) {
        BPlusNode* cur = parent->children[idx];
        BPlusNode* sib = parent->children[idx + 1];
        int val = sib->keys[0];
        sib->keys.erase(sib->keys.begin());
        cur->keys.push_back(val);
        parent->keys[idx] = sib->keys[0];
    }
    void merge_leaf(BPlusNode* parent, int idx, bool left_side) {
        BPlusNode* cur = parent->children[idx];
        if (left_side) {
            BPlusNode* sib = parent->children[idx - 1];
            sib->keys.insert(sib->keys.end(), cur->keys.begin(), cur->keys.end());
            unlink_leaf(cur);
            parent->keys.erase(parent->keys.begin() + idx - 1);
            parent->children.erase(parent->children.begin() + idx);
        } else {
            BPlusNode* sib = parent->children[idx + 1];
            cur->keys.insert(cur->keys.end(), sib->keys.begin(), sib->keys.end());
            unlink_leaf(sib);
            parent->keys.erase(parent->keys.begin() + idx);
            parent->children.erase(parent->children.begin() + idx + 1);
        }
    }

    void borrow_left_idx(BPlusNode* parent, int idx) {
        BPlusNode* cur = parent->children[idx];
        BPlusNode* sib = parent->children[idx - 1];
        int sep = parent->keys[idx - 1];
        cur->keys.insert(cur->keys.begin(), sep);
        parent->keys[idx - 1] = sib->keys.back();
        sib->keys.pop_back();
        if (!cur->leaf) {
            cur->children.insert(cur->children.begin(), sib->children.back());
            sib->children.pop_back();
        }
    }
    void borrow_right_idx(BPlusNode* parent, int idx) {
        BPlusNode* cur = parent->children[idx];
        BPlusNode* sib = parent->children[idx + 1];
        int sep = parent->keys[idx];
        cur->keys.push_back(sep);
        parent->keys[idx] = sib->keys[0];
        sib->keys.erase(sib->keys.begin());
        if (!cur->leaf) {
            cur->children.push_back(sib->children[0]);
            sib->children.erase(sib->children.begin());
        }
    }
    void merge_idx(BPlusNode* parent, int idx, bool left_side) {
        BPlusNode* cur = parent->children[idx];
        if (left_side) {
            BPlusNode* sib = parent->children[idx - 1];
            sib->keys.push_back(parent->keys[idx - 1]);
            sib->keys.insert(sib->keys.end(), cur->keys.begin(), cur->keys.end());
            sib->children.insert(sib->children.end(), cur->children.begin(), cur->children.end());
            parent->keys.erase(parent->keys.begin() + idx - 1);
            parent->children.erase(parent->children.begin() + idx);
        } else {
            BPlusNode* sib = parent->children[idx + 1];
            cur->keys.push_back(parent->keys[idx]);
            cur->keys.insert(cur->keys.end(), sib->keys.begin(), sib->keys.end());
            cur->children.insert(cur->children.end(), sib->children.begin(), sib->children.end());
            parent->keys.erase(parent->keys.begin() + idx);
            parent->children.erase(parent->children.begin() + idx + 1);
        }
    }

    void fix_underflow(BPlusNode* node, vector<pair<BPlusNode*, int>>& stack) {
        while (node != root && (int)node->keys.size() < min_keys) {
            pair<BPlusNode*, int> item = stack.back();
            stack.pop_back();
            BPlusNode* p = item.first;
            int idx = item.second;

            BPlusNode* left_sib = (idx > 0) ? p->children[idx - 1] : nullptr;
            BPlusNode* right_sib = ((size_t)(idx + 1) < p->children.size()) ? p->children[idx + 1] : nullptr;
            if (node->leaf) {
                if (left_sib && left_sib->leaf && (int)left_sib->keys.size() > min_keys) {
                    borrow_left_leaf(p, idx);
                    break;
                } else if (right_sib && right_sib->leaf && (int)right_sib->keys.size() > min_keys) {
                    borrow_right_leaf(p, idx);
                    break;
                } else if (left_sib && left_sib->leaf) {
                    merge_leaf(p, idx, true);
                } else if (right_sib && right_sib->leaf) {
                    merge_leaf(p, idx, false);
                }
            } else {
                if (left_sib && (int)left_sib->keys.size() > min_keys) {
                    borrow_left_idx(p, idx);
                    break;
                } else if (right_sib && (int)right_sib->keys.size() > min_keys) {
                    borrow_right_idx(p, idx);
                    break;
                } else if (left_sib) {
                    merge_idx(p, idx, true);
                } else {
                    merge_idx(p, idx, false);
                }
            }
            node = p;
        }
        if (root->keys.empty() && !root->children.empty()) {
            root = root->children[0];
            root->prev = root->next = nullptr;
            first_leaf = get_leftmost(root);
        }
    }

    void del(int key) {
        vector<pair<BPlusNode*, int>> stack;
        BPlusNode* cur = root;
        while (!cur->leaf) {
            int i = 0;
            while ((size_t)i < cur->keys.size() && key >= cur->keys[i]) {
                i++;
            }
            stack.emplace_back(cur, i);
            cur = cur->children[i];
        }
        auto it = lower_bound(cur->keys.begin(), cur->keys.end(), key);
        if (it == cur->keys.end() || *it != key) {
            cout << "不存在\n";
            return;
        }
        cur->keys.erase(it);
        fix_underflow(cur, stack);
        first_leaf = get_leftmost(root);
    }

    vector<int> traversal_in_business() {
        vector<int> res;
        BPlusNode* p = first_leaf;
        while (p) {
            res.insert(res.end(), p->keys.begin(), p->keys.end());
            p = p->next;
        }
        return res;
    }

    void inorder_dfs(BPlusNode* n, vector<int>& res) {
        if (!n) return;
        if (n->leaf) {
            res.insert(res.end(), n->keys.begin(), n->keys.end());
            return;
        }
        for (int i = 0; (size_t)i < n->keys.size(); i++) {
            inorder_dfs(n->children[i], res);
            res.push_back(n->keys[i]);
        }
        inorder_dfs(n->children.back(), res);
    }
    vector<int> traversal_in_teaching() {
        vector<int> r;
        inorder_dfs(root, r);
        return r;
    }

    void preorder(BPlusNode* n, vector<int>& res) {
        if (!n) return;
        res.insert(res.end(), n->keys.begin(), n->keys.end());
        for (auto c : n->children) preorder(c, res);
    }
    vector<int> traversal_pre() {
        vector<int> r;
        preorder(root, r);
        return r;
    }

    void postorder(BPlusNode* n, vector<int>& res) {
        if (!n) return;
        for (auto c : n->children) postorder(c, res);
        res.insert(res.end(), n->keys.begin(), n->keys.end());
    }
    vector<int> traversal_post() {
        vector<int> r;
        postorder(root, r);
        return r;
    }

    vector<int> traversal_level() {
        vector<int> r;
        queue<BPlusNode*> q;
        q.push(root);
        while (!q.empty()) {
            auto u = q.front();
            q.pop();
            r.insert(r.end(), u->keys.begin(), u->keys.end());
            for (auto c : u->children) q.push(c);
        }
        return r;
    }

    int get_min() {
        return first_leaf->keys[0];
    }
    int get_max() {
        BPlusNode* p = first_leaf;
        while (p->next) p = p->next;
        return p->keys.back();
    }

    vector<int> range_query(int low, int high) {
        vector<int> res;
        BPlusNode* cur = root;
        while (!cur->leaf) {
            int i = 0;
            while ((size_t)i < cur->keys.size() && low >= cur->keys[i]) {
                i++;
            }
            cur = cur->children[i];
        }
        while (cur) {
            for (int k : cur->keys) {
                if (k > high) return res;
                if (k >= low) res.push_back(k);
            }
            cur = cur->next;
        }
        return res;
    }
};

int main()
{
	cout << "=============== B+ 树的基本操作展示 ===============\n";
    BPlusTree bpt(3);
    vector<int> insert_seq = {60, 47, 69, 22, 90, 5, 64, 32, 15, 7};
    cout << "批量插入序列：";
    for (int num : insert_seq)
    {
        cout << num << " ";
        bpt.insert(num);
    }
    cout << "\n\n";

    cout << "【业务中序（仅叶子有序数据）】：";
    vector<int> bus_in = bpt.traversal_in_business();
    for (int x : bus_in) cout << x << " ";
    cout << "\n";

    cout << "【教学DFS中序（含索引键）】：";
    vector<int> tea_in = bpt.traversal_in_teaching();
    for (int x : tea_in) cout << x << " ";
    cout << "\n\n";

    cout << "【前序遍历】：";
    vector<int> pre = bpt.traversal_pre();
    for (int x : pre) cout << x << " ";
    cout << "\n";

    cout << "【后序遍历】：";
    vector<int> post = bpt.traversal_post();
    for (int x : post) cout << x << " ";
    cout << "\n";

    cout << "【层序遍历】：";
    vector<int> level = bpt.traversal_level();
    for (int x : level) cout << x << " ";
    cout << "\n\n";

    cout << "最小值：" << bpt.get_min() << "\n";
    cout << "最大值：" << bpt.get_max() << "\n\n";

    int f1 = 32, f2 = 99;
    bool s1 = bpt.search(f1);
    bool s2 = bpt.search(f2);
    cout << "查找" << f1 << "：" << (s1 ? "存在" : "不存在") << "\n";
    cout << "查找" << f2 << "：" << (s2 ? "存在" : "不存在") << "\n\n";

    cout << "区间查询 [10,70]：";
    vector<int> range = bpt.range_query(10, 70);
    for (int x : range) cout << x << " ";
    cout << "\n\n";

    int del_key = 47;
    cout << "删除键 " << del_key << "\n";
    bpt.del(del_key);
    cout << "删除后业务有序序列：";
    vector<int> after_del = bpt.traversal_in_business();
    for (int x : after_del) cout << x << " ";
    cout << "\n\n";

    cout << "重复插入60：";
    bpt.insert(60);

    return 0;
}
