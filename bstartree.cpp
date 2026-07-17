#include <iostream>
#include <vector>
#include <algorithm>
#include <queue>
#include <cmath>
using namespace std;

struct SplitTwoRes {
    vector<int> left;
    int sep;
    vector<int> right;
    SplitTwoRes(vector<int> l, int s, vector<int> r) : left(l), sep(s), right(r) {}
};

struct SplitThreeRes {
    vector<int> left;
    int k1;
    vector<int> mid;
    int k2;
    vector<int> right;
    SplitThreeRes(vector<int> l, int k_1, vector<int> m, int k_2, vector<int> r)
        : left(l), k1(k_1), mid(m), k2(k_2), right(r) {}
};

struct BStarNode {
    vector<int> keys;
    vector<BStarNode*> children;
    bool leaf;
    BStarNode(bool isLeaf = true) : leaf(isLeaf) {}
};

class BStarTree {
public:
    int m;
    int max_keys;
    int min_child;
    int min_keys;
    BStarNode* root;

    BStarTree(int order) {
        m = order;
        max_keys = m - 1;
        min_child = static_cast<int>(ceil(2.0 * m / 3));
        min_keys = max(1, min_child - 1);
        root = new BStarNode(true);
    }

    SplitTwoRes split_two_even(const vector<int>& all) {
        int total = all.size();
        int mid = total / 2;
        vector<int> left(all.begin(), all.begin() + mid);
        int sep = all[mid];
        vector<int> right(all.begin() + mid + 1, all.end());
        return SplitTwoRes(left, sep, right);
    }

    bool try_split_three(const vector<int>& all, SplitThreeRes& out) {
        int min_seg = min_keys;
        int min_total = min_seg * 3 + 2;
        if ((int)all.size() < min_total)
            return false;
        int total = (int)all.size();
        int pos1 = max(min_seg, total / 3);
        int pos2 = min(total - min_seg - 1, 2 * total / 3);
        if (pos2 - pos1 - 1 < min_seg)
            return false;

        vector<int> l(all.begin(), all.begin() + pos1);
        int k1 = all[pos1];
        vector<int> mid(all.begin() + pos1 + 1, all.begin() + pos2);
        int k2 = all[pos2];
        vector<int> r(all.begin() + pos2 + 1, all.end());
        out = SplitThreeRes(l, k1, mid, k2, r);
        return true;
    }

    bool search(int key) {
        BStarNode* cur = root;
        while (true) {
            int i = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)i < cur->keys.size() && cur->keys[i] == key)
                return true;
            if (cur->leaf)
                return false;
            cur = cur->children[i];
        }
    }

    void insert(int key) {
        vector<pair<BStarNode*, int>> stack;
        BStarNode* cur = root;
        while (!cur->leaf) {
            int i = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)i < cur->keys.size() && cur->keys[i] == key) {
                cout << "重复键\n";
                return;
            }
            stack.emplace_back(cur, i);
            cur = cur->children[i];
        }
        int pos = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
        if ((size_t)pos < cur->keys.size() && cur->keys[pos] == key) {
            cout << "重复键\n";
            return;
        }
        cur->keys.insert(cur->keys.begin() + pos, key);

        while ((int)cur->keys.size() > max_keys) {
            if (cur == root) {
                int mid = (int)cur->keys.size() / 2;
                int midk = cur->keys[mid];
                BStarNode* l = new BStarNode(cur->leaf);
                BStarNode* r = new BStarNode(cur->leaf);
                l->keys.assign(cur->keys.begin(), cur->keys.begin() + mid);
                r->keys.assign(cur->keys.begin() + mid + 1, cur->keys.end());
                if (!cur->leaf) {
                    l->children.assign(cur->children.begin(), cur->children.begin() + mid + 1);
                    r->children.assign(cur->children.begin() + mid + 1, cur->children.end());
                }
                BStarNode* new_root = new BStarNode(false);
                new_root->keys.push_back(midk);
                new_root->children = {l, r};
                root = new_root;
                break;
            }
            pair<BStarNode*, int> item = stack.back();
            stack.pop_back();
            BStarNode* p = item.first;
            int idx = item.second;

            BStarNode* left_sib = (idx > 0) ? p->children[idx - 1] : nullptr;
            BStarNode* right_sib = ((size_t)(idx + 1) < p->children.size()) ? p->children[idx + 1] : nullptr;

            if (left_sib && (int)left_sib->keys.size() < max_keys) {
                int sep = p->keys[idx - 1];
                int move = cur->keys[0];
                cur->keys.erase(cur->keys.begin());
                left_sib->keys.push_back(sep);
                p->keys[idx - 1] = move;
                if (!cur->leaf) {
                    BStarNode* c = cur->children[0];
                    cur->children.erase(cur->children.begin());
                    left_sib->children.push_back(c);
                }
                cur = p;
                continue;
            }
            if (right_sib && (int)right_sib->keys.size() < max_keys) {
                int sep = p->keys[idx];
                int move = cur->keys.back();
                cur->keys.pop_back();
                right_sib->keys.insert(right_sib->keys.begin(), sep);
                p->keys[idx] = move;
                if (!cur->leaf) {
                    BStarNode* c = cur->children.back();
                    cur->children.pop_back();
                    right_sib->children.insert(right_sib->children.begin(), c);
                }
                cur = p;
                continue;
            }

            SplitThreeRes split3({}, 0, {}, 0, {});
            bool can_split3 = false;
            if (left_sib) {
                vector<int> allk = left_sib->keys;
                allk.push_back(p->keys[idx - 1]);
                allk.insert(allk.end(), cur->keys.begin(), cur->keys.end());
                can_split3 = try_split_three(allk, split3);
                if (can_split3) {
                    left_sib->keys = split3.left;
                    BStarNode* mid_node = new BStarNode(cur->leaf);
                    mid_node->keys = split3.mid;
                    cur->keys = split3.right;
                    if (!cur->leaf) {
                        vector<BStarNode*> allc = left_sib->children;
                        allc.insert(allc.end(), cur->children.begin(), cur->children.end());
                        int s1 = (int)split3.left.size() + 1;
                        int s2 = s1 + (int)split3.mid.size() + 1;
                        left_sib->children.assign(allc.begin(), allc.begin() + s1);
                        mid_node->children.assign(allc.begin() + s1, allc.begin() + s2);
                        cur->children.assign(allc.begin() + s2, allc.end());
                    }
                    p->keys.erase(p->keys.begin() + idx - 1);
                    p->keys.insert(p->keys.begin() + idx - 1, split3.k2);
                    p->keys.insert(p->keys.begin() + idx - 1, split3.k1);
                    p->children.insert(p->children.begin() + idx, mid_node);
                    cur = p;
                    continue;
                }
            }
            if (right_sib && !can_split3) {
                vector<int> allk = cur->keys;
                allk.push_back(p->keys[idx]);
                allk.insert(allk.end(), right_sib->keys.begin(), right_sib->keys.end());
                can_split3 = try_split_three(allk, split3);
                if (can_split3) {
                    cur->keys = split3.left;
                    BStarNode* mid_node = new BStarNode(cur->leaf);
                    mid_node->keys = split3.mid;
                    right_sib->keys = split3.right;
                    if (!cur->leaf) {
                        vector<BStarNode*> allc = cur->children;
                        allc.insert(allc.end(), right_sib->children.begin(), right_sib->children.end());
                        int s1 = (int)split3.left.size() + 1;
                        int s2 = s1 + (int)split3.mid.size() + 1;
                        cur->children.assign(allc.begin(), allc.begin() + s1);
                        mid_node->children.assign(allc.begin() + s1, allc.begin() + s2);
                        right_sib->children.assign(allc.begin() + s2, allc.end());
                    }
                    p->keys.erase(p->keys.begin() + idx);
                    p->keys.insert(p->keys.begin() + idx, split3.k2);
                    p->keys.insert(p->keys.begin() + idx, split3.k1);
                    p->children.insert(p->children.begin() + idx + 1, mid_node);
                    cur = p;
                    continue;
                }
            }
            int mid = (int)cur->keys.size() / 2;
            int midk = cur->keys[mid];
            BStarNode* rnode = new BStarNode(cur->leaf);
            rnode->keys.assign(cur->keys.begin() + mid + 1, cur->keys.end());
            cur->keys.resize((size_t)mid);
            if (!cur->leaf) {
                rnode->children.assign(cur->children.begin() + mid + 1, cur->children.end());
                cur->children.resize((size_t)(mid + 1));
            }
            p->keys.insert(p->keys.begin() + idx, midk);
            p->children.insert(p->children.begin() + idx + 1, rnode);
            cur = p;
        }
    }

    void del(int key) {
        vector<pair<BStarNode*, int>> stack;
        BStarNode* cur = root;
        int pos;
        while (true) {
            pos = lower_bound(cur->keys.begin(), cur->keys.end(), key) - cur->keys.begin();
            if ((size_t)pos < cur->keys.size() && cur->keys[pos] == key)
                break;
            if (cur->leaf) {
                cout << "不存在\n";
                return;
            }
            stack.emplace_back(cur, pos);
            cur = cur->children[pos];
        }
        int del_key;
        if (!cur->leaf) {
            BStarNode* pred = cur->children[pos];
            stack.emplace_back(cur, pos);
            while (!pred->leaf) {
                stack.emplace_back(pred, (int)pred->keys.size());
                pred = pred->children.back();
            }
            del_key = pred->keys.back();
            cur->keys[pos] = del_key;
            cur = pred;
        } else {
            del_key = key;
        }
        auto it = lower_bound(cur->keys.begin(), cur->keys.end(), del_key);
        cur->keys.erase(it);

        while (cur != root && (int)cur->keys.size() < min_keys) {
            pair<BStarNode*, int> item = stack.back();
            stack.pop_back();
            BStarNode* p = item.first;
            int idx = item.second;

            BStarNode* left_sib = (idx > 0) ? p->children[idx - 1] : nullptr;
            BStarNode* right_sib = ((size_t)(idx + 1) < p->children.size()) ? p->children[idx + 1] : nullptr;

            if (left_sib && (int)left_sib->keys.size() > min_keys) {
                int sep = p->keys[idx - 1];
                int borrow = left_sib->keys.back();
                left_sib->keys.pop_back();
                cur->keys.insert(cur->keys.begin(), sep);
                p->keys[idx - 1] = borrow;
                if (!cur->leaf) {
                    BStarNode* c = left_sib->children.back();
                    left_sib->children.pop_back();
                    cur->children.insert(cur->children.begin(), c);
                }
                cur = p;
                continue;
            }
            if (right_sib && (int)right_sib->keys.size() > min_keys) {
                int sep = p->keys[idx];
                int borrow = right_sib->keys[0];
                right_sib->keys.erase(right_sib->keys.begin());
                cur->keys.push_back(sep);
                p->keys[idx] = borrow;
                if (!cur->leaf) {
                    BStarNode* c = right_sib->children[0];
                    right_sib->children.erase(right_sib->children.begin());
                    cur->children.push_back(c);
                }
                cur = p;
                continue;
            }

            vector<int> allk;
            SplitTwoRes res({}, 0, {});
            if (left_sib) {
                allk = left_sib->keys;
                allk.push_back(p->keys[idx - 1]);
                allk.insert(allk.end(), cur->keys.begin(), cur->keys.end());
                res = split_two_even(allk);
                left_sib->keys = res.left;
                cur->keys = res.right;
                p->keys.erase(p->keys.begin() + idx - 1);
                p->keys.insert(p->keys.begin() + idx - 1, res.sep);
                if (!cur->leaf) {
                    vector<BStarNode*> allc = left_sib->children;
                    allc.insert(allc.end(), cur->children.begin(), cur->children.end());
                    int split_idx = (int)res.left.size() + 1;
                    left_sib->children.assign(allc.begin(), allc.begin() + split_idx);
                    cur->children.assign(allc.begin() + split_idx, allc.end());
                }
                p->children.erase(p->children.begin() + idx);
            } else {
                allk = cur->keys;
                allk.push_back(p->keys[idx]);
                allk.insert(allk.end(), right_sib->keys.begin(), right_sib->keys.end());
                res = split_two_even(allk);
                cur->keys = res.left;
                right_sib->keys = res.right;
                p->keys.erase(p->keys.begin() + idx);
                p->keys.insert(p->keys.begin() + idx, res.sep);
                if (!cur->leaf) {
                    vector<BStarNode*> allc = cur->children;
                    allc.insert(allc.end(), right_sib->children.begin(), right_sib->children.end());
                    int split_idx = (int)res.left.size() + 1;
                    cur->children.assign(allc.begin(), allc.begin() + split_idx);
                    right_sib->children.assign(allc.begin() + split_idx, allc.end());
                }
                p->children.erase(p->children.begin() + idx + 1);
            }
            cur = p;
        }
        if (root->keys.empty() && !root->children.empty()) {
            root = root->children[0];
        }
    }

    // 中序遍历
    void inorder(BStarNode* n, vector<int>& res) {
        if (!n) return;
        if (n->leaf) {
            // 叶子直接输出key，不访问children
            for (int k : n->keys)
                res.push_back(k);
            return;
        }
        // 非叶子才递归子节点
        for (int i = 0; (size_t)i < n->keys.size(); i++) {
            inorder(n->children[i], res);
            res.push_back(n->keys[i]);
        }
        inorder(n->children.back(), res);
    }
    vector<int> traversal_in() {
        vector<int> r;
        inorder(root, r);
        return r;
    }

    void preorder(BStarNode* n, vector<int>& res) {
        if (!n) return;
        res.insert(res.end(), n->keys.begin(), n->keys.end());
        for (BStarNode* c : n->children)
            preorder(c, res);
    }
    vector<int> traversal_pre() {
        vector<int> r;
        preorder(root, r);
        return r;
    }

    void postorder(BStarNode* n, vector<int>& res) {
        if (!n) return;
        for (BStarNode* c : n->children)
            postorder(c, res);
        res.insert(res.end(), n->keys.begin(), n->keys.end());
    }
    vector<int> traversal_post() {
        vector<int> r;
        postorder(root, r);
        return r;
    }

    vector<int> traversal_level() {
        vector<int> r;
        queue<BStarNode*> q;
        q.push(root);
        while (!q.empty()) {
            BStarNode* u = q.front();
            q.pop();
            r.insert(r.end(), u->keys.begin(), u->keys.end());
            for (BStarNode* c : u->children)
                q.push(c);
        }
        return r;
    }

    int get_min() {
        BStarNode* cur = root;
        while (!cur->leaf)
            cur = cur->children[0];
        return cur->keys[0];
    }
    int get_max() {
        BStarNode* cur = root;
        while (!cur->leaf)
            cur = cur->children.back();
        return cur->keys.back();
    }

    void range_dfs(BStarNode* n, int l, int h, vector<int>& res) {
        if (n->leaf) {
            for (int k : n->keys) {
                if (k >= l && k <= h)
                    res.push_back(k);
            }
            return;
        }
        for (int i = 0; (size_t)i < n->keys.size(); i++) {
            range_dfs(n->children[i], l, h, res);
            if (n->keys[i] >= l && n->keys[i] <= h)
                res.push_back(n->keys[i]);
        }
        range_dfs(n->children.back(), l, h, res);
    }
    vector<int> range_query(int l, int h) {
        vector<int> res;
        range_dfs(root, l, h, res);
        return res;
    }
};

int main()
{
	cout << "=============== B* 树的基本操作展示 ===============\n";
    BStarTree bst(4);
    vector<int> insert_seq = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
    cout << "批量插入序列：";
    for (int num : insert_seq) {
        cout << num << " ";
        bst.insert(num);
    }
    cout << "\n\n";

    cout << "【中序遍历】：";
    vector<int> in = bst.traversal_in();
    for (int x : in) cout << x << " ";
    cout << "\n";

    cout << "【前序遍历】：";
    vector<int> pre = bst.traversal_pre();
    for (int x : pre) cout << x << " ";
    cout << "\n";

    cout << "【后序遍历】：";
    vector<int> post = bst.traversal_post();
    for (int x : post) cout << x << " ";
    cout << "\n";

    cout << "【层序遍历】：";
    vector<int> level = bst.traversal_level();
    for (int x : level) cout << x << " ";
    cout << "\n\n";

    cout << "最小值：" << bst.get_min() << "\n";
    cout << "最大值：" << bst.get_max() << "\n\n";

    int f1 = 7, f2 = 99;
    bool s1 = bst.search(f1);
    bool s2 = bst.search(f2);
    cout << "查找" << f1 << "：" << (s1 ? "存在" : "不存在") << "\n";
    cout << "查找" << f2 << "：" << (s2 ? "存在" : "不存在") << "\n\n";

    cout << "区间查询 [5,12]：";
    vector<int> range = bst.range_query(5, 12);
    for (int x : range) cout << x << " ";
    cout << "\n\n";

    int del_key = 7;
    cout << "删除键 " << del_key << "\n";
    bst.del(del_key);
    cout << "删除后中序序列：";
    vector<int> after_del = bst.traversal_in();
    for (int x : after_del) cout << x << " ";
    cout << "\n\n";

    cout << "重复插入6：";
    bst.insert(6);
    cout << "\n";

    return 0;
}
