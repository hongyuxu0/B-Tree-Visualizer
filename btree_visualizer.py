import tkinter as tk
import tkinter.ttk as ttk
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from tkinter import scrolledtext, simpledialog, messagebox
from dataclasses import dataclass
from typing import Dict, Generator, List, Optional, Tuple
import bisect
import copy
import random
import math
import threading
from collections import deque
import sys, os

def get_resource_path(filename: str) -> str:
    if hasattr(sys, "_MEIPASS"):
        base_dir = sys._MEIPASS
    else:
        base_dir = os.path.abspath(".")
    return os.path.join(base_dir, filename)

# 全局中文设置
plt.rcParams["font.sans-serif"] = ["Microsoft YaHei", "SimHei"]
plt.rcParams["axes.unicode_minus"] = False

# 全局唯一节点ID计数器
_uid_counter = 0


# ===================== 1. 核心数据结构 =====================
class BTreeNode:
    def __init__(self, leaf: bool = True):
        global _uid_counter
        _uid_counter += 1
        self.uid = _uid_counter
        self.keys: List[int] = []
        self.children: List["BTreeNode"] = []
        self.leaf: bool = leaf
        self.next: Optional["BTreeNode"] = None  # B+ 树叶子后继
        self.prev: Optional["BTreeNode"] = None  # B+ 树叶子前驱
        self.parent: Optional["BTreeNode"] = None  # 父指针


@dataclass
class Snapshot:
    root: BTreeNode
    highlights: Dict[int, str]
    phase: str
    message: str

# 性能结果数据类
@dataclass
class PerfResult:
    height: int
    split_cnt: int
    fill_rate: float
    cmp_times: int

# ===================== 2. 树算法基类 =====================
class BaseBTree:
    tree_type_name = "BaseBTree"

    def __init__(self, order: int):
        self.m = order  # 阶数：最大子节点数
        self.max_keys = order - 1  # 单节点最大键数
        self.root = BTreeNode(leaf=True)

    def _deepcopy_root(self) -> BTreeNode:
        if getattr(self, '_disable_deepcopy', False):
            return self.root
        # 第一步：先克隆纯树结构（父子关系，清空链表指针）
        node_map: Dict[int, BTreeNode] = {}

        def clone_structure(src: BTreeNode) -> BTreeNode:
            new_node = BTreeNode(leaf=src.leaf)
            new_node.uid = src.uid
            new_node.keys = src.keys.copy()
            new_node.parent = None
            new_node.prev = None
            new_node.next = None
            node_map[src.uid] = new_node
            for child in src.children:
                c_clone = clone_structure(child)
                c_clone.parent = new_node
                new_node.children.append(c_clone)
            return new_node

        root_clone = clone_structure(self.root)

        # 第二步：单独还原叶子链表（只在克隆节点内部建立链表，不关联原树）
        if self.tree_type_name == "B+ Tree":
            cur_src = self.first_leaf
            prev_clone = None
            while cur_src is not None:
                cur_clone = node_map[cur_src.uid]
                cur_clone.prev = prev_clone
                if prev_clone is not None:
                    prev_clone.next = cur_clone
                prev_clone = cur_clone
                cur_src = cur_src.next
        return root_clone

    def insert(self, key: int) -> Generator[Snapshot, None, None]:
        raise NotImplementedError

    def delete(self, key: int) -> Generator[Snapshot, None, None]:
        raise NotImplementedError

    def search(self, key: int) -> Generator[Snapshot, None, bool]:
        raise NotImplementedError

    def get_min(self) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "min", "空树，无最小值")
            return None
        node = self.root
        path = []
        while not node.leaf:
            path.append(node.uid)
            node = node.children[0]
        path.append(node.uid)
        highlights = {uid: "lightblue" for uid in path}
        highlights[node.uid] = "lightgreen"
        min_val = node.keys[0]
        yield Snapshot(self._deepcopy_root(), highlights, "min", f"树的最小值为：{min_val}")
        return min_val

    def get_max(self) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "max", "空树，无最大值")
            return None
        node = self.root
        path = []
        while not node.leaf:
            path.append(node.uid)
            node = node.children[-1]
        path.append(node.uid)
        highlights = {uid: "lightblue" for uid in path}
        highlights[node.uid] = "lightgreen"
        max_val = node.keys[-1]
        yield Snapshot(self._deepcopy_root(), highlights, "max", f"树的最大值为：{max_val}")
        return max_val

    def get_predecessor(self, key: int) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "pred", "空树，无前驱")
            return None
        node = self.root
        pred = None
        path = []
        while True:
            path.append(node.uid)
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                if not node.leaf:
                    pred_node = node.children[i]
                    while not pred_node.leaf:
                        path.append(pred_node.uid)
                        pred_node = pred_node.children[-1]
                    path.append(pred_node.uid)
                    pred = pred_node.keys[-1]
                elif i > 0:
                    pred = node.keys[i - 1]
                break
            if node.leaf:
                if i > 0:
                    pred = node.keys[i - 1]
                break
            node = node.children[i]
        highlights = {uid: "lightblue" for uid in path}
        if pred is not None:
            yield Snapshot(self._deepcopy_root(), highlights, "pred", f"键 {key} 的前驱为：{pred}")
        else:
            yield Snapshot(self._deepcopy_root(), highlights, "pred", f"键 {key} 没有前驱")
        return pred

    def get_successor(self, key: int) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "succ", "空树，无后继")
            return None
        node = self.root
        succ = None
        path = []
        while True:
            path.append(node.uid)
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                if not node.leaf:
                    succ_node = node.children[i + 1]
                    while not succ_node.leaf:
                        path.append(succ_node.uid)
                        succ_node = succ_node.children[0]
                    path.append(succ_node.uid)
                    succ = succ_node.keys[0]
                elif i < len(node.keys) - 1:
                    succ = node.keys[i + 1]
                break
            if node.leaf:
                if i < len(node.keys):
                    succ = node.keys[i]
                break
            node = node.children[i]
        highlights = {uid: "lightblue" for uid in path}
        if succ is not None:
            yield Snapshot(self._deepcopy_root(), highlights, "succ", f"键 {key} 的后继为：{succ}")
        else:
            yield Snapshot(self._deepcopy_root(), highlights, "succ", f"键 {key} 没有后继")
        return succ

    def range_query(self, low: int, high: int) -> Generator[Snapshot, None, List[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "range_done", "空树，查询结果为空")
            return []
        res = []
        highlights = {}
        node = self.root

        # 定位左边界
        while not node.leaf:
            highlights[node.uid] = "lightblue"
            i = bisect.bisect_left(node.keys, low)
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_search",
                           f"查找左边界，进入节点 {node.keys}")
            node = node.children[i]
        highlights[node.uid] = "lightblue"
        yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_search",
                       f"到达左边界叶子节点，开始收集结果")

        # 中序收集，遇上限终止
        def dfs_collect(n):
            nonlocal res
            if not n:
                return
            highlights[n.uid] = "lightgreen"
            if n.leaf:
                for k in n.keys:
                    if k > high:
                        highlights[n.uid] = "lightblue"
                        return
                    if k >= low:
                        res.append(k)
                highlights[n.uid] = "lightblue"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_collect",
                               f"处理叶子节点 {n.keys}，已收集：{res}")
                return
            # 索引节点：只递归子树，不收集自己的键
            for i in range(len(n.keys)):
                if n.keys[i] > high:
                    yield from dfs_collect(n.children[i])
                    highlights[n.uid] = "lightblue"
                    return
                yield from dfs_collect(n.children[i])
            yield from dfs_collect(n.children[-1])
            highlights[n.uid] = "lightblue"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_collect",
                           f"处理索引节点 {n.keys}，已收集：{res}")

        yield from dfs_collect(node)

        yield Snapshot(self._deepcopy_root(), highlights, "range_done",
                       f"范围 [{low}, {high}] 内的键：{res}，共 {len(res)} 个")
        return res

    def count_keys(self) -> int:
        def _count(node):
            if not node:
                return 0
            total = len(node.keys)
            for c in node.children:
                total += _count(c)
            return total

        return _count(self.root)

    def clear(self):
        global _uid_counter
        _uid_counter = 0
        self.root = BTreeNode(leaf=True)

    def count_keys_animated(self) -> Generator[Snapshot, None, int]:
        res = []
        def dfs(node):
            yield Snapshot(self._deepcopy_root(), {node.uid:"lightblue"}, "count", f"遍历节点 {node.keys}")
            res.extend(node.keys)
            if not node.leaf:
                for c in node.children:
                    yield from dfs(c)
        yield from dfs(self.root)
        total = len(res)
        yield Snapshot(self._deepcopy_root(), {}, "count_done", f"统计完成，树内总键数量：{total}")
        return total

    def check_properties(self) -> tuple[bool, str]:
        raise NotImplementedError

    def check_properties_animated(self) -> Generator[Snapshot, None, tuple[bool, str]]:
        raise NotImplementedError

    def traversal(self, mode: str) -> List[int]:
        res = []

        def preorder(n):
            if not n:
                return
            res.extend(n.keys)
            for c in n.children:
                preorder(c)

        def inorder(n):
            if not n:
                return
            if n.leaf:
                res.extend(n.keys)
                return
            for i in range(len(n.keys)):
                inorder(n.children[i])
                res.append(n.keys[i])
            inorder(n.children[-1])

        def postorder(n):
            if not n:
                return
            for c in n.children:
                postorder(c)
            res.extend(n.keys)

        def levelorder(n):
            q = deque([n])
            while q:
                level_size = len(q)
                for _ in range(level_size):
                    node = q.popleft()
                    res.extend(node.keys)
                    if not node.leaf:
                        q.extend(node.children)

        if mode == "前序":
            preorder(self.root)
        elif mode == "中序":
            inorder(self.root)
        elif mode == "后序":
            postorder(self.root)
        elif mode == "层序":
            levelorder(self.root)
        return res

    def traversal_animated(self, mode: str) -> Generator[Snapshot, None, List[int]]:
        res = []
        highlights = {}

        if mode == "前序":
            def dfs(n):
                if not n:
                    return
                highlights[n.uid] = "lightgreen"
                res.extend(n.keys)
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                               f"前序遍历：访问节点 {n.keys}，已收集：{res}")
                highlights[n.uid] = "lightblue"
                for c in n.children:
                    yield from dfs(c)

            yield from dfs(self.root)

        elif mode == "中序":
            def dfs(n):
                if not n:
                    return
                highlights[n.uid] = "lightblue"
                if n.leaf:
                    for k in n.keys:
                        res.append(k)
                        highlights[n.uid] = "lightgreen"
                        yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                                       f"中序遍历：取出叶子键 {k}，已收集：{res}")
                        highlights[n.uid] = "lightblue"
                    return
                for i in range(len(n.keys)):
                    yield from dfs(n.children[i])
                    res.append(n.keys[i])
                    highlights[n.uid] = "lightgreen"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                                   f"中序遍历：取出键 {n.keys[i]}，已收集：{res}")
                    highlights[n.uid] = "lightblue"
                yield from dfs(n.children[-1])

            yield from dfs(self.root)

        elif mode == "后序":
            def dfs(n):
                if not n:
                    return
                highlights[n.uid] = "lightblue"
                for c in n.children:
                    yield from dfs(c)
                highlights[n.uid] = "lightgreen"
                res.extend(n.keys)
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                               f"后序遍历：访问节点 {n.keys}，已收集：{res}")
                highlights[n.uid] = "lightblue"

            yield from dfs(self.root)

        elif mode == "层序":
            q = deque([self.root])
            while q:
                level_size = len(q)
                for _ in range(level_size):
                    node = q.popleft()
                    highlights[node.uid] = "lightgreen"
                    res.extend(node.keys)
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                                   f"层序遍历：当前节点 {node.keys}，已收集：{res}")
                    highlights[node.uid] = "lightblue"
                    if not node.leaf:
                        q.extend(node.children)

        yield Snapshot(self._deepcopy_root(), highlights, "traversal_done",
                       f"{mode}遍历完成，结果：{res}，共 {len(res)} 个")
        return res


# ---------- B 树 ----------
class BTree(BaseBTree):
    tree_type_name = "B-Tree"

    def __init__(self, order: int):
        super().__init__(order)
        self.min_keys = (self.m - 1) // 2  # 非根节点最小键数

    def insert(self, key: int) -> Generator[Snapshot, None, None]:
        stack: List[tuple[BTreeNode, int]] = []
        node = self.root

        while not node.leaf:
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "duplicate", f"键 {key} 已存在，插入失败")
                return
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search", f"查找路径：进入节点 {node.keys}")

        if key in node.keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "duplicate", f"键 {key} 已存在，插入失败")
            return

        bisect.insort(node.keys, key)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "insert",
                       f"在叶子节点插入 {key}，当前节点：{node.keys}")

        # 逐层向上分裂
        while len(node.keys) > self.max_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "overflow",
                           f"节点 {node.keys} 溢出（键数={len(node.keys)}），准备分裂")

            mid = len(node.keys) // 2
            mid_key = node.keys[mid]
            left = BTreeNode(leaf=node.leaf)
            right = BTreeNode(leaf=node.leaf)
            left.keys = node.keys[:mid]
            right.keys = node.keys[mid + 1:]

            if not node.leaf:
                left.children = node.children[:mid + 1]
                right.children = node.children[mid + 1:]
                for c in left.children:
                    c.parent = left
                for c in right.children:
                    c.parent = right

            if not stack:
                # 根节点分裂
                new_root = BTreeNode(leaf=False)
                new_root.keys = [mid_key]
                new_root.children = [left, right]
                left.parent = new_root
                right.parent = new_root
                self.root = new_root
                yield Snapshot(self._deepcopy_root(),
                               {left.uid: "orange", right.uid: "orange", new_root.uid: "plum"},
                               "new_root",
                               f"创建新根节点 {new_root.keys}，分裂为左{left.keys}、右{right.keys}")
                return
            else:
                parent, idx = stack.pop()
                bisect.insort(parent.keys, mid_key)
                parent.children.pop(idx)
                parent.children[idx:idx] = [left, right]
                left.parent = parent
                right.parent = parent
                node = parent
                yield Snapshot(self._deepcopy_root(),
                               {left.uid: "orange", right.uid: "orange", parent.uid: "plum"},
                               "push_up",
                               f"分裂为左{left.keys}、右{right.keys}，中间键 {mid_key} 上推到父节点")

    def delete(self, key: int) -> Generator[Snapshot, None, None]:
        stack = []
        node = self.root

        # 查找待删除键
        while True:
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                break
            if node.leaf:
                yield Snapshot(self._deepcopy_root(), {}, "not_found", f"键 {key} 不存在，删除失败")
                return
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search",
                           f"查找键 {key}，进入节点 {node.keys}")

        # 内部节点：用叶子前驱替换
        if not node.leaf:
            pred = node.children[i]
            stack.append((node, i))
            while not pred.leaf:
                stack.append((pred, len(pred.keys)))
                pred = pred.children[-1]
            node.keys[i] = pred.keys[-1]
            key_del = pred.keys[-1]
            node = pred
        else:
            key_del = key

        node.keys.remove(key_del)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "delete",
                       f"删除键 {key_del}，节点变为 {node.keys}")

        # 逐层向上处理下溢
        while node is not self.root and len(node.keys) < self.min_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "underflow",
                           f"节点下溢（键数={len(node.keys)}），准备处理")

            parent, idx = stack.pop()
            left_sib = parent.children[idx - 1] if idx > 0 else None
            right_sib = parent.children[idx + 1] if idx < len(parent.children) - 1 else None

            # 向左兄弟借键
            if left_sib and len(left_sib.keys) > self.min_keys:
                borrowed = left_sib.keys.pop()
                p_key = parent.keys[idx - 1]
                node.keys.insert(0, p_key)
                parent.keys[idx - 1] = borrowed
                if not node.leaf:
                    moved = left_sib.children.pop()
                    node.children.insert(0, moved)
                    moved.parent = node
                yield Snapshot(self._deepcopy_root(), {left_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                               f"从左兄弟借键 {borrowed}，父键 {p_key} 下移")
                break  # 借键不改变父节点键数，无需继续向上

            # 向右兄弟借键
            elif right_sib and len(right_sib.keys) > self.min_keys:
                borrowed = right_sib.keys.pop(0)
                p_key = parent.keys[idx]
                node.keys.append(p_key)
                parent.keys[idx] = borrowed
                if not node.leaf:
                    moved = right_sib.children.pop(0)
                    node.children.append(moved)
                    moved.parent = node
                yield Snapshot(self._deepcopy_root(), {right_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                               f"从右兄弟借键 {borrowed}，父键 {p_key} 下移")
                break  # 借键不改变父节点键数，无需继续向上

            # 无法借键，合并节点
            else:
                if left_sib:
                    merged_keys = left_sib.keys + [parent.keys.pop(idx - 1)] + node.keys
                    merged_children = left_sib.children + node.children if not node.leaf else []
                    left_sib.keys = merged_keys
                    if not node.leaf:
                        left_sib.children = merged_children
                        for c in node.children:
                            c.parent = left_sib
                    parent.children.pop(idx)
                    yield Snapshot(self._deepcopy_root(), {left_sib.uid: "lightgray"}, "merge",
                                   f"与左兄弟合并，合并后：{left_sib.keys}")
                else:
                    merged_keys = node.keys + [parent.keys.pop(idx)] + right_sib.keys
                    merged_children = node.children + right_sib.children if not node.leaf else []
                    node.keys = merged_keys
                    if not node.leaf:
                        node.children = merged_children
                        for c in right_sib.children:
                            c.parent = node
                    parent.children.pop(idx + 1)
                    yield Snapshot(self._deepcopy_root(), {node.uid: "lightgray"}, "merge",
                                   f"与右兄弟合并，合并后：{node.keys}")

                # 父节点减少一个键，继续向上检查下溢
                node = parent

        # 根节点收缩
        if not self.root.keys and self.root.children:
            self.root = self.root.children[0]
            self.root.parent = None
            yield Snapshot(self._deepcopy_root(), {self.root.uid: "plum"}, "new_root",
                           "根节点为空，提升子节点为新根")

    def search(self, key: int) -> Generator[Snapshot, None, bool]:
        node = self.root
        while True:
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search",
                           f"查找键 {key}，当前节点：{node.keys}")
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "found", f"✅ 找到键 {key}")
                return True
            if node.leaf:
                yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "not_found", f"❌ 未找到键 {key}")
                return False
            node = node.children[i]

    def check_properties(self) -> tuple[bool, str]:
        def get_subtree_max(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[-1]
            return n.keys[-1] if n.keys else -float('inf')

        def _check(node, depth, leaf_depth):
            if node is not self.root and len(node.keys) < self.min_keys:
                return False, f"非根节点键数 {len(node.keys)} 小于最小值 {self.min_keys}"
            if len(node.keys) > self.max_keys:
                return False, f"节点键数 {len(node.keys)} 超过上限 {self.max_keys}"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i - 1]:
                    return False, "节点键未严格递增"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    return False, f"子节点数 {len(node.children)} 不等于键数+1 {len(node.keys) + 1}"
                for i, key in enumerate(node.keys):
                    left_max = get_subtree_max(node.children[i])
                    if left_max >= key:
                        return False, f"分隔键 {key} 错误：左子树最大值 {left_max} 不小于分隔键"
                for c in node.children:
                    ok, msg = _check(c, depth + 1, leaf_depth)
                    if not ok:
                        return False, msg
            else:
                if leaf_depth[0] is None:
                    leaf_depth[0] = depth
                elif depth != leaf_depth[0]:
                    return False, "叶子节点不在同一层"
            return True, "符合B树性质"

        if not self.root.keys:
            return True, "空树，符合性质"
        leaf_depth = [None]
        return _check(self.root, 0, leaf_depth)

    def check_properties_animated(self) -> Generator[Snapshot, None, tuple[bool, str]]:
        highlights = {}

        def get_subtree_max(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[-1]
            return n.keys[-1] if n.keys else -float('inf')

        def _check(node, depth, leaf_depth):
            highlights[node.uid] = "lightblue"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check",
                           f"检查节点 {node.keys}，深度 {depth}")

            if node is not self.root and len(node.keys) < self.min_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                               f"❌ 非根节点键数 {len(node.keys)} 小于最小值 {self.min_keys}")
                return False, f"非根节点键数 {len(node.keys)} 小于最小值 {self.min_keys}"
            if len(node.keys) > self.max_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                               f"❌ 节点键数 {len(node.keys)} 超过上限 {self.max_keys}")
                return False, f"节点键数 {len(node.keys)} 超过上限 {self.max_keys}"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i - 1]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                   "❌ 节点键未严格递增")
                    return False, "节点键未严格递增"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                   f"❌ 子节点数 {len(node.children)} 不等于键数+1 {len(node.keys) + 1}")
                    return False, f"子节点数 {len(node.children)} 不等于键数+1 {len(node.keys) + 1}"

                for i, key in enumerate(node.keys):
                    left_max = get_subtree_max(node.children[i])
                    if left_max >= key:
                        highlights[node.uid] = "salmon"
                        yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                       f"❌ 分隔键 {key} 非法：左子树最大值 {left_max} 不小于分隔键")
                        return False, f"分隔键 {key} 非法"
                for c in node.children:
                    ok, msg = yield from _check(c, depth + 1, leaf_depth)
                    if not ok:
                        return False, msg
            else:
                if leaf_depth[0] is None:
                    leaf_depth[0] = depth
                elif depth != leaf_depth[0]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                   "❌ 叶子节点不在同一层")
                    return False, "叶子节点不在同一层"
            highlights[node.uid] = "lightgreen"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_pass",
                           f"✅ 节点 {node.keys} 符合性质")
            return True, "符合B树性质"

        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "check_done", "✅ 空树，符合性质")
            return True, "空树，符合性质"
        leaf_depth = [None]
        ok, msg = yield from _check(self.root, 0, leaf_depth)
        if ok:
            yield Snapshot(self._deepcopy_root(), highlights, "check_done", f"✅ {msg}")
        return ok, msg

# ---------- B+ 树 ----------
class BPlusTree(BaseBTree):
    tree_type_name = "B+ Tree"

    def __init__(self, order: int):
        super().__init__(order)
        self.min_keys = (self.m - 1) // 2
        self.first_leaf = self.root

    def _get_leftmost_leaf(self, node: BTreeNode) -> BTreeNode:
        while not node.leaf:
            node = node.children[0]
        return node

    def _get_rightmost_leaf(self, node: BTreeNode) -> BTreeNode:
        while not node.leaf:
            node = node.children[-1]
        return node

    def _full_refresh_all_index_sep(self, root_node: BTreeNode):
        if root_node.leaf:
            return
        for i, child in enumerate(root_node.children):
            child_min = self._get_leftmost_leaf(child).keys[0]
            if i > 0:
                root_node.keys[i - 1] = child_min
            self._full_refresh_all_index_sep(child)

    def _sync_all_ancestor_recursive(self, target: BTreeNode):
        if not target.keys:  # 防止空节点传入
            return
        p = target.parent
        if p is None:
            return
        idx = p.children.index(target)
        if idx > 0:
            p.keys[idx - 1] = self._get_leftmost_leaf(target).keys[0]
        if idx + 1 < len(p.children):
            r_child = p.children[idx + 1]
            p.keys[idx] = self._get_leftmost_leaf(r_child).keys[0]
        self._sync_all_ancestor_recursive(p)

    def _link_leaf_pair(self, left: Optional[BTreeNode], right: BTreeNode):
        if left is None:
            right.prev = None
            if self.first_leaf is not None:
                old_first = self.first_leaf
                right.next = old_first
                old_first.prev = right
            self.first_leaf = right
            return
        old_next = left.next
        left.next = right
        right.prev = left
        right.next = old_next
        if old_next is not None:
            old_next.prev = right

    def _detach_single_leaf(self, node: BTreeNode):
        prev = node.prev
        nxt = node.next
        if prev is not None:
            prev.next = nxt
        if nxt is not None:
            nxt.prev = prev
        if node == self.first_leaf:
            self.first_leaf = nxt
        node.prev = None
        node.next = None

    def clear(self):
        super().clear()
        self.first_leaf = self.root

    def count_keys(self) -> int:
        cnt = 0
        cur = self.first_leaf
        while cur:
            cnt += len(cur.keys)
            cur = cur.next
        return cnt

    def count_keys_animated(self) -> Generator[Snapshot, None, int]:
        total = 0
        cur = self.first_leaf
        while cur:
            yield Snapshot(self._deepcopy_root(), {cur.uid: "lightblue"}, "count",
                           f"遍历叶子 {cur.keys}，新增{len(cur.keys)}个键")
            total += len(cur.keys)
            cur = cur.next
        yield Snapshot(self._deepcopy_root(), {}, "count_done", f"统计完成，总键数：{total}")
        return total

    def traversal(self, mode: str) -> List[int]:
        res = []
        if mode == "中序":
            cur = self.first_leaf
            while cur:
                res.extend(cur.keys)
                cur = cur.next
            return res
        return super().traversal(mode)

    def traversal_animated(self, mode: str) -> Generator[Snapshot, None, List[int]]:
        res = []
        highlights = {}
        if mode == "中序":
            cur = self.first_leaf
            while cur:
                highlights[cur.uid] = "lightgreen"
                for k in cur.keys:
                    res.append(k)
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "traversal",
                                   f"中序取出键 {k}，已收集：{res}")
                highlights[cur.uid] = "lightblue"
                cur = cur.next
            yield Snapshot(self._deepcopy_root(), highlights, "traversal_done",
                           f"中序遍历完成，数据：{res}，共{len(res)}个")
            return res
        yield from super().traversal_animated(mode)
        return res

    def insert(self, key: int) -> Generator[Snapshot, None, None]:
        stack: List[Tuple[BTreeNode, int]] = []
        node = self.root
        while not node.leaf:
            i = bisect.bisect_left(node.keys, key)
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search",
                           f"查找路径：进入节点 {node.keys}")
        if key in node.keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "duplicate", f"键 {key} 已存在")
            return
        bisect.insort(node.keys, key)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "insert",
                       f"叶子插入 {key}，当前：{node.keys}")

        while len(node.keys) > self.max_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "overflow",
                           f"节点溢出（键数={len(node.keys)}）")
            left = BTreeNode(leaf=node.leaf)
            right = BTreeNode(leaf=node.leaf)

            if node.leaf:
                mid = (len(node.keys) + 1) // 2
                left.keys = node.keys[:mid]
                right.keys = node.keys[mid:]
                sep_up = right.keys[0]

                # 保存原节点的前后邻居
                prev_node = node.prev
                next_node = node.next

                # 将 left 和 right 插入到原 node 的位置
                left.prev = prev_node
                left.next = right
                right.prev = left
                right.next = next_node

                if prev_node is not None:
                    prev_node.next = left
                else:
                    self.first_leaf = left

                if next_node is not None:
                    next_node.prev = right

                # 断开原 node 的链接（不再属于链表）
                node.prev = None
                node.next = None
            else:
                mid = len(node.keys) // 2
                sep_up = node.keys[mid]
                left.keys = node.keys[:mid]
                right.keys = node.keys[mid + 1:]
                left.children = node.children[:mid + 1]
                right.children = node.children[mid + 1:]
                for c in left.children:
                    c.parent = left
                for c in right.children:
                    c.parent = right

            if not stack:
                new_root = BTreeNode(leaf=False)
                new_root.keys = [sep_up]
                new_root.children = [left, right]
                left.parent = new_root
                right.parent = new_root
                self.root = new_root
                self.first_leaf = self._get_leftmost_leaf(self.root)
                yield Snapshot(self._deepcopy_root(),
                               {left.uid: "orange", right.uid: "orange", new_root.uid: "plum"}, "new_root",
                               f"新建根 {new_root.keys}，分裂左{left.keys}右{right.keys}")
                self._full_refresh_all_index_sep(self.root)
                return

            parent, idx = stack.pop()
            bisect.insort(parent.keys, sep_up)
            parent.children.pop(idx)
            parent.children[idx:idx] = [left, right]
            left.parent = parent
            right.parent = parent
            node = parent
            yield Snapshot(self._deepcopy_root(), {left.uid: "orange", right.uid: "orange", parent.uid: "plum"},
                           "push_up", f"分裂上推分隔键 {sep_up} 至父节点")
            self._sync_all_ancestor_recursive(node)

        self.first_leaf = self._get_leftmost_leaf(self.root)
        self._full_refresh_all_index_sep(self.root)

    def delete(self, key: int) -> Generator[Snapshot, None, None]:
        stack: List[Tuple[BTreeNode, int]] = []
        node = self.root
        while not node.leaf:
            i = bisect.bisect_right(node.keys, key)  # 关键修复：使用 bisect_right
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search",
                           f"查找键 {key}，进入节点 {node.keys}")
        if key not in node.keys:
            yield Snapshot(self._deepcopy_root(), {}, "not_found", f"键 {key} 不存在")
            return

        old_min = node.keys[0]
        old_max = node.keys[-1]
        node.keys.remove(key)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "delete", f"删除叶子键 {key}，剩余：{node.keys}")

        new_min = node.keys[0] if node.keys else -1
        new_max = node.keys[-1] if node.keys else -1
        if node.keys and (new_min != old_min or new_max != old_max):
            self._sync_all_ancestor_recursive(node)

        while node is not self.root and len(node.keys) < self.min_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "underflow", f"节点下溢（键数={len(node.keys)}）")
            parent, idx = stack.pop()
            left_sib = parent.children[idx - 1] if idx > 0 else None
            right_sib = parent.children[idx + 1] if idx < len(parent.children) - 1 else None

            if node.leaf:
                if left_sib and left_sib.leaf and len(left_sib.keys) > self.min_keys:
                    borrow = left_sib.keys.pop()
                    node.keys.insert(0, borrow)
                    self._sync_all_ancestor_recursive(parent)
                    yield Snapshot(self._deepcopy_root(), {left_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                                   f"左借{borrow}")
                    node = parent
                    continue  # 继续检查父节点下溢
                elif right_sib and right_sib.leaf and len(right_sib.keys) > self.min_keys:
                    borrow = right_sib.keys.pop(0)
                    node.keys.append(borrow)
                    self._sync_all_ancestor_recursive(parent)
                    yield Snapshot(self._deepcopy_root(), {right_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                                   f"右借{borrow}")
                    node = parent
                    continue
                else:
                    if left_sib:
                        # 与左叶子合并
                        left_sib.keys.extend(node.keys)
                        # 链表操作：left_sib 跳过 node 连接到 node.next
                        left_sib.next = node.next
                        if node.next is not None:
                            node.next.prev = left_sib
                        # 断开 node
                        node.prev = None
                        node.next = None
                        # 索引操作
                        parent.keys.pop(idx - 1)
                        parent.children.pop(idx)
                        yield Snapshot(self._deepcopy_root(), {left_sib.uid: "lightgray"}, "merge",
                                       f"与左叶子合并：{left_sib.keys}")
                    elif right_sib:
                        # 与右叶子合并
                        node.keys.extend(right_sib.keys)
                        # 链表操作：node 跳过 right_sib 连接到 right_sib.next
                        node.next = right_sib.next
                        if right_sib.next is not None:
                            right_sib.next.prev = node
                        # 断开 right_sib
                        right_sib.prev = None
                        right_sib.next = None
                        # 索引操作
                        parent.keys.pop(idx)
                        parent.children.pop(idx + 1)
                        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgray"}, "merge",
                                       f"与右叶子合并：{node.keys}")
                    node = parent
            else:
                # 内部节点借键/合并（与B树相同）
                if left_sib and len(left_sib.keys) > self.min_keys:
                    node.keys.insert(0, parent.keys[idx - 1])
                    parent.keys[idx - 1] = left_sib.keys.pop()
                    c = left_sib.children.pop()
                    node.children.insert(0, c)
                    c.parent = node
                    break
                elif right_sib and len(right_sib.keys) > self.min_keys:
                    node.keys.append(parent.keys[idx])
                    parent.keys[idx] = right_sib.keys.pop(0)
                    c = right_sib.children.pop(0)
                    node.children.append(c)
                    c.parent = node
                    break
                if left_sib:
                    left_sib.keys.append(parent.keys.pop(idx - 1))
                    left_sib.keys.extend(node.keys)
                    left_sib.children.extend(node.children)
                    for c in node.children:
                        c.parent = left_sib
                    parent.children.pop(idx)
                    node = left_sib
                else:
                    node.keys.append(parent.keys.pop(idx))
                    node.keys.extend(right_sib.keys)
                    node.children.extend(right_sib.children)
                    for c in right_sib.children:
                        c.parent = node
                    parent.children.pop(idx + 1)
                    node = parent

        # 根节点收缩
        if len(self.root.keys) == 0 and len(self.root.children) > 0:
            self.root = self.root.children[0]
            self.root.parent = None

        self.first_leaf = self._get_leftmost_leaf(self.root)
        self._full_refresh_all_index_sep(self.root)

    def search(self, key: int) -> Generator[Snapshot, None, bool]:
        node = self.root
        while not node.leaf:
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search",
                           f"查找键 {key}，索引节点：{node.keys}")
            i = bisect.bisect_right(node.keys, key)  # 修复：改为 bisect_right
            node = node.children[i]
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search", f"到达叶子节点：{node.keys}")
        found = key in node.keys
        if found:
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "found", f"✅ 找到键 {key}")
        else:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "not_found", f"❌ 未找到键 {key}")
        return found

    def range_query(self, low: int, high: int) -> Generator[Snapshot, None, List[int]]:
        if self.first_leaf is None:
            yield Snapshot(self._deepcopy_root(), {}, "range_done", "空树，查询结果为空")
            return []
        res = []
        highlights = {}
        node = self.root
        while not node.leaf:
            highlights[node.uid] = "lightblue"
            i = bisect.bisect_right(node.keys, low)  # 修复：改为 bisect_right
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_search",
                           f"查找左边界，索引节点 {node.keys}")
            node = node.children[i]
        highlights[node.uid] = "lightblue"
        yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_search",
                       f"到达左边界叶子 {node.keys}，开始收集")
        while node:
            highlights[node.uid] = "lightgreen"
            for k in node.keys:
                if low <= k <= high:
                    res.append(k)
                elif k > high:
                    highlights[node.uid] = "lightblue"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_done",
                                   f"范围[{low},{high}]结果：{res}，共{len(res)}个")
                    return res
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "range_collect",
                           f"遍历叶子 {node.keys}，已收集{res}")
            highlights[node.uid] = "lightblue"
            node = node.next
        yield Snapshot(self._deepcopy_root(), highlights, "range_done",
                       f"范围[{low},{high}]结果：{res}，共{len(res)}个")
        return res

    def check_properties(self) -> Tuple[bool, str]:
        # 检查叶子链表
        cur_leaf = self.first_leaf
        prev_leaf = None
        while cur_leaf:
            if len(cur_leaf.keys) < self.min_keys and cur_leaf is not self.root:
                return False, f"叶子键数不足最小值{self.min_keys}"
            if prev_leaf is not None and cur_leaf.keys[0] <= prev_leaf.keys[-1]:
                return False, "叶子链表数值无序"
            if cur_leaf.prev != prev_leaf:
                return False, "叶子prev指针断裂"
            if prev_leaf is not None and prev_leaf.next != cur_leaf:
                return False, "叶子next指针断裂"
            prev_leaf = cur_leaf
            cur_leaf = cur_leaf.next

        # 递归检查索引节点
        def dfs_check(node: BTreeNode, depth: int, leaf_depth: List[Optional[int]]):
            if len(node.keys) > self.max_keys:
                return False, "索引键数超限"
            if node is not self.root and len(node.keys) < self.min_keys:
                return False, "索引键数不足下限"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i - 1]:
                    return False, "索引内部键无序"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    return False, "索引子节点数量不匹配"
                # 验证索引键等于右子树最小值
                for i, key in enumerate(node.keys):
                    right_min = self._get_leftmost_leaf(node.children[i + 1]).keys[0]
                    if key != right_min:
                        return False, f"索引键 {key} 不等于右子树最小值 {right_min}"
                for child in node.children:
                    ok, msg = dfs_check(child, depth + 1, leaf_depth)
                    if not ok:
                        return False, msg
            else:
                if leaf_depth[0] is None:
                    leaf_depth[0] = depth
                elif depth != leaf_depth[0]:
                    return False, "叶子深度不一致"
                return True, ""
            return True, ""

        if len(self.root.keys) == 0:
            return True, "空树合规"
        leaf_depth = [None]
        return dfs_check(self.root, 0, leaf_depth)

    def check_properties_animated(self) -> Generator[Snapshot, None, Tuple[bool, str]]:
        highlights = {}
        # 检查叶子链表
        cur_leaf = self.first_leaf
        prev_leaf = None
        while cur_leaf:
            highlights[cur_leaf.uid] = "lightblue"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check", f"校验叶子 {cur_leaf.keys}")
            if len(cur_leaf.keys) < self.min_keys and cur_leaf is not self.root:
                highlights[cur_leaf.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                               f"❌ 叶子键不足最小{self.min_keys}")
                return False, "叶子键不足"
            if prev_leaf is not None and cur_leaf.keys[0] <= prev_leaf.keys[-1]:
                highlights[cur_leaf.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ 叶子链表无序")
                return False, "链表无序"
            if cur_leaf.prev != prev_leaf:
                highlights[cur_leaf.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ prev指针断裂")
                return False, "指针错误"
            if prev_leaf is not None and prev_leaf.next != cur_leaf:
                highlights[cur_leaf.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ next指针断裂")
                return False, "指针错误"
            highlights[cur_leaf.uid] = "lightgreen"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_pass", f"✅ 叶子{cur_leaf.keys}合法")
            prev_leaf = cur_leaf
            cur_leaf = cur_leaf.next

        # 递归检查索引节点
        def dfs_anim(node: BTreeNode, depth: int, leaf_depth: List[Optional[int]]):
            highlights[node.uid] = "lightblue"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check", f"校验索引 {node.keys}")
            if len(node.keys) > self.max_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", f"❌ 键超上限{self.max_keys}")
                return False, "超限"
            if node is not self.root and len(node.keys) < self.min_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                               f"❌ 键低于下限{self.min_keys}")
                return False, "不足"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i - 1]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ 键无序")
                    return False, "无序"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                   f"❌ 子节点{len(node.children)} != 键+1{len(node.keys) + 1}")
                    return False, "数量不匹配"
                # 验证索引键等于右子树最小值
                for i, key in enumerate(node.keys):
                    right_min = self._get_leftmost_leaf(node.children[i + 1]).keys[0]
                    if key != right_min:
                        highlights[node.uid] = "salmon"
                        yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail",
                                       f"❌ 索引键 {key} 不等于右子树最小值 {right_min}")
                        return False, f"索引键 {key} 不等于右子树最小值 {right_min}"
                for child in node.children:
                    ok, msg = yield from dfs_anim(child, depth + 1, leaf_depth)
                    if not ok:
                        return False, msg
            else:
                if leaf_depth[0] is None:
                    leaf_depth[0] = depth
                elif depth != leaf_depth[0]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ 叶子深度不同")
                    return False, "深度错误"
                return True, ""
            return True, ""

        if len(self.root.keys) == 0:
            yield Snapshot(self._deepcopy_root(), {}, "check_done", "✅ 空树合法")
            return True, "合规"
        leaf_depth = [None]
        ok, msg = yield from dfs_anim(self.root, 0, leaf_depth)
        if ok:
            yield Snapshot(self._deepcopy_root(), highlights, "check_done", "✅ 整棵B+树全部符合规范")
        return ok, msg

    def get_predecessor(self, key: int) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "pred", "空树，无前驱")
            return None
        node = self.root
        pred = None
        path = []
        # 记录从根到叶子父节点的所有索引节点
        while not node.leaf:
            path.append(node.uid)
            i = bisect.bisect_right(node.keys, key)
            node = node.children[i]
        # 此时 node 是叶子节点，path 记录了所有索引节点（不含叶子）
        # 在叶子中查找前驱
        i = bisect.bisect_left(node.keys, key)
        if i > 0:
            pred = node.keys[i - 1]
        else:
            cur = node.prev
            while cur is not None and len(cur.keys) == 0:
                cur = cur.prev
            if cur is not None and len(cur.keys) > 0:
                pred = cur.keys[-1]
        highlights = {uid: "lightblue" for uid in path}
        if pred is not None:
            yield Snapshot(self._deepcopy_root(), highlights, "pred", f"键 {key} 的前驱为：{pred}")
        else:
            yield Snapshot(self._deepcopy_root(), highlights, "pred", f"键 {key} 没有前驱")
        return pred

    def get_successor(self, key: int) -> Generator[Snapshot, None, Optional[int]]:
        if not self.root.keys:
            yield Snapshot(self._deepcopy_root(), {}, "succ", "空树，无后继")
            return None
        node = self.root
        succ = None
        path = []
        while not node.leaf:
            path.append(node.uid)
            i = bisect.bisect_right(node.keys, key)
            node = node.children[i]
        # 叶子中找后继
        i = bisect.bisect_right(node.keys, key)
        if i < len(node.keys):
            succ = node.keys[i]
        else:
            cur = node.next
            while cur is not None and len(cur.keys) == 0:
                cur = cur.next
            if cur is not None and len(cur.keys) > 0:
                succ = cur.keys[0]
        highlights = {uid: "lightblue" for uid in path}
        if succ is not None:
            yield Snapshot(self._deepcopy_root(), highlights, "succ", f"键 {key} 的后继为：{succ}")
        else:
            yield Snapshot(self._deepcopy_root(), highlights, "succ", f"键 {key} 没有后继")
        return succ

# ---------- B* 树 ----------
class BStarTree(BaseBTree):
    tree_type_name = "B* Tree"

    def __init__(self, order: int):
        super().__init__(order)
        self.max_keys = self.m - 1
        self.min_child = math.ceil(2 * self.m / 3)
        self.min_keys = max(1, self.min_child - 1)

    def _split_two_even(self, all_keys: List[int]) -> Tuple[List[int], int, List[int]]:
        total = len(all_keys)
        mid = total // 2
        left = all_keys[:mid]
        sep = all_keys[mid]
        right = all_keys[mid + 1:]
        return left, sep, right

    def _try_split_three(self, all_keys: List[int]) -> Optional[Tuple[List[int], int, List[int], int, List[int]]]:
        total = len(all_keys)
        min_seg = self.min_keys
        min_total = min_seg * 3 + 2
        if total < min_total:
            return None
        pos1 = max(min_seg, total // 3)
        pos2 = min(total - min_seg - 1, 2 * total // 3)
        if pos2 - pos1 - 1 < min_seg:
            return None
        left = all_keys[:pos1]
        k1 = all_keys[pos1]
        mid = all_keys[pos1 + 1: pos2]
        k2 = all_keys[pos2]
        right = all_keys[pos2 + 1:]
        return left, k1, mid, k2, right

    def _full_reset_parent(self, node: BTreeNode):
        for child in node.children:
            child.parent = node
            self._full_reset_parent(child)

    def insert(self, key: int) -> Generator[Snapshot, None, None]:
        stack: List[Tuple[BTreeNode, int]] = []
        node = self.root
        while not node.leaf:
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "duplicate", f"键{key}已存在")
                return
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search", f"查找进入节点 {node.keys}")
        if key in node.keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "duplicate", f"键{key}已存在")
            return
        bisect.insort(node.keys, key)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "insert", f"插入{key}，节点{node.keys}")
        while len(node.keys) > self.max_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "overflow", f"节点溢出{node.keys}")
            if node is self.root:
                mid = len(node.keys) // 2
                mid_key = node.keys[mid]
                left = BTreeNode(node.leaf)
                right = BTreeNode(node.leaf)
                left.keys = node.keys[:mid]
                right.keys = node.keys[mid + 1:]
                if not node.leaf:
                    left.children = node.children[:mid + 1]
                    right.children = node.children[mid + 1:]
                    for c in left.children: c.parent = left
                    for c in right.children: c.parent = right
                new_root = BTreeNode(False)
                new_root.keys = [mid_key]
                new_root.children = [left, right]
                left.parent = new_root
                right.parent = new_root
                self.root = new_root
                yield Snapshot(self._deepcopy_root(), {left.uid: "orange", right.uid: "orange", new_root.uid: "plum"},
                               "new_root", f"根二分分裂，新根{new_root.keys}")
                break
            parent, idx = stack.pop()
            left_sib = parent.children[idx - 1] if idx > 0 else None
            right_sib = parent.children[idx + 1] if idx < len(parent.children) - 1 else None
            if left_sib and len(left_sib.keys) < self.max_keys:  # ← 修复：left_silt → left_sib
                sep_key = parent.keys[idx - 1]
                move_k = node.keys.pop(0)
                left_sib.keys.append(sep_key)
                parent.keys[idx - 1] = move_k
                if not node.leaf:
                    child = node.children.pop(0)
                    left_sib.children.append(child)
                    child.parent = left_sib
                yield Snapshot(self._deepcopy_root(), {left_sib.uid: "khaki", node.uid: "khaki"}, "redistribute",
                               f"左重分配，移键{move_k}")
                node = parent
                continue
            if right_sib and len(right_sib.keys) < self.max_keys:
                sep_key = parent.keys[idx]
                move_k = node.keys.pop()
                right_sib.keys.insert(0, sep_key)
                parent.keys[idx] = move_k
                if not node.leaf:
                    child = node.children.pop()
                    right_sib.children.insert(0, child)
                    child.parent = right_sib
                yield Snapshot(self._deepcopy_root(), {right_sib.uid: "khaki", node.uid: "khaki"}, "redistribute",
                               f"右重分配，移键{move_k}")
                node = parent
                continue
            split_res = None
            if left_sib:
                all_k = left_sib.keys + [parent.keys[idx - 1]] + node.keys
                all_c = left_sib.children + node.children if not node.leaf else []
                split_res = self._try_split_three(all_k)
                if split_res is not None:
                    lk, k1, mk, k2, rk = split_res
                    left_sib.keys = lk
                    mid_node = BTreeNode(node.leaf)
                    mid_node.keys = mk
                    node.keys = rk
                    if not node.leaf:
                        s1 = len(lk) + 1
                        s2 = s1 + len(mk) + 1
                        left_sib.children = all_c[:s1]
                        mid_node.children = all_c[s1:s2]
                        node.children = all_c[s2:]
                        for c in left_sib.children: c.parent = left_sib
                        for c in mid_node.children: c.parent = mid_node
                        for c in node.children: c.parent = node
                    parent.keys.pop(idx - 1)
                    parent.keys.insert(idx - 1, k2)
                    parent.keys.insert(idx - 1, k1)
                    parent.children.insert(idx, mid_node)
                    mid_node.parent = parent
                    yield Snapshot(self._deepcopy_root(),
                                   {left_sib.uid: "orange", mid_node.uid: "orange", node.uid: "orange"},
                                   "split_three", f"三分拆分：{lk} | {mk} | {rk}")
                    node = parent
                    continue
            if right_sib and split_res is None:
                all_k = node.keys + [parent.keys[idx]] + right_sib.keys
                all_c = node.children + right_sib.children if not node.leaf else []
                split_res = self._try_split_three(all_k)
                if split_res is not None:
                    lk, k1, mk, k2, rk = split_res
                    node.keys = lk
                    mid_node = BTreeNode(node.leaf)
                    mid_node.keys = mk
                    right_sib.keys = rk
                    if not node.leaf:
                        s1 = len(lk) + 1
                        s2 = s1 + len(mk) + 1
                        node.children = all_c[:s1]
                        mid_node.children = all_c[s1:s2]
                        right_sib.children = all_c[s2:]
                        for c in node.children: c.parent = node
                        for c in mid_node.children: c.parent = mid_node
                        for c in right_sib.children: c.parent = right_sib
                    parent.keys.pop(idx)
                    parent.keys.insert(idx, k2)
                    parent.keys.insert(idx, k1)
                    parent.children.insert(idx + 1, mid_node)
                    mid_node.parent = parent
                    yield Snapshot(self._deepcopy_root(),
                                   {node.uid: "orange", mid_node.uid: "orange", right_sib.uid: "orange"},
                                   "split_three", f"三分拆分：{lk} | {mk} | {rk}")
                    node = parent
                    continue
            mid = len(node.keys) // 2
            mid_key = node.keys[mid]
            right_node = BTreeNode(node.leaf)
            right_node.keys = node.keys[mid + 1:]
            node.keys = node.keys[:mid]
            if not node.leaf:
                right_node.children = node.children[mid + 1:]
                node.children = node.children[:mid + 1]
                for c in right_node.children: c.parent = right_node
            bisect.insort(parent.keys, mid_key)
            parent.children.insert(idx + 1, right_node)
            right_node.parent = parent
            yield Snapshot(self._deepcopy_root(), {node.uid: "orange", right_node.uid: "orange"}, "split_two",
                           f"二分分裂，上推键{mid_key}")
            node = parent

    def delete(self, key: int) -> Generator[Snapshot, None, None]:
        stack = []
        node = self.root
        while True:
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                break
            if node.leaf:
                yield Snapshot(self._deepcopy_root(), {}, "not_found", f"键{key}不存在")
                return
            stack.append((node, i))
            node = node.children[i]
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search", f"查找{key}进入{node.keys}")
        del_key = key
        if not node.leaf:
            pred = node.children[i]
            stack.append((node, i))
            while not pred.leaf:
                stack.append((pred, len(pred.keys)))
                pred = pred.children[-1]
            node.keys[i] = pred.keys[-1]
            del_key = pred.keys[-1]
            node = pred
        node.keys.remove(del_key)
        yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "delete", f"删除{del_key}，剩余{node.keys}")
        while node is not self.root and len(node.keys) < self.min_keys:
            yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "underflow", f"节点下溢{node.keys}")
            parent, idx = stack.pop()
            left_sib = parent.children[idx - 1] if idx > 0 else None
            right_sib = parent.children[idx + 1] if idx < len(parent.children) - 1 else None
            # 优先借位
            if left_sib and len(left_sib.keys) > self.min_keys:
                sep = parent.keys[idx - 1]
                borrow_k = left_sib.keys.pop()
                node.keys.insert(0, sep)
                parent.keys[idx - 1] = borrow_k
                if not node.leaf:
                    child = left_sib.children.pop()
                    node.children.insert(0, child)
                    child.parent = node
                yield Snapshot(self._deepcopy_root(), {left_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                               f"左借{borrow_k}")
                node = parent
                continue
            if right_sib and len(right_sib.keys) > self.min_keys:
                sep = parent.keys[idx]
                borrow_k = right_sib.keys.pop(0)
                node.keys.append(sep)
                parent.keys[idx] = borrow_k
                if not node.leaf:
                    child = right_sib.children.pop(0)
                    node.children.append(child)
                    child.parent = node
                yield Snapshot(self._deepcopy_root(), {right_sib.uid: "khaki", node.uid: "khaki"}, "borrow",
                               f"右借{borrow_k}")
                node = parent
                continue
            # 标准二节点合并（当前+单侧兄弟）
            if left_sib:
                merge_keys = left_sib.keys + [parent.keys.pop(idx - 1)] + node.keys
                merge_children = left_sib.children + node.children if not node.leaf else []
                left_sib.keys = merge_keys
                if not node.leaf:
                    left_sib.children = merge_children
                    for c in left_sib.children:
                        c.parent = left_sib
                parent.children.pop(idx)
                discard = node
            else:
                merge_keys = node.keys + [parent.keys.pop(idx)] + right_sib.keys
                merge_children = node.children + right_sib.children if not node.leaf else []
                node.keys = merge_keys
                if not node.leaf:
                    node.children = merge_children
                    for c in node.children:
                        c.parent = node
                parent.children.pop(idx + 1)
                discard = right_sib
            discard.keys.clear()
            discard.children.clear()
            discard.parent = None
            yield Snapshot(self._deepcopy_root(), {left_sib.uid if left_sib else node.uid: "lightgray"}, "merge",
                           f"节点合并，合并后键：{left_sib.keys if left_sib else node.keys}")
            # 合并后父节点减少一个键，继续向上检查下溢
            node = parent
        # 根节点收缩
        if not self.root.keys and len(self.root.children) == 1:
            self.root = self.root.children[0]
            self.root.parent = None
            self._full_reset_parent(self.root)
            yield Snapshot(self._deepcopy_root(), {self.root.uid: "plum"}, "new_root", "根收缩，全树父指针重置")

    def search(self, key: int) -> Generator[Snapshot, None, bool]:
        node = self.root
        while True:
            yield Snapshot(self._deepcopy_root(), {node.uid: "lightblue"}, "search", f"查找{key}，节点{node.keys}")
            i = bisect.bisect_left(node.keys, key)
            if i < len(node.keys) and node.keys[i] == key:
                yield Snapshot(self._deepcopy_root(), {node.uid: "lightgreen"}, "found", f"✅ 找到{key}")
                return True
            if node.leaf:
                yield Snapshot(self._deepcopy_root(), {node.uid: "salmon"}, "not_found", f"❌ 未找到{key}")
                return False
            node = node.children[i]

    def check_properties(self) -> Tuple[bool, str]:
        def get_sub_max(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[-1]
            return n.keys[-1] if n.keys else -float("inf")

        def get_sub_min(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[0]
            return n.keys[0] if n.keys else float("inf")

        def dfs(node: BTreeNode, depth: int, leaf_dep: List[Optional[int]]):
            if len(node.keys) > self.max_keys:
                return False, f"键数{len(node.keys)}超上限{self.max_keys}"
            if node is not self.root and len(node.keys) < self.min_keys:
                return False, f"键数{len(node.keys)}低于下限{self.min_keys}"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i - 1]:
                    return False, "节点键无序"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    return False, f"子节点{len(node.children)} != 键+1 {len(node.keys) + 1}"
                for idx, sep in enumerate(node.keys):
                    lm = get_sub_max(node.children[idx])
                    rm = get_sub_min(node.children[idx + 1])
                    if lm >= sep or rm <= sep:
                        return False, f"分隔键{sep}区间非法"
                for child in node.children:
                    ok, msg = dfs(child, depth + 1, leaf_dep)
                    if not ok:
                        return False, msg
            else:
                if leaf_dep[0] is None:
                    leaf_dep[0] = depth
                elif depth != leaf_dep[0]:
                    return False, "叶子层级不一致"
                return True, ""  # ← 新增
            return True, ""  # ← 新增

        if not self.root.keys:
            if len(self.root.children) == 1:
                return True, "空根单节点合规"
            else:
                return False, "空根子节点数量非法"
        leaf_dep = [None]
        return dfs(self.root, 0, leaf_dep)

    def check_properties_animated(self) -> Generator[Snapshot, None, Tuple[bool, str]]:
        highlights = {}
        def get_sub_max(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[-1]
            return n.keys[-1] if n.keys else -float("inf")
        def get_sub_min(n: BTreeNode) -> int:
            while not n.leaf:
                n = n.children[0]
            return n.keys[0] if n.keys else float("inf")
        def dfs_anim(node: BTreeNode, depth: int, leaf_dep: List[Optional[int]]):
            highlights[node.uid] = "lightblue"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check", f"校验B*节点 {node.keys}")
            if len(node.keys) > self.max_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", f"❌ 键数超上限{self.max_keys}")
                return False, "键超限"
            if node is not self.root and len(node.keys) < self.min_keys:
                highlights[node.uid] = "salmon"
                yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", f"❌ 键数低于下限{self.min_keys}")
                return False, "键不足"
            for i in range(1, len(node.keys)):
                if node.keys[i] <= node.keys[i-1]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ 键无序")
                    return False, "内部无序"
            if not node.leaf:
                if len(node.children) != len(node.keys) + 1:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", f"❌ 子节点{len(node.children)} != 键+1 {len(node.keys)+1}")
                    return False, "子节点数量不匹配"
                for idx, sep in enumerate(node.keys):
                    lm = get_sub_max(node.children[idx])
                    rm = get_sub_min(node.children[idx+1])
                    if lm >= sep or rm <= sep:
                        highlights[node.uid] = "salmon"
                        yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", f"❌ 分隔键{sep}区间错误")
                        return False, "分隔键非法"
                for child in node.children:
                    ok, msg = yield from dfs_anim(child, depth+1, leaf_dep)
                    if not ok:
                        return False, msg
            else:
                if leaf_dep[0] is None:
                    leaf_dep[0] = depth
                elif depth != leaf_dep[0]:
                    highlights[node.uid] = "salmon"
                    yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_fail", "❌ 叶子层级不同")
                    return False, "叶子深度不一致"
            highlights[node.uid] = "lightgreen"
            yield Snapshot(self._deepcopy_root(), highlights.copy(), "check_pass", f"✅ B*节点{node.keys}合法")
            return True, ""
        if not self.root.keys:
            if len(self.root.children) == 1:
                yield Snapshot(self._deepcopy_root(), {}, "check_done", "✅ 空根单节点合法")
                return True, "合规"
            else:
                yield Snapshot(self._deepcopy_root(), {}, "check_fail", "❌ 空根子节点数量非法")
                return False, "非法"
        leaf_dep = [None]
        ok, msg = yield from dfs_anim(self.root, 0, leaf_dep)
        if ok:
            yield Snapshot(self._deepcopy_root(), highlights, "check_done", "✅ 整棵B*树全部符合规范")
        return ok, msg

# ===================== 3. 画布渲染布局常量与工具函数 =====================
NODE_HEIGHT = 40
KEY_WIDTH = 30
NODE_PADDING = 10
LEVEL_GAP = 100
SIBLING_GAP = 45

def get_subtree_width(node: BTreeNode) -> int:
    if not node:
        return 0
    if node.leaf or len(node.children) == 0:
        return max(80, len(node.keys) * KEY_WIDTH + NODE_PADDING * 2)
    child_ws = [get_subtree_width(c) for c in node.children]
    total_child = sum(child_ws) + (len(child_ws) - 1) * SIBLING_GAP
    return total_child

def compute_positions(node: BTreeNode, depth: int = 0, x_offset: int = 0) -> Dict[int, Tuple[int, int]]:
    pos_map = {}
    if not node:
        return pos_map
    child_ws = [get_subtree_width(c) for c in node.children]
    total_child_w = sum(child_ws) + (len(child_ws) - 1) * SIBLING_GAP if child_ws else 0
    node_w = max(80, len(node.keys) * KEY_WIDTH + NODE_PADDING * 2)
    center_x = x_offset + (total_child_w / 2 if total_child_w > 0 else node_w / 2)
    center_y = depth * LEVEL_GAP + 60
    pos_map[node.uid] = (int(center_x), int(center_y))
    cur_x = x_offset
    for idx, child in enumerate(node.children):
        pos_map.update(compute_positions(child, depth + 1, cur_x))
        cur_x += child_ws[idx] + SIBLING_GAP
    return pos_map

def _find_node_by_uid(root: BTreeNode, target_uid: int) -> Optional[BTreeNode]:
    if root.uid == target_uid:
        return root
    for c in root.children:
        res = _find_node_by_uid(c, target_uid)
        if res:
            return res
    return None

def draw_tree(canvas: tk.Canvas, root: BTreeNode, highlights: Dict[int, str], tree_type: str):
    canvas.delete("all")
    pos = compute_positions(root)

    # 递归绘制索引节点到子节点的实线连接线
    def draw_edge(n: BTreeNode):
        if len(n.children) == 0:
            return
        x1, y1 = pos[n.uid]
        for child in n.children:
            x2, y2 = pos[child.uid]
            canvas.create_line(
                x1, y1 + NODE_HEIGHT // 2,
                x2, y2 - NODE_HEIGHT // 2,
                fill="#333", width=2
            )
            draw_edge(child)

    draw_edge(root)

    # B+ 树专属：绘制叶子双向链表虚线箭头
    if tree_type == "B+ Tree":
        # 找到最左叶子起点
        temp = root
        while not temp.leaf:
            temp = temp.children[0]
        cur_leaf = temp
        # 沿着next链表完整遍历所有叶子
        while cur_leaf is not None:
            nxt = cur_leaf.next
            if nxt is None:
                cur_leaf = nxt
                continue
            # 过滤快照中丢失坐标的节点
            if cur_leaf.uid not in pos or nxt.uid not in pos:
                cur_leaf = nxt
                continue
            x1, y1 = pos[cur_leaf.uid]
            x2, y2 = pos[nxt.uid]
            # 动态计算节点宽度
            w1 = max(80, len(cur_leaf.keys) * KEY_WIDTH + NODE_PADDING * 2)
            w2 = max(80, len(nxt.keys) * KEY_WIDTH + NODE_PADDING * 2)
            # 箭头起点：当前叶子最右侧
            start_x = x1 + w1 / 2
            # 箭头终点：下一个叶子最左侧
            end_x = x2 - w2 / 2
            canvas.create_line(
                start_x, y1, end_x, y2,
                fill="#2c3e50", dash=(4, 3), width=2, arrow=tk.LAST
            )
            cur_leaf = nxt

    # 遍历所有节点，绘制矩形、分隔竖线与键文字
    for uid, (x, y) in pos.items():
        node = _find_node_by_uid(root, uid)
        if not node:
            continue
        fill_color = highlights.get(uid, "white")
        node_w = max(80, len(node.keys) * KEY_WIDTH + NODE_PADDING * 2)
        half_h = NODE_HEIGHT // 2
        x0 = x - node_w // 2
        y0 = y - half_h
        x1 = x + node_w // 2
        y1 = y + half_h
        canvas.create_rectangle(
            x0, y0, x1, y1,
            fill=fill_color, outline="#2c3e50", width=2
        )
        key_cnt = len(node.keys)
        if key_cnt == 0:
            continue
        cell_w = node_w / key_cnt
        for i, k in enumerate(node.keys):
            cx = x0 + cell_w * i + cell_w / 2
            if i > 0:
                split_x = x0 + cell_w * i
                canvas.create_line(split_x, y0, split_x, y1, fill="#2c3e50", width=1)
            canvas.create_text(
                cx, y, text=str(k),
                font=("Microsoft YaHei", 11, "bold"), fill="#2c3e50"
            )

# ===================== 4. 动画引擎类 =====================
class AnimEngine:
    def __init__(self, canvas: tk.Canvas, log_widget: scrolledtext.ScrolledText):
        self.canvas = canvas
        self.log = log_widget
        self.tree: Optional[BaseBTree] = None
        self.generator: Optional[Generator[Snapshot, None, None]] = None
        self.history: List[Snapshot] = []
        self.current_idx = -1
        self.playing = False
        self.speed = 800
        self.tree_type = "B-Tree"

    def set_tree(self, tree: BaseBTree, tree_type: str):
        self.tree = tree
        self.tree_type = tree_type
        self.history.clear()
        self.current_idx = -1
        self.generator = None
        self.playing = False
        self._render()

    def start_op(self, gen: Generator[Snapshot, None, None]):
        self.generator = gen
        self.history = self.history[:self.current_idx + 1]
        self.current_idx = len(self.history) - 1
        self.playing = False
        self.step_forward()

    def step_forward(self):
        if self.current_idx < len(self.history) - 1:
            self.current_idx += 1
            self._render()
            self._log(self.history[self.current_idx].message)
            if self.playing:
                self.canvas.after(self.speed, self.step_forward)
            return
        if self.generator is None:
            return
        try:
            snap = next(self.generator)
            self.history.append(snap)
            self.current_idx += 1
            self._render()
            self._log(snap.message)
            if self.playing:
                self.canvas.after(self.speed, self.step_forward)
        except StopIteration:
            self.playing = False
            self._log("--- 操作完成 ---")

    def step_backward(self):
        if self.current_idx > 0:
            self.current_idx -= 1
            self._render()
            self._log(self.history[self.current_idx].message)

    def play_pause(self):
        if self.playing:
            self.playing = False
        else:
            self.playing = True
            self.step_forward()

    def reset(self):
        self.playing = False
        self.generator = None
        self.history.clear()
        self.current_idx = -1
        self._render()
        self.log.delete(1.0, tk.END)

    def set_speed(self, ms: int):
        self.speed = ms

    def _render(self):
        if self.tree is None:
            self.canvas.delete(tk.ALL)
            return
        if self.current_idx < 0 or len(self.history) == 0:
            draw_tree(self.canvas, self.tree.root, {}, self.tree_type)
        else:
            snap = self.history[self.current_idx]
            draw_tree(self.canvas, snap.root, snap.highlights, self.tree_type)

    def _log(self, msg: str):
        self.log.insert(tk.END, msg + "\n")
        self.log.see(tk.END)

# ===================== 5. 主窗口UI完整类 =====================
class BTreeVisualizer:
    def __init__(self, root_win: tk.Tk):
        self.root = root_win
        self.root.title("B-、B+和B*树可视化工具")
        self.root.geometry("1280x850")
        self.root.minsize(1100, 680)
        # 绑定变量
        self.order_var = tk.IntVar(value=3)
        self.tree_type_var = tk.StringVar(value="B-Tree")
        self.key_var = tk.StringVar()
        self.range_low_var = tk.StringVar()
        self.range_high_var = tk.StringVar()
        self.speed_var = tk.IntVar(value=800)
        self.traversal_var = tk.StringVar(value="中序")
        self.perf_cnt_var = tk.IntVar(value=1000)
        self.perf_thread = None  # 后台线程句柄
        self.plot_lock = threading.Lock()  # 绘图线程锁

        # 顶部操作栏
        top_frame = tk.Frame(self.root, bg="#f0f0f0", padx=10, pady=8)
        top_frame.pack(side=tk.TOP, fill=tk.X)

        # 多页签容器
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        # ========== Tab1：树可视化页面 ==========
        tab_visual = ttk.Frame(self.notebook)
        self.notebook.add(tab_visual, text="树可视化")
        main_frame = tk.Frame(tab_visual)
        main_frame.pack(fill=tk.BOTH, expand=True)

        left_panel = tk.Frame(main_frame, width=270, bg="#f0f0f0", padx=12, pady=12)
        left_panel.pack(side=tk.LEFT, fill=tk.Y)
        left_panel.pack_propagate(False)

        self.canvas = tk.Canvas(main_frame, bg="white", highlightthickness=0)
        self.canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # ========== Tab2：性能对比页面 ==========
        tab_perf = ttk.Frame(self.notebook)
        self.notebook.add(tab_perf, text="性能对比")
        self._build_perf_tab(tab_perf)

        # 底部日志框
        log_frame = tk.Frame(self.root, height=130, bg="#f0f0f0", padx=10, pady=5)
        log_frame.pack(side=tk.BOTTOM, fill=tk.X)
        log_frame.pack_propagate(False)
        self.log_box = scrolledtext.ScrolledText(log_frame, font=("Microsoft YaHei", 9))
        self.log_box.pack(fill=tk.BOTH, expand=True)

        self.anim = AnimEngine(self.canvas, self.log_box)
        self._rebuild_tree()
        self._build_top_bar(top_frame)
        self._build_left_panel(left_panel)

    # ---------- 性能对比Tab构建 ----------
    def _build_perf_tab(self, parent):
        # 控制行
        ctrl_frame = ttk.Frame(parent)
        ctrl_frame.pack(fill=tk.X, padx=10, pady=8)
        ttk.Label(ctrl_frame, text="单棵树测试数据量:").pack(side=tk.LEFT)
        ttk.Entry(ctrl_frame, textvariable=self.perf_cnt_var, width=8).pack(side=tk.LEFT, padx=6)
        ttk.Button(ctrl_frame, text="一键批量测试(m=3~10)", command=self._run_perf_test).pack(side=tk.LEFT, padx=10)
        # 进度提示
        self.perf_status = ttk.Label(ctrl_frame, text="就绪", foreground="gray")
        self.perf_status.pack(side=tk.LEFT, padx=10)

        # matplotlib画布初始化
        self.perf_fig, self.perf_axes = plt.subplots(2, 2, figsize=(14, 9))
        self.perf_mpl_canvas = FigureCanvasTkAgg(self.perf_fig, master=parent)
        self.perf_mpl_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

    # ---------- 树统计工具函数 ----------
    def _count_node(self, node: BTreeNode) -> int:
        if not node:
            return 0
        total = 1
        for child in node.children:
            total += self._count_node(child)
        return total

    def _get_tree_height(self, node: BTreeNode) -> int:
        if node.leaf:
            return 1
        max_h = 0
        for child in node.children:
            max_h = max(max_h, self._get_tree_height(child))
        return max_h + 1

    # ---------- 批量性能测试入口 ----------
    def _run_perf_test(self):
        if self.perf_thread and self.perf_thread.is_alive():
            self.anim._log("测试正在进行中，请等待...")
            return
        test_num = self.perf_cnt_var.get()
        m_range = list(range(3, 11))
        self.perf_status.config(text="测试中...", foreground="blue")
        self.anim._log(f"开始批量性能测试，数据量={test_num}...")

        def worker():
            btree_res, bplus_res, bstar_res = [], [], []
            for m in m_range:
                test_keys = random.sample(range(1, 9999), test_num)

                # ---------- B-Tree ----------
                t_b = BTree(m)
                t_b._disable_deepcopy = True  # 禁用深拷贝
                split_cnt, cmp_cnt = 0, 0
                for k in test_keys:
                    gen = t_b.insert(k)
                    for snap in gen:  # 消耗生成器，同时统计
                        cmp_cnt += 1
                        if snap.phase == "overflow":
                            split_cnt += 1
                total_k = t_b.count_keys()
                total_n = self._count_node(t_b.root)
                fill_rate = total_k / (total_n * (m - 1)) if total_n > 0 else 0
                h = self._get_tree_height(t_b.root)
                btree_res.append(PerfResult(height=h, split_cnt=split_cnt, fill_rate=fill_rate, cmp_times=cmp_cnt))

                # ---------- B+ Tree ----------
                t_bp = BPlusTree(m)
                t_bp._disable_deepcopy = True
                split_cnt, cmp_cnt = 0, 0
                for k in test_keys:
                    gen = t_bp.insert(k)
                    for snap in gen:
                        cmp_cnt += 1
                        if snap.phase == "overflow":
                            split_cnt += 1
                total_k = t_bp.count_keys()
                total_n = self._count_node(t_bp.root)
                fill_rate = total_k / (total_n * (m - 1)) if total_n > 0 else 0
                h = self._get_tree_height(t_bp.root)
                bplus_res.append(PerfResult(height=h, split_cnt=split_cnt, fill_rate=fill_rate, cmp_times=cmp_cnt))

                # ---------- B* Tree ----------
                t_bs = BStarTree(m)
                t_bs._disable_deepcopy = True
                split_cnt, cmp_cnt = 0, 0
                for k in test_keys:
                    gen = t_bs.insert(k)
                    for snap in gen:
                        cmp_cnt += 1
                        if snap.phase in ("overflow", "split_two", "split_three"):
                            split_cnt += 1
                total_k = t_bs.count_keys()
                total_n = self._count_node(t_bs.root)
                fill_rate = total_k / (total_n * (m - 1)) if total_n > 0 else 0
                h = self._get_tree_height(t_bs.root)
                bstar_res.append(PerfResult(height=h, split_cnt=split_cnt, fill_rate=fill_rate, cmp_times=cmp_cnt))

            # 主线程更新图表
            def draw_safe():
                with self.plot_lock:
                    self._draw_perf_chart(m_range, btree_res, bplus_res, bstar_res)

            self.root.after(0, draw_safe)
            self.root.after(0, lambda: self.perf_status.config(text="完成", foreground="green"))
            self.root.after(0, lambda: self.anim._log("性能测试完成"))

        self.perf_thread = threading.Thread(target=worker, daemon=True)
        self.perf_thread.start()

    # ---------- Matplotlib绘图函数 ----------
    def _draw_perf_chart(self, m_list, b_res, bp_res, bs_res):
        self.perf_fig.clear()
        self.perf_axes = self.perf_fig.subplots(nrows=2, ncols=2)  # 移除 figsize
        ax1, ax2 = self.perf_axes[0]
        ax3, ax4 = self.perf_axes[1]

        w = 0.22
        x_idx = list(range(len(m_list)))

        # 图1：树高对比
        bh = [item.height for item in b_res]
        bph = [item.height for item in bp_res]
        bsh = [item.height for item in bs_res]
        ax1.plot(m_list, bh, marker="o", color="#2196F3", label="B-Tree")
        ax1.plot(m_list, bph, marker="s", color="#FF9800", label="B+ Tree")
        ax1.plot(m_list, bsh, marker="^", color="#4CAF50", label="B* Tree")
        ax1.set_title("阶数 m - 树高对比", fontsize=13, fontweight="bold", pad=10)
        ax1.set_xlabel("阶 m", fontsize=10)
        ax1.set_ylabel("树高度", fontsize=10)
        ax1.legend(fontsize=9)
        ax1.grid(alpha=0.3)

        # 图2：分裂次数柱状图
        bs = [item.split_cnt for item in b_res]
        bps = [item.split_cnt for item in bp_res]
        bss = [item.split_cnt for item in bs_res]
        ax2.bar([i - w for i in x_idx], bs, width=w, color="#2196F3", label="B-Tree")
        ax2.bar(x_idx, bps, width=w, color="#FF9800", label="B+ Tree")
        ax2.bar([i + w for i in x_idx], bss, width=w, color="#4CAF50", label="B* Tree")
        ax2.set_xticks(x_idx)
        ax2.set_xticklabels(m_list)
        ax2.set_title("各阶总分裂次数", fontsize=13, fontweight="bold", pad=10)
        ax2.set_xlabel("阶 m", fontsize=10)
        ax2.set_ylabel("分裂次数", fontsize=10)
        ax2.legend(fontsize=9)

        # 图3：填充率折线
        bf = [item.fill_rate for item in b_res]
        bpf = [item.fill_rate for item in bp_res]
        bsf = [item.fill_rate for item in bs_res]
        ax3.plot(m_list, bf, marker="o", color="#2196F3", label="B-Tree")
        ax3.plot(m_list, bpf, marker="s", color="#FF9800", label="B+ Tree")
        ax3.plot(m_list, bsf, marker="^", color="#4CAF50", label="B* Tree")
        ax3.set_title("节点平均填充率", fontsize=13, fontweight="bold", pad=10)
        ax3.set_xlabel("阶 m", fontsize=10)
        ax3.set_ylabel("填充率(总键/总容量)", fontsize=10)
        ax3.legend(fontsize=9)
        ax3.grid(alpha=0.3)

        # 图4：比较次数柱状图
        bc = [item.cmp_times for item in b_res]
        bpc = [item.cmp_times for item in bp_res]
        bsc = [item.cmp_times for item in bs_res]
        ax4.bar([i - w for i in x_idx], bc, width=w, color="#2196F3", label="B-Tree")
        ax4.bar(x_idx, bpc, width=w, color="#FF9800", label="B+ Tree")
        ax4.bar([i + w for i in x_idx], bsc, width=w, color="#4CAF50", label="B* Tree")
        ax4.set_xticks(x_idx)
        ax4.set_xticklabels(m_list)
        ax4.set_title("插入总键比较次数", fontsize=13, fontweight="bold", pad=10)
        ax4.set_xlabel("阶 m", fontsize=10)
        ax4.set_ylabel("比较次数", fontsize=10)
        ax4.legend(fontsize=9)

        self.perf_fig.subplots_adjust(top=0.95)
        self.perf_fig.tight_layout()
        self.perf_mpl_canvas.draw()

    # ---------- 树实例重建 ----------
    def _rebuild_tree(self):
        m = self.order_var.get()
        t_type = self.tree_type_var.get()
        if t_type == "B-Tree":
            tree = BTree(m)
        elif t_type == "B+ Tree":
            tree = BPlusTree(m)
        else:
            tree = BStarTree(m)
        self.anim.set_tree(tree, t_type)
        self.anim._log(f"已创建 {t_type}，阶数 m={m}")

    # ---------- 顶部操作栏UI构建 ----------
    def _build_top_bar(self, frame: tk.Frame):
        # 第一行：增删改查
        row1 = tk.Frame(frame, bg="#f0f0f0")
        row1.pack(fill=tk.X, pady=2)
        tk.Label(row1, text="键值：", bg="#f0f0f0", font=("Microsoft YaHei", 10)).pack(side=tk.LEFT, padx=4)
        tk.Entry(row1, textvariable=self.key_var, width=10).pack(side=tk.LEFT, padx=4)
        tk.Button(row1, text="插入", width=7, command=self._on_insert).pack(side=tk.LEFT, padx=2)
        tk.Button(row1, text="删除", width=7, command=self._on_delete).pack(side=tk.LEFT, padx=2)
        tk.Button(row1, text="查找", width=7, command=self._on_search).pack(side=tk.LEFT, padx=2)
        tk.Button(row1, text="更新", width=7, command=self._on_update).pack(side=tk.LEFT, padx=2)

        # 第二行：最值、前驱后继
        row2 = tk.Frame(frame, bg="#f0f0f0")
        row2.pack(fill=tk.X, pady=2)
        tk.Button(row2, text="最小值", width=9, command=self._min).pack(side=tk.LEFT, padx=2)
        tk.Button(row2, text="最大值", width=9, command=self._max).pack(side=tk.LEFT, padx=2)
        tk.Button(row2, text="查找前驱", width=9, command=self._pred).pack(side=tk.LEFT, padx=2)
        tk.Button(row2, text="查找后继", width=9, command=self._succ).pack(side=tk.LEFT, padx=2)

        # 第三行：区间查询、统计
        row3 = tk.Frame(frame, bg="#f0f0f0")
        row3.pack(fill=tk.X, pady=2)
        tk.Label(row3, text="区间：", bg="#f0f0f0").pack(side=tk.LEFT, padx=4)
        tk.Entry(row3, textvariable=self.range_low_var, width=7).pack(side=tk.LEFT)
        tk.Label(row3, text="~", bg="#f0f0f0").pack(side=tk.LEFT, padx=2)
        tk.Entry(row3, textvariable=self.range_high_var, width=7).pack(side=tk.LEFT)
        tk.Button(row3, text="区间查询", width=9, command=self._range).pack(side=tk.LEFT, padx=4)
        tk.Button(row3, text="统计总数", width=9, command=self._count_anim).pack(side=tk.LEFT, padx=2)

        # 第四行：校验、清空、演示、随机
        row4 = tk.Frame(frame, bg="#f0f0f0")
        row4.pack(fill=tk.X, pady=2)
        tk.Button(row4, text="检查树合法", width=11, command=self._check_anim).pack(side=tk.LEFT, padx=2)
        tk.Button(row4, text="清空树", width=9, command=self._clear).pack(side=tk.LEFT, padx=2)
        tk.Button(row4, text="演示序列", width=9, command=self._demo).pack(side=tk.LEFT, padx=2)
        tk.Button(row4, text="随机10个", width=11, command=self._random).pack(side=tk.LEFT, padx=2)

        # 第五行：使用帮助、C++源码按钮
        row5 = tk.Frame(frame, bg="#f0f0f0")
        row5.pack(fill=tk.X, pady=2)
        tk.Button(row5, text="使用帮助", width=9, command=self._usehelp).pack(side=tk.LEFT, padx=2)
        tk.Button(row5, text="B-树C++源代码", width=15, command=self._btree).pack(side=tk.LEFT, padx=2)
        tk.Button(row5, text="B+树C++源代码", width=15, command=self._bplustree).pack(side=tk.LEFT, padx=2)
        tk.Button(row5, text="B*树C++源代码", width=15, command=self._bstartree).pack(side=tk.LEFT, padx=2)

    # ---------- 左侧参数面板UI构建 ----------
    def _build_left_panel(self, frame: tk.Frame):
        tk.Label(frame, text="参数设置", font=("Microsoft YaHei", 12, "bold"), bg="#f0f0f0").pack(anchor="w", pady=(0, 8))
        # 阶数滑块
        tk.Label(frame, text="阶数 m", bg="#f0f0f0", anchor="w").pack(fill=tk.X)
        tk.Scale(frame, from_=3, to=10, orient=tk.HORIZONTAL, variable=self.order_var, command=self._on_order).pack(fill=tk.X, pady=(0, 10))
        # 树类型单选
        tk.Label(frame, text="树类型", bg="#f0f0f0", anchor="w").pack(fill=tk.X)
        tk.Radiobutton(frame, text="B-Tree", variable=self.tree_type_var, value="B-Tree", bg="#f0f0f0", command=self._on_tree).pack(anchor="w")
        tk.Radiobutton(frame, text="B+ Tree", variable=self.tree_type_var, value="B+ Tree", bg="#f0f0f0", command=self._on_tree).pack(anchor="w")
        tk.Radiobutton(frame, text="B* Tree", variable=self.tree_type_var, value="B* Tree", bg="#f0f0f0", command=self._on_tree).pack(anchor="w")

        tk.Frame(frame, height=15, bg="#f0f0f0").pack()
        tk.Label(frame, text="动画控制", font=("Microsoft YaHei", 10, "bold"), bg="#f0f0f0").pack(anchor="w")
        btn_line = tk.Frame(frame, bg="#f0f0f0")
        btn_line.pack(fill=tk.X)
        tk.Button(btn_line, text="重置", command=self._anim_reset).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        tk.Button(btn_line, text="上一步", command=self._prev).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        tk.Button(btn_line, text="播放", command=self._play).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        tk.Button(btn_line, text="下一步", command=self._next).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)

        tk.Label(frame, text="动画速度(ms)", bg="#f0f0f0", anchor="w").pack(fill=tk.X, pady=10)
        tk.Scale(frame, from_=200, to=2000, resolution=100, orient=tk.HORIZONTAL, variable=self.speed_var, command=self._speed).pack(fill=tk.X)
        tk.Label(frame, text="数值越小越快", bg="#f0f0f0", font=("Microsoft YaHei", 8), fg="#555").pack(anchor="w")

        tk.Frame(frame, height=15, bg="#f0f0f0").pack()
        tk.Label(frame, text="遍历方式", font=("Microsoft YaHei", 10, "bold"), bg="#f0f0f0").pack(anchor="w")
        trav_line = tk.Frame(frame, bg="#f0f0f0")
        trav_line.pack(fill=tk.X)
        for m in ["前序", "中序", "后序", "层序"]:
            tk.Radiobutton(trav_line, text=m, variable=self.traversal_var, value=m, bg="#f0f0f0", command=self._traverse_anim).pack(side=tk.LEFT, expand=True)

    # ---------- 输入工具方法 ----------
    def _get_key(self) -> int | None:
        txt = self.key_var.get().strip()
        try:
            return int(txt)
        except ValueError:
            self.anim._log("错误：请输入合法整数键值")
            return None

    # ---------- 按钮绑定事件 ----------
    def _on_insert(self):
        k = self._get_key()
        if k is None:
            return
        gen = self.anim.tree.insert(k)
        self.anim.start_op(gen)

    def _on_delete(self):
        k = self._get_key()
        if k is None:
            return
        gen = self.anim.tree.delete(k)
        self.anim.start_op(gen)

    def _on_search(self):
        k = self._get_key()
        if k is None:
            return
        gen = self.anim.tree.search(k)
        self.anim.start_op(gen)

    def _on_update(self):
        old = self._get_key()
        if old is None:
            return
        new = simpledialog.askinteger("更新键", f"替换键 {old} 的新数字：", parent=self.root)
        if new is None:
            return
        def update_gen():
            yield from self.anim.tree.delete(old)
            yield from self.anim.tree.insert(new)
        self.anim.start_op(update_gen())

    def _pred(self):
        k = self._get_key()
        if k is None:
            return
        self.anim.start_op(self.anim.tree.get_predecessor(k))

    def _succ(self):
        k = self._get_key()
        if k is None:
            return
        self.anim.start_op(self.anim.tree.get_successor(k))

    def _min(self):
        self.anim.start_op(self.anim.tree.get_min())

    def _max(self):
        self.anim.start_op(self.anim.tree.get_max())

    def _range(self):
        try:
            l = int(self.range_low_var.get())
            h = int(self.range_high_var.get())
        except ValueError:
            self.anim._log("错误：区间上下限必须为整数")
            return
        self.anim.start_op(self.anim.tree.range_query(l, h))

    def _count_anim(self):
        gen = self.anim.tree.count_keys_animated()
        self.anim.start_op(gen)

    def _check_anim(self):
        gen = self.anim.tree.check_properties_animated()
        self.anim.start_op(gen)

    def _clear(self):
        self.anim.tree.clear()
        self._rebuild_tree()

    def _demo(self):
        seq = [10, 20, 30, 40, 50, 25, 35, 5, 60, 70]
        self.anim._log(f"演示插入序列：{seq}")
        def demo_gen():
            for num in seq:
                yield from self.anim.tree.insert(num)
        self.anim.start_op(demo_gen())

    def _random(self):
        nums = random.sample(range(1, 100), 10)
        self.anim._log(f"随机插入10个数字：{nums}")
        def rand_gen():
            for n in nums:
                yield from self.anim.tree.insert(n)
        self.anim.start_op(rand_gen())

    def _traverse_anim(self):
        mode = self.traversal_var.get()
        gen = self.anim.tree.traversal_animated(mode)
        self.anim.start_op(gen)

    # ---------- 参数滑块回调 ----------
    def _on_order(self, v):
        self._rebuild_tree()

    def _on_tree(self):
        self._rebuild_tree()

    def _speed(self, v):
        self.anim.set_speed(int(v))

    # ---------- 动画控制按钮 ----------
    def _anim_reset(self):
        self.anim.reset()

    def _prev(self):
        self.anim.step_backward()

    def _next(self):
        self.anim.step_forward()

    def _play(self):
        self.anim.play_pause()

    # ---------- 源码/帮助弹窗 ----------
    def _usehelp(self):
        try:
            file_path = get_resource_path("usehelp.txt")
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            win = tk.Toplevel(self.root)
            win.title("使用帮助")
            win.geometry("900x600")
            st = scrolledtext.ScrolledText(win, font=("Consolas", 10))
            st.pack(fill=tk.BOTH, expand=True)
            st.insert(tk.END, content)
            st.config(state=tk.DISABLED)
        except FileNotFoundError:
            messagebox.showerror("错误", "未找到 usehelp.txt 文件")

    def _btree(self):
        try:
            file_path = get_resource_path("btree.cpp")
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            win = tk.Toplevel(self.root)
            win.title("B-Tree C++ 源代码")
            win.geometry("1100x700")
            st = scrolledtext.ScrolledText(win, font=("Consolas", 10))
            st.pack(fill=tk.BOTH, expand=True)
            st.insert(tk.END, content)
            st.config(state=tk.DISABLED)
        except FileNotFoundError:
            messagebox.showerror("错误", "未找到 btree.cpp 文件")

    def _bplustree(self):
        try:
            file_path = get_resource_path("bplustree.cpp")
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            win = tk.Toplevel(self.root)
            win.title("B+ Tree C++ 源代码")
            win.geometry("1100x700")
            st = scrolledtext.ScrolledText(win, font=("Consolas", 10))
            st.pack(fill=tk.BOTH, expand=True)
            st.insert(tk.END, content)
            st.config(state=tk.DISABLED)
        except FileNotFoundError:
            messagebox.showerror("错误", "未找到 bplustree.cpp 文件")

    def _bstartree(self):
        try:
            file_path = get_resource_path("bstartree.cpp")
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
            win = tk.Toplevel(self.root)
            win.title("B* Tree C++ 源代码")
            win.geometry("1100x700")
            st = scrolledtext.ScrolledText(win, font=("Consolas", 10))
            st.pack(fill=tk.BOTH, expand=True)
            st.insert(tk.END, content)
            st.config(state=tk.DISABLED)
        except FileNotFoundError:
            messagebox.showerror("错误", "未找到 bstartree.cpp 文件")


# 程序入口启动函数
def main():
    root = tk.Tk()
    app = BTreeVisualizer(root)
    root.mainloop()

if __name__ == "__main__":
    main()
