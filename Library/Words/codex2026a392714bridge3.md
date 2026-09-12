---
bibkey: codex2026a392714bridge3
authors: Codex implementation worker
year: 2026
title: A392714 Phi and residual words — obstruction to a direct bijection
doi: null
url: https://arxiv.org/html/2605.11137v1
claim: Exact enumeration at n=2 gives three Phi permutations but only one legal residual pair, excluding the proposed direct bijection.
strata_touched:
  - D5/S1/Words/Compositions/PhiTailEncoding
  - D5/S1/Words/Compositions/AlternatingResidualBridge
license: citation-only
triage: anchor
---

# A392714 Φ 与剩余类的直接双射障碍

## Verified locator

The external conjecture is stated in arXiv:2605.11137v1, Remark 4:
https://arxiv.org/html/2605.11137v1
The repository definitions are
`D5/S1/Words/Compositions/PhiTailEncoding.lean`, specifically
`suffixBudget`, `admissible`, `phi`, and `tailWord`.
The residual encoding and predicates are in
`D5/S1/Words/Compositions/AlternatingResidualBridge.lean`, specifically
`alternating`, `encode`, `Good`, and `Unswappable`.
The finite calculation below concerns these definitions; it is not a statement
attributed to the external paper or a new kernel-verified theorem.

## 直接双射不成立

取 n=2、m=1。全部固定首项的六个零基排列中，恰有下列三个属于 Φ(2)。
预算列按 k=1,2,3 排列；符号由逆序数计算。

| p | 后缀预算 | tailWord | signInt p |
| --- | --- | --- | --- |
| (0,1,2,3) | (1,1,0) | (1,0,−1) | +1 |
| (0,1,3,2) | (0,1,0) | (0,1,−1) | −1 |
| (0,2,1,3) | (1,0,0) | (1,−1,0) | −1 |

Fin 1 上只有恒等排列，故唯一的 (a,b) 为 (id,id)。冻结定义给出
encode a b = [1,−1,0]，满足 Good 0 与 Unswappable 0。
因此两侧基数为 3 与 1，任何双射都不成立，改变尾词等式的写法也不能修复。

具体失效的正向命题是：
对每个 p∈phi 2，存在 a,b : Perm(Fin 1)，使 tailWord 2 p = encode a b。
恒等排列已经反驳它：尾词末位是 −1，不是 0。
同一尾词满足 Good 0，却不满足 Unswappable 0，因为首块 (1,0)
在高度 0 处两种次序均合法。这也反驳从 admissible 单独推出不可交换性。

此外，alternating [] 的定义已经是 [0]，encode 已包含末位零。
在 n=2 再追加零会得到长度 4 的 [1,−1,0,0]，而 tailWord 长度为 3。
省掉重复追加只能修复长度，不能修复上面的基数障碍。

保号命题在整个 Φ 上同样不成立：右侧唯一一对的 signInt a · signInt b = 1，
而上表同时含有正号与负号，所以不存在仅依赖 n 的 ε(n) 使所有项逐项相等。
上表的总符号和仍为 −1，符合原猜想的 n=2 情形；本反例不反驳原猜想。

## 可复算的有限计算

以下 Python 3 程序枚举全部六个固定首项排列，独立核对后缀与倒序前缀预算，
并直接按冻结 Good / Unswappable 的递归条件检查唯一编码词。
它不重试第一轮已经排除的对合，也不以有限吻合声称一般公式。

```python
from itertools import permutations

def sign(p):
    return (-1) ** sum(p[i] > p[j]
                       for i in range(len(p)) for j in range(i + 1, len(p)))

def good(w):
    h = 0
    for x in w:
        h += x
        if h < 0:
            return False
    return True

def unswappable(w):
    h = 0
    for i in range(0, len(w) - 1, 2):
        x, y = w[i:i + 2]
        if h + x >= 0 and h + y >= 0:
            return False
        h += x + y
    return True

rows = []
for t in permutations(range(1, 4)):
    p = (0,) + t
    budgets = tuple(sum(p[i] - 2 for i in range(4 - k, 4))
                    for k in range(1, 4))
    w = tuple(p[i] - 2 for i in range(3, 0, -1))
    assert budgets == tuple(sum(w[:k]) for k in range(1, 4))
    assert (min(budgets) >= 0) == good(w)
    if min(budgets) >= 0:
        rows.append((p, budgets, w, sign(p)))

pairs = []
for a in permutations(range(1)):
    for b in permutations(range(1)):
        w = tuple(x for i in range(1)
                  for x in (a[i] + 1, -(b[i] + 1))) + (0,)
        if good(w) and unswappable(w):
            pairs.append((a, b, w))

assert len(rows) == 3 and len(pairs) == 1
assert rows[0][2] == (1, 0, -1) and pairs[0][2] == (1, -1, 0)
assert not unswappable(rows[0][2])
assert {r[3] for r in rows} == {-1, 1}
assert sum(r[3] for r in rows) == -1
print(rows)
print(pairs)
```

## 原猜想尚缺的数学环节

必须先证明整个 Φ(n) 的非剩余项反号消去，再把不可交换剩余项与合法 (a,b)
双射并比较符号，才能应用已冻结的 encoded_product_sign_sum。
双射的正确候选定义域须加上 Unswappable 0 (tailWord n p hn)。
上述一般消去、受限双射及符号桥均未在本次交付中形式化。
第一轮笔记的配对探针不能代替这些一般证明。

本次按尾词形态不匹配的预登记条件停止：没有交付正向映射、逆向映射或保号定理，
没有进入逆向构造的三次尝试。没有新公开 Lean 声明或首次冻结；
admission_basis: none。原猜想未闭合，未推进其已知计算范围。
