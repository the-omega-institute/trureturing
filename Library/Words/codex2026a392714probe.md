---
bibkey: codex2026a392714probe
authors: Codex implementation worker
year: 2026
title: A392714 parity imbalance — bounded involution probe
doi: null
url: https://arxiv.org/html/2605.11137v1
claim: Investigation of the unweighted parity conjecture; no resolution is claimed.
strata_touched: []
license: citation-only
triage: anchor
---

# A392714 反号对合探针

产地：Codex 主循环，使用 lean4 skill 检索与核验；零独立评审席。
输入来自 caller 的实施 brief 与分诊笔记 `oeis2026triage0909`；下列现场读数由本席取得。
源码起点 `4ac806a62d274a48550978b827a4bf546a8c898e`，
Lean 4.33.0 / Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。

## 预登记与停止条件

档位 1，有停止条件的组合探针。目标严格为 caller 的全称无权符号和；
拟议逃逸仍为保持后缀预算的反号对合及唯一余项分类。
先检索冻结 D5 与钉版 Mathlib；若精确绑定闭合，则报 bind-only 停手。
若未命中，检验三类配对：固定不交位置对、首个可交换的相邻位置、固定相邻值对。
允许基于反例修订一次组合表述；若仍没有可证明的全局对合与余项分类，
以 blocked 端化，记录可证明子类与反例，不把有限吻合当成一般证明。
有限枚举只作探针和语义回声，不独立冻结正向实例。

## 目标回声

一基排列满足 σ(1)=1，且对 1≤k<2n，
T_k=Σ_{i=2n−k+1}^{2n}((σ(i):ℤ)−1−n)≥0。
零基编码应为 π:Perm(Fin(2n))，π(0)=0，
T_k=Σ_{i:Fin(2n), 2n−k≤i.val}((π(i).val:ℤ)−n)。
π(i)=σ(i+1)−1；所有减法在 ℤ 中进行。
signInt π 是 Mathlib `Equiv.Perm.sign π : ℤˣ` 到 ℤ 的强制转换。
k=2n 不纳入：该总和为 −n；k=2n−1 的和为 0。

## 文献现场核对

已下载 OEIS A392714、A147681 的完整 text 响应与 arXiv:2605.11137v1 HTML。
论文 §3 的 T_k、固定首项与 k=1,…,N−1 均吻合；Remark 4 明确写 conjecture，
且说明偶 p 奇排列占优、奇 p 偶排列占优。
Claim 4.1 含乘积权重 ∏ E_k!/(E_k−p)!，未推出本目标的无权和。
OEIS A392714 当前 comment 仍将奇偶差称为 conjecture（报告 n≤13 数据）。
A147681 的关联计数不构成本目标的证明。

## 构建与检索现场记录

`make lean-cache-ensure`：seeded / clonefile / clonefile_attempts=1，
donor=`/Users/chronoai/trureturing`，Mathlib 缺失 olean=0，两层 warm。
ensure 后独立按 D5 源 stem 与 olean stem 作集合差：3965 个源、3962 个 olean，
缺失 7 个源模块（另有 4 个多余 olean）；warm 未被当作有效性证明。
目录直接文件数：Library/Words=20，D5/S1/Words=14，Blueprint/D5/S1/Words=20，均低于 48。
未设置 LAKE_JOBS。

初筛 D5 的 `392714|147681|Wronskian|sum_involution|sign.revers` 未命中本目标；
钉版 Mathlib 的 Wronskian 文件只处理两个多项式，非此排列计数。
`Finset.sum_involution` 要求自行提供反号、无不动点、集合保持、二次还原四项；
其泛型消去不产生所缺对合。检索范围与后续 Lean 接口核验将继续补记。

## 未主张

未主张检索穷尽；未主张文献不存在后续证明；未主张本目标已证或已反驳。
caller 的 n=1..4 表与分诊席的查阅范围目前是输入，不能冒充本席枚举或穷尽检索。
未证明一般反号对合、唯一余项分类、无权奇偶差或 Wronskian 常数公式。
本笔记不是 OpenProblemResolutionClaim 或冻结记录。

## 第一轮实测与唯一一次归约修订

本席独立枚举全部固定首项排列，实际得到 n=1,…,5 的
（偶，奇）为 (1,0)、(1,2)、(18,17)、(500,501)、(26555,26554)。
倒序尾项步长 w_j=σ(2n+1−j)−1−n，j=1,…,2n−1，构成
{−(n−1),…,0,…,n−1} 的非负前缀路径。
尾项倒序的符号因子为 (−1)^((2n−1)(n−1))=(−1)^(n−1)，
所以原目标等价于这些步长词相对递增次序的符号和为 +1。

固定位置块 (w₁,w₂)、(w₃,w₄)、…，从左选第一个两种次序均合法的块交换。
若块前高度为 h，交换可行恰需 h+a≥0、h+b≥0（块末高度不变）。
换前换后同一块仍可选，且所有更早块未变，故二次还原；互异步长的交换反号。
n=1,…,5 穷举未出现保持性/反号性/二次还原失败，但剩余项数为
1、1、3、15、121，不能报告为唯一余项。

重叠位置规则失败：w=(1,−1,0) → (1,0,−1) → (0,1,−1)，
三者前缀预算分别为 (1,0,0)、(1,1,0)、(0,1,0)。
每次都选首个合法相邻交换，选点改变，n=2 已不构成对合。

固定相邻值对也失败：按递增步长配 (−3,−2)、(−1,0)、(1,2)，
选择最小的可合法交换对。n=4 时
(1,−1,2,−2,3,−3,0) → (1,0,2,−2,3,−3,−1)
→ (1,0,2,−3,3,−2,−1)。首步抬高预算，使原来不可交换的更小值对可交换。

修订探针：固定位置规则的剩余项必形如
(a₁,−b₁,…,a_m,−b_m,0)，m=n−1，a、b 各为 {1,…,m} 的排列。
理由：零在任一完整块中都会使该块可交换，所以只能在末位；不可交换块
必须先正后负，且 h<b_i≤h+a_i。记 A_i=Σ_{j≤i}a_j、B_i=Σ_{j≤i}b_j，
等价于 A_{i−1}<B_i≤A_i。剩余词的符号为 sign(a)sign(b)。
此轮只尝试证明/配对这个交错分割类；失败即停止，不继续扩展选题。
进一步枚举 m≤6 观察到：固定 a 后对合法 b 的符号和，仅 a=(1,…,m) 时为 1，
其它 a 时为 0。这是待证加强命题，不能当作已知引理。

构建实测：`make lean` EXIT=0，39.41 秒，maximum resident set size=5907873792 bytes。
未触发串行回退。GitHub code search 的 `A392714 extension:lean` 与
`"late-growing" extension:lean` 各返回空数组；Google 搜索返回 challenge 页面，
未取得可用检索结果，不作搜索完成声明。

## 停止结算：blocked

剩余类上的首个合法相邻 b 交换也不是对合：固定 a=(2,3,1)，
b=(1,3,2) → (1,2,3) → (2,1,3)。三者的 B_i 分别为
(1,4,6)、(1,3,6)、(2,3,6)，均满足 A=(2,5,6) 给出的交错条件。
因此一次归约修订后，仍未得到剩余类的稳定反号配对；按预登记停止。
加强的逐 a 符号和公式未证，不能拿它闭合原猜想。

有价值的剩余问题：对非递增 a，如何把满足 A_{i−1}<B_i≤A_i 的 b 配成反号对，
或者给出该逐行符号和的独立证明。递增 a 的确只允许递增 b：
逐项从最小未用正整数归纳即可，但这未解决其他 a 的消去。

原判据直接逐后缀求和，与倒序步长前缀判据在 n=1,…,4 的合格集合
对称差均为 0，集合大小 1、3、35、1001。
非空两侧数值见证（均固定首项 1）：n=2，
σ=(1,2,3,4) 的 T₁,T₂,T₃=(1,1,0)，signInt=+1，属于 Φ₂；
σ=(1,4,3,2) 的预算为 (−1,−1,0)，signInt=−1，被预算排除。
误把 k=4 纳入时，前者 T₄=−2；这是边界陷阱的实际负对照。
下列 Lean 单元已在 warm/stamped 树执行，EXIT=0。

## 已编译探针源码与保证边界

下列为完整独立探针，可提取本节唯一 Lean 代码块到仓外文件后，
在此钉版热树执行 `lake env lean <该文件>`。
四条一般引理的 kernel axiom 闭包均仅为 propext、Classical.choice、Quot.sound；
无 sorry、无私 axiom。初次编译的两个展开/模式匹配错误已修，最终退出码为 0。
数值见证用 kernel `decide`；没有使用 native_decide。

已核验：原目标的零基 Prop 定义、正反见证、fixed-pair flip 的二次还原、
前缀非负保持、List.Perm 保持、不可交换块的正负/高度必要条件。
未核验：Target 的证明、φ 到 List Good 的一般形式化等价、
List flip 与原始 Perm.sign 的完整桥、全部剩余项的 Lean 分类及其符号消去。
反号的数学理由是一次相邻交换；不能把仅有的 List.Perm 保持定理冒称反号定理。

本轮零新增 D5 模块、零 Problems 卷宗、零冻结、零 coverage、
零 OpenProblemResolutionClaim。编译探针源码以本报告代码块保存；
它是诊断交付，不以有限正向实例申请内容准入。
因此没有新域目录，也没有改动 Problems 的封闭八节。

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open scoped BigOperators
namespace A392714Probe

-- Explicit zero-based encoding of the one-based source statement.
def suffixBudget (n k : ℕ) (p : Equiv.Perm (Fin (2 * n))) : ℤ :=
  ∑ i : Fin (2 * n), if 2 * n - k ≤ i.val then ((p i).val : ℤ) - (n : ℤ) else 0

def admissible (n : ℕ) (p : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i : Fin (2 * n), i.val = 0 → (p i).val = 0) ∧
    ∀ k ∈ Finset.Ico 1 (2 * n), 0 ≤ suffixBudget n k p

noncomputable def phi (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) := by
  classical
  exact Finset.univ.filter (admissible n)

def signInt {d : ℕ} (p : Equiv.Perm (Fin d)) : ℤ := (Equiv.Perm.sign p : ℤ)

-- This is a Prop definition, not atheorem or an assumed axiom.
def Target : Prop :=
  ∀ n : ℕ, 1 ≤ n → (∑ p ∈ phi n, signInt p) = (-1 : ℤ) ^ (n + 1)

example : admissible 2 (1 : Equiv.Perm (Fin 4)) := by unfold admissible; decide
example : suffixBudget 2 1 (1 : Equiv.Perm (Fin 4)) = 1 ∧
    suffixBudget 2 2 (1 : Equiv.Perm (Fin 4)) = 1 ∧
    suffixBudget 2 3 (1 : Equiv.Perm (Fin 4)) = 0 := by decide
example : suffixBudget 2 4 (1 : Equiv.Perm (Fin 4)) = -2 := by decide
example : suffixBudget 2 1 (Equiv.swap (1 : Fin 4) 3) = -1 ∧
    suffixBudget 2 2 (Equiv.swap (1 : Fin 4) 3) = -1 ∧
    suffixBudget 2 3 (Equiv.swap (1 : Fin 4) 3) = 0 := by decide
example : ¬ admissible 2 (Equiv.swap (1 : Fin 4) 3) := by
  unfold admissible
  decide
example : signInt (1 : Equiv.Perm (Fin 4)) = 1 := by simp [signInt]
example : signInt (Equiv.swap (1 : Fin 4) 3) = -1 := by
  simp [signInt, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3)]

-- Generic prefix budgets and the fixed, disjoint position-pair rule.
def Good (h : ℤ) : List ℤ → Prop
  | [] => 0 ≤ h
  | a :: w => 0 ≤ h ∧ Good (h + a) w

instance (h : ℤ) (w : List ℤ) : Decidable (Good h w) := by
  induction w generalizing h with
  | nil => exact inferInstanceAs (Decidable (0 ≤ h))
  | cons a w ih => exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (0 ≤ h))) (ih _)

def flip (h : ℤ) : List ℤ → List ℤ
  | a :: b :: w =>
    if 0 ≤ h + a ∧ 0 ≤ h + b then b :: a :: w else a :: b :: flip (h + a + b) w
  | w => w

theorem flip_twice (h : ℤ) (w : List ℤ) : flip h (flip h w) = w := by
  match w with
  | [] => rfl
  | [a] => rfl
  | a :: b :: w =>
    by_cases hab : 0 ≤ h + a ∧ 0 ≤ h + b
    · simp only [flip, if_pos hab, if_pos (And.intro hab.2 hab.1)]
    · simp only [flip, if_neg hab]
      rw [flip_twice (h + a + b) w]
termination_by w.length

theorem flip_good (h : ℤ) (w : List ℤ) (hw : Good h w) : Good h (flip h w) := by
  match w with
  | [] => exact hw
  | [a] => exact hw
  | a :: b :: w =>
    by_cases hab : 0 ≤ h + a ∧ 0 ≤ h + b
    · simp only [flip, if_pos hab, Good] at *
      exact ⟨hw.1, hab.2, by simpa [add_assoc, add_comm, add_left_comm] using hw.2.2⟩
    · simp only [flip, if_neg hab, Good] at *
      exact ⟨hw.1, hw.2.1, flip_good (h + a + b) w hw.2.2⟩
termination_by w.length

theorem flip_perm (h : ℤ) (w : List ℤ) : (flip h w).Perm w := by
  match w with
  | [] => exact List.Perm.refl _
  | [a] => exact List.Perm.refl _
  | a :: b :: w =>
    by_cases hab : 0 ≤ h + a ∧ 0 ≤ h + b
    · simp only [flip, if_pos hab]
      exact List.Perm.swap _ _ _
    · simp only [flip, if_neg hab]
      exact List.Perm.cons a (List.Perm.cons b (flip_perm (h + a + b) w))
termination_by w.length

theorem blocked_pair (h a b : ℤ) (w : List ℤ)
    (hg : Good h (a :: b :: w)) (hb : ¬ (0 ≤ h + a ∧ 0 ≤ h + b)) :
    0 < a ∧ b < 0 ∧ h < -b ∧ -b ≤ h + a := by
  have ha := hg.2.1
  have hab : 0 ≤ h + a + b := by
    have ht : Good (h + a + b) w := hg.2.2
    cases w with
    | nil => exact ht
    | cons c w => exact ht.1
  have hh := hg.1
  omega

#check Finset.sum_involution
#check Equiv.Perm.sign_mul
#check Equiv.Perm.sign_swap
#print axioms flip_twice
#print axioms flip_good
#print axioms flip_perm
#print axioms blocked_pair
end A392714Probe
```

## 重现实验代码

仅用于有限探针，不承担一般定理。完整三规则枚举器如下；
输出中的 null 表示仅在所枚举窗口未发现失败。

```python
from itertools import permutations
from collections import Counter
import json
from pathlib import Path

def budgets(w):
 h=0; out=[]
 for x in w:h+=x;out.append(h)
 return out

def valid(w):return all(x>=0 for x in budgets(w))
def sign(w):return (-1)**sum(a>b for i,a in enumerate(w) for b in w[i+1:])
def swap(w,i,j):
 v=list(w);v[i],v[j]=v[j],v[i];return tuple(v)
def fixed_positions(w):
 for i in range(0,len(w)-1,2):
  v=swap(w,i,i+1)
  if valid(v):return v
 return w

def first_adjacent(w):
 for i in range(len(w)-1):
  v=swap(w,i,i+1)
  if valid(v):return v
 return w

def fixed_values(w):
 s=sorted(w)
 for a,b in zip(s[::2],s[1::2]):
  v=swap(w,w.index(a),w.index(b))
  if valid(v):return v
 return w

results=[]
for n in range(1,6):
 ws=[w for w in permutations(range(1-n,n)) if valid(w)]
 sigmas=[(1,)+tuple(x+n+1 for x in w[::-1]) for w in ws]
 count=Counter(sign(s) for s in sigmas)
 row={'n':n,'count':len(ws),'even':count[1],'odd':count[-1], 'difference':count[1]-count[-1], 'rules':{}}
 for rule in [fixed_positions,first_adjacent,fixed_values]:
  fixed=[];bad=None
  for w in ws:
   v=rule(w)
   if v==w:fixed.append(w)
   elif not valid(v) or sign(v)!=-sign(w) or rule(v)!=w:
    if bad is None:bad={'w':w,'image':v,'image_twice':rule(v),'budgets':budgets(w),'image_budgets':budgets(v)}
  row['rules'][rule.__name__]={'fixed_count':len(fixed),'fixed_signed_sum':sum(map(sign,fixed)), 'first_failure':bad, 'fixed_examples':fixed[:5]}
 results.append(row)
print(json.dumps(results,ensure_ascii=False,indent=2))
for steps in [(-3,1,2),(-4,-2,1,2,3),(-5,-2,1,2,4),(-3,-2,-1,1,2,3),(-7,-3,-1,1,3,7)]:
 ws=[w for w in permutations(steps) if valid(w)]
 print('general_steps',steps,'count',len(ws),'signed_sum',sum(map(sign,ws)))
Path(__file__).with_name('probe-results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
```

## 未主张补记

未主张数学检索穷尽；GitHub 两个精确词查询为空并不证明无第三方形式化。
没有读完 A147681 的全部直接引用、SeqFan 历史链或 2025 年论文全文，
没有把 Google challenge 当作有效搜索结果。
分诊席原先的“未找到对合”是转述；本报告三类失败与剩余项计数由本席亲算。
caller 的四项数值已由本席独立算法复核；n=5 亦仅为有限探针，未推进未知范围。
本席单点自查与 Lean kernel 核验不冒称独立/异模型评审。
一般奇偶差仍未证；本报告不是 published 或问题已解决的证据。

## 交付门收据

`make lean-report` EXIT=0，58.90 秒，delta changed=0 / added=1 / recheck=1。
计量口径分列：time 的 maximum resident set size=3922231296 bytes，
report-supervisor 的 rss_peak_kb=4843216；二者不混作同一峰值。
该步骤前报告与已编译源码已提交并推送至 c8828a5812。
首次 `make emit` 被 invalid-library-note 拒绝：bibkey 不满足
`^[a-z]+[0-9]{4}[a-z][a-z0-9]*$`。已按既有格式改名为 codex2026a392714probe，
未改判官。最终 `make emit` EXIT=0，emitted: 0 changed blueprint(s)。
无 OpenProblemResolutionClaim，故 ledger-align --add 不适用。
提交前与当次 origin/dev=c2f1ec82d0c22eeb0712d495fbe230465954f196
作 git merge-tree，EXIT=0，无冲突。
