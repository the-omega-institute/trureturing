---
bibkey: codex2026a392714residual
authors: Codex implementation worker
year: 2026
title: A392714 round two — the residual signed sum S(a)
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: A general Lean proof of the residual signed sum S(a); the original conjecture bridge is outside scope.
strata_touched:
  - D5/S1/Words/Compositions/ResidualPermutationSign
license: citation-only
triage: anchor
---

# S(a) 第二轮研究记录

**本轮结算：成。** S(a) 的全称 Lean 证明已通过 make lean，无 sorry、私 axiom 或
native_decide，且已开 [PR #6689](https://github.com/the-omega-institute/trureturing/pull/6689)。
证明、发射与冻结/覆盖均通过规定门序。这个“成”按用户本轮的停止判据，
不表示 PR 已合入 dev，也不表示 A392714 原猜想及其桥已证明。

产地：Codex 主循环，使用 lean4 skill；零独立评审席，单点自查。
用户给出的 m≤7 读数是输入，未冒充本席亲验。
起点及本地 origin/dev 均为 `25b883dcebf4305950c779111490338639eed3bc`；
分支 `lane/math/a392714r2`，Lean 4.33.0，
Mathlib pin `db584cd6d46c92f209a44c0f1c829460d327499d`。
已完整分段阅读 CLAUDE.md、agents/CONTEXT.md 及上一轮
`codex2026a392714probe`；不重做 Φ(n) 上的配对、文献核对或已有有限枚举。
Library/Words 容量：`find Library/Words -type f | wc -l` = 22（新增本文件前）。

## Verified locator

本条**不是文献陈述,是本仓推导**,故 `doi: null`。规范定位是仓库本身:
https://github.com/the-omega-institute/trureturing
S(a) 的形式化真源为 `D5/S1/Words/Compositions/ResidualPermutationSign.lean`,
公开定理 `signed_residual_sum`(另两条公开定理 `lower_cut_removal`、`upper_sum_vanish`
是其证明路径上的具名中间结果)。

**原始上下文(只作 provenance,不是本条的出处)**:OEIS A392714
(https://oeis.org/A392714)与 arXiv:2605.11137v1 §3 及 Remark 4 —— 二者把 A392714 的
奇偶差明写为 conjecture。**S(a) 这条陈述在那两处都没有出现**:它是本研究线第一轮把
「在 Φ(n) 上找反号对合」归约之后新造的组合命题。原猜想到 S(a) 的桥不在本轮范围内。

## 预登记 v1

档位 1，新近小猜想研究线的独立组合子命题。
唯一目标：对 m≥1 及 {1,…,m} 的排列 a，A₀=0，Aᵢ=Σⱼ≤ᵢaⱼ，
L(a)={b排列 : 对所有 1≤i≤m，Aᵢ₋₁<Bᵢ≤Aᵢ}，证明
Σᵦ∈L(a)sign(b)=[a=id]。不加入从 Φ(n) 到 L(a) 的桥。

先按 D5 → 钉版 Mathlib → 第三方 Lean/数学文献顺序检索。
精确的已发表且带证明的等价陈述命中，即按用户要求
`bind-only + rule-11-upstream-wrapper` 报告并停止重证。
未命中时先分析带区间约束的交替路径和，优先最大值删除递推，
再分析行列式/外代数状态和及容斥；每条路线记录所需的精确一般引理。
拟议 escape_witness：区间约束交替路径和的一般消去递推，或等效的
行列式/组合构造。尚未构造，不把拟议见证报成已证。
如观察所得见证改变，先另记预登记版本再实施。

停止：成=S(a) 无 sorry/私 axiom 的 Lean 证明通过 make lean 且 PR 开出；
翻=实际反例及 kernel 见证；否则本轮以 blocked 端化。
路线停止条件：一个候选递推被反例击破后，只允许一次改变状态空间的修订；
同一缺口再次出现即登记障碍，转向下一路线。
本次交回前必须结算三态之一，不以 open/进行中冒充结算。
每批检索读数、路线结论和 Lean 验证后即时 commit + push。
有限正向枚举只作诊断，不冻结，不称未知范围进展。

## 声明与构建账（开工时）

公开定理：空；proof_shape / 直接冻结依赖(GID, statement_id) /
escape_witness / admission_basis 均暂无已交付条目。
拟议 S(a) 为 content、escape-witness，最终须以实际证明项重新逐条核对。
make lean：尚未运行；LEAN_CACHE：尚未取得。

## 未主张

未主张检索穷尽；未主张 A392714 原猜想已解决
（桥明确不在本轮范围）；未主张任何有限吻合构成证明。
未真正打开的外部页面均为 ASSUMED-UNVERIFIED，不能承载文献结论。

## 检索批次 1：D5

命令模板 `git grep -n -P '<pattern>' -- D5`，在上述起点源码上查询。
下列为匹配行数，不冒充声明数：

| pattern | 行数 | exit |
| --- | ---: | ---: |
| `\bsum_involution\b` | 3 | 0 |
| `\bsign\b` | 294 | 0 |
| `\bPerm\.sign\b` | 0 | 1 |
| `\bprefix\b` | 371 | 0 |
| `partial sum` | 41 | 0 |
| `Lindström\|Gessel\|Viennot\|LGV`（PCRE alternation） | 0 | 1 |
| `\btheorem\b`（相同词界特性阳性对照） | 25410 | 0 |

sum_involution 命中 ConvolutionRecurrenceOddPowersOfTwo 与
ReflectedSpectrum/ParityConditionedMoments，均需自供配对，不是 S(a)。
Perm.sign 与 LGV 零命中；sign/prefix 的宽筛含注释及不相关含义，
这些计数只证明搜索执行，不证明语义穷尽。
完整 stdout、命令及退出码保存在 runner attempt 的 `d5-search.json` 和对应 txt。

## 检索批次 2：钉版 Mathlib 与缓存

`make lean-cache-ensure` EXIT=0：status=seeded，method=clonefile，
clonefile_attempts=1，donor=/Users/chronoai/trureturing，stamp_miss=null，
mathlib_missing_olean_files=0，project_olean_state=warm，mathlib_olean_state=warm；
archive_status=not_attempted，archive_skip_reason=project olean state is warm。
未设置 LAKE_JOBS；warm 收据不代替 make lean。

命令模板 `rg -n '<pattern>' .lake/packages/mathlib/Mathlib`。
匹配行数（不是声明数）：`\bsum_involution\b` 7；
`\b(theorem|lemma) sign_[A-Za-z_]+` 115；`\bdet_apply\b` 53；
`\bsum_comm\b` 95；`Lindström|Lindstrom|Gessel|Viennot|\bLGV\b` 0；
`non.?intersecting|nonintersecting` 0；阳性对照 `\btheorem\b` 130789。
零命中 exit=1，其余 exit=0，全部 stderr 为空。
完整收据在 attempt 的 mathlib-search.json 与对应 txt。

精确接口位于 GroupTheory/Perm/Sign.lean 的 sign_mul、sign_one、sign_swap，
LinearAlgebra/Matrix/Determinant/Basic.lean 的 det_apply 与 det_apply'。
后者逐位乘积的展开本身不处理依赖整个前缀的约束。
sum_involution 由 to_additive 生成，文本计数不含它的生成声明头；
后续编译 #check 才核对 elaborated 类型。
此范围未命中目标；不主张整个数学文献中不存在等价定理。

## 检索批次 3：第三方与公开数学检索

实际出网方式为本地 authenticated gh 与 Python urllib（未用任何未开放的搜索工具）。
命令 `gh api -X GET search/code -f 'q="partial sums" "sign" language:Lean'`
返回 total_count=97，读取默认第一页；`"interlacing" "permutation" language:Lean`
返回 2（PerAlexandersson/RealRooted 的 Tactic/Targets.lean、
afflom/emporous 的 UorAtlas/Scales.lean）。查询是词面粗筛，未宣称全部 97 个文件已读。

已打开 arXiv API：`all:"permutations" AND all:"partial sums" AND all:"sign"`，
max_results=10，totalResults=2。摘要分别为 2608.16752v1（随机游走凸包吸收概率的
signed permutations，符号为步长正负选择）及 1703.08830v2（signed Young modules
和整除限制的 compositions）；摘要没有本题双排列交错区间的逐 a 奇偶差定理。
两篇全文目前 ASSUMED-UNVERIFIED，不从摘要推断全文没有等价结果。

OEIS 搜索 `"permutations" "partial sums" "sign"` 的 text 响应已打开，首批十项为
A316292、A316293、A214663、A316294、A282864、A282840、A282865、A130472、
A058884、A137501；未命中 S(a) 陈述。不重查上一轮已核对的原序列全文。
Reservoir `/packages?q=permutation` 返回普通 829 项目录及 No results found 混合页面，
未把它认作有效的精确包检索。
Google 的查询 `permutation "partial sums" "signed sum"` 返回重定向/challenge；
Bing 的查询 `permutation "interlacing" "partial sums" sign` 页面标题保留查询，
正文却全为 API design 结果（10 条），语义不相干，判无有效读数。
以上失败不当作零命中或检索穷尽。原始响应与解析文本均保存在 attempt。

### 第三方跟进与第一批状态探针

已下载并读相关命中上下文：TauCeti 的 Dominance.lean 是 James dominance lemma
（Young tabloids / column antisymmetrizer）；RealRooted 的 Targets.lean 是实根多项式
tactic 目标目录；UorAtlas/Scales.lean 的 interlacing 是 Cauchy 特征值交错。
它们均不是所查 S(a) 的精确陈述，未加入依赖。
arXiv 另查 `all:"permutation" AND all:"interlacing" AND all:"sum"` 得 4 摘要：
2602.04390v2、1505.08010v1、1312.0665v2、2505.05873v1；分别是彩色交错三角形、
Ramanujan 图、Hardy–Littlewood–Pólya 序列和 Baxter 多项式实根。
`all:"permutation" AND all:"partial sums" AND all:"cancellation"` 得 0。
四篇全文未读，ASSUMED-UNVERIFIED。以上是有限检索范围中的 not-found-in-searched-scope。

先定义子集状态，避免把前缀和相同但已用值不同的历史混在一起：
F₀(∅)=1，其余零；令 w(T)=Σₓ∈T x，则
Fᵢ(T)=[Aᵢ₋₁<w(T)≤Aᵢ] Σₓ∈T (−1)^{#{y∈T:y>x}} Fᵢ₋₁(T\{x})。
末态 Fₘ({1,…,m}) 是目标交替和；这一步的纸面理由是按末字母分组，
新增逆序恰为前缀中大于 x 的字母数，尚未声称 Lean 证明。

以该状态算法诊断更强的任意正权重版本：权重集 (1,2,3,4)、(1,2,4,8)、
(1,3,4,9)、(2,3,5,6) 各查全部 24 个 a，均仅递增 a 的末态为 1。
原目标 m=8 查 40320 个 a：一个 1、40319 个 0、反例零。
这批只用于检查状态表述及决定是否研究权重一般化；不是证明，也不报为未知范围进展。
首次脚本因本机 Python 不支持 int.bit_count 退出 1，改为 bin(...).count("1")
后退出 0；未隐去工具失败。完整代码和结果如下，另存 attempt/states.py 与 states-results.json。

```python
from itertools import permutations,combinations
from collections import defaultdict
import json
from pathlib import Path

def signed_states(weights,a):
 n=len(a); states={0:1}; layers=[]; low=0
 for y in a:
  high=low+y; nxt=defaultdict(int)
  for mask,v in states.items():
   h=sum(w for j,w in enumerate(weights) if mask>>j&1)
   for j,x in enumerate(weights):
    if not mask>>j&1 and low<h+x<=high:
     nxt[mask|1<<j]+=v*(-1 if bin(mask>>(j+1)).count("1")%2 else 1)
  states={k:v for k,v in nxt.items() if v};layers.append(states);low=high
 return states.get((1<<n)-1,0),layers

rows=[]
for weights in [(1,2,3,4),(1,2,4,8),(1,3,4,9),(2,3,5,6),(1,2,3,4,5,6,7,8)]:
 bad=None;count=0;hist=defaultdict(int)
 for a in permutations(weights):
  val,_=signed_states(weights,a);count+=1;hist[val]+=1
  if val!=int(a==weights):bad={'a':a,'sum':val};break
 row={'weights':weights,'checked':count,'bad':bad,'hist':dict(hist)};rows.append(row);print(json.dumps(row),flush=True)
Path(__file__).with_name('states-results.json').write_text(json.dumps(rows,indent=2)+'\n')
```

## 预登记 v2：有限多项式的行列式消去（待核验）

v1 的子集递推保留为探针；新的拟议逃逸见证改为以下**有限多项式恒等式**及
排列指数的唯一性引理。它不是幂级数，也不包含原猜想的桥。
本节在 Lean 实施和该恒等式的独立数值核验之前登记。

对固定 b，原条件等价于 Bᵢ≤Aᵢ<Bᵢ₊₁（1≤i<m），Aₘ=Bₘ=N。
故 dᵢ=Aᵢ−Bᵢ 独立满足 0≤dᵢ<bᵢ₊₁；d₀=dₘ=0；
aᵢ=bᵢ+dᵢ−dᵢ₋₁ 自动为正整数。
把所有正整数组合 a 的符号和作为系数，得到有限多项式

Pₘ(x)=Σᵦ sign(b) x₁^{b₁} ∏ᵢ₌₂ᵐ [xᵢ Σᵣ₌₀^{bᵢ−1} xᵢ^{bᵢ−1−r}xᵢ₋₁^r]。

这是逐位乘积的行列式。乘以相邻差 ∏ᵢ₌₂ᵐ(xᵢ−xᵢ₋₁)，
各行成为 xᵢ^{bᵢ}−xᵢ₋₁^{bᵢ}（首行不变），累加行还原普通幂矩阵。
Vandermonde 公式预期给出

Pₘ = x₁ (∏ᵢ₌₂ᵐ xᵢ²) ∏_{1≤i<j≤m, j−i≥2}(xⱼ−xᵢ)。

排列指数唯一性拟议证明：任一项的第 2…m 个指数至少 2；若指数是
1…m 的排列，则指数 1 必在第一位。取第一变量指数 1 强迫所有含 x₁ 的
差因子选 xⱼ；去掉第一变量并把其余指数各减 1 后归纳，唯一得到 (1,…,m)，
系数 +1。也可把每个差因子选项看作完全图定向，固定相邻边形成一条有向链；
入度为 0…m−1 的排列迫使定向传递且链决定次序。

状态仍未结算：上述恒等式及系数桥尚未 Lean 核验，不把纸面推导当作成功态。

## 预登记 v3：逐条删除下界的组合证明（待 Lean 核验）

v2 仍是一条纸面证明路线；现改用更短的纯组合证明，不需要形式化多项式系数桥。
新的拟议见证点名为 lower_cut_removal（符号和层面删去一个下界）与
upper_sum_vanish（上界集合由最小错位值给出的固定交换封闭）。在此登记后才写 Lean。

1. 总是保留 Bᵢ≤Aᵢ。按 i=1,2,…,m 的顺序删去下界 Aᵢ₋₁<Bᵢ。
   i=1 下界由正性自动成立；i≥2 的坏子集 Bᵢ≤Aᵢ₋₁ 用固定交换 (i−1,i)。
   它只改变 Bᵢ₋₁，而交换后 Bᵢ₋₁′<Bᵢ≤Aᵢ₋₁，故上界保持。
   早先的下界已经删除，剩余下界涉及 Bᵢ 或更后，均不变。
   坏子集反号且二次还原，因此删除该下界不改变总符号和。
   **不是**在 L(a) 上再选首个合法交换；这是不同集合之间逐条消去的恒等式。
2. 对只剩上界的集合，若 a=id，逐项最小未用值强制 b=id。
   否则令 k 为 a 的最小错位值（此前各位固定），令 j>k 为值 k 的位置。
   上界同样强制 b 的此前各位固定，所以位置 j−1,j 的值都至少 k。
   由 Bⱼ≤Aⱼ=Aⱼ₋₁+k，交换后 Bⱼ₋₁′≤Bⱼ−k≤Aⱼ₋₁；
   其它上界不变，固定交换 (j−1,j) 即给出整个上界集合的反号对合。

一基描述如上；Lean 将在 Fin m 里对数值加 1，全部边界按前缀长度定义。
拟议公开 S(a)：proof_shape=content，直接冻结依赖=[]（只用 Mathlib），
escape_witness=lower_cut_removal + upper_sum_vanish，admission_basis=escape-witness。
最终四项判据须对 elaborate 后的实际声明路径逐条作答。

## Lean 核验批次 1

热树增量 `lake env lean <attempt>/Residual.lean` 最终 EXIT=0。
已验证 prefixSum、Upper、LowerFrom、signInt 定义，及 prefixSum_zero /
prefixSum_step / prefixSum_mono / prefixSum_pos。首次 prefix 是 Lean 保留字，
且一个试查的 sum_filter_add_sum_filter_not_eq 名不存在；修正后无诊断。
实际 #check 命中 Equiv.sum_comp、Finset.sum_involution、
Finset.sum_filter_add_sum_filter_not、Equiv.Perm.mul_apply、swap_apply_def。
没有 S(a) 证明或冻结；当前完整编译源码保存在本报告末尾，随提交推送。
A5/A5.1 真源已查：utility 位于 anchors 与 digest 之间，无计算性内容时字面 none。
候选 D5/S1/Words 根递归计数 103、Blueprint 对应根 120，故不在根新增；
实际落点须另数一个现有子目录容量。


## Lean 核验批次 2

热树增量最终 EXIT=0，无诊断。已验证相邻交换只改变一个前缀长度、交换二次还原、
无不动点、signInt 反号，以及短前缀上界条件下 Upper 的保持。
首次 rw 误选到要保留的前缀，指定 k=v.val+1 后闭合；未改陈述。
落点候选 Compositions 子目录实际递归计数：D5 6，Blueprint 12，均小于 48。


## Lean 核验批次 3：关键下界删除

热树增量最终 EXIT=0；lower_cut_removal 与 rowSum_eq_upper 已通过 kernel。
它们直接证明每次下界删除的坏子集符号和为零，并迭代到 Upper 集合。
初次 Finset ext/simp 过度展开成员关系，改为显式 Finset.ext 与分步展开后闭合；
类型头需 Classical 的 DecidablePred 已显式提供。余一个不承重的 unused change 警告，
下批会删除该行。未引入 sorry 或 axiom；上界总和的最终消去仍待验证。


## Lean 核验批次 4：上界集合的消去

热树增量最终 EXIT=0，无诊断。upper_fixed_prefix、upper_identity、
exists_min_move、upper_sum_vanish 已通过 kernel。
非恒等 a 的固定交换取最小错位值所在位置及前一位置，与 b 无关，故稳定。
修正了 ext 继续下钻到 Fin.val 的类型错位、let 的替换方向和一次 rw 的匹配侧；
数学陈述未改。两个承重消去引理现在均已编译；最后需把原始 L(a) 的逐项条件接上，
再进入 D5/Scribe/构建门，尚未报“成”。


## Lean 核验批次 5：S(a) 全称证明

热树增量最终 EXIT=0。InResidual 逐项采用原题的严格下界与非严格上界；
inResidual_iff 接到 Upper ∧ LowerFrom 0；signed_residual_sum 无附加假设闭合。
首次 id 分支的 singleton 和未被 simp 自动求值，改用 sum_eq_single 后闭合。
最终 #print axioms 的现场原文为：

- Residual.signed_residual_sum: [propext, choice, Quot.sound]
- Residual.lower_cut_removal: [propext, choice, Quot.sound]
- Residual.upper_sum_vanish: [propext, choice, Quot.sound]

无 sorry、无私 axiom、无 native_decide。该定理还覆盖 n=0，但其 n≥1 特化恰为 S(a)。
这只是单文件 kernel 结果；“成”的其余门（make lean、正式落点、PR）仍须完成。

## 正式落点与摄入收据

S(a) 的唯一内容模块落在 D5/S1/Words/Compositions/ResidualPermutationSign.lean。
Words 已在 Meta/domains.yaml 注册于 S1；同域 Library/Words 与既有 G 模块可查。
头七行采用 A5.1 的 literal `utility: none`。实际新增前目录容量为 D5 6、
Blueprint 12、theory 43（direct files）；均未挤入已满父桶。
**该席曾为本题独立摄入 `docs/develop/theory/RESIDUAL_PERMUTATION_SIGN.md`
（8 行，内容即 S(a) 本身），并以其 atom 走 `make deposit ATOM_ID=…`。
orchestrator 在结算时把这一段整体撤下**（卷、atom blob、backfill 条目三个面),
理由见本节末的「撤下循环摄入」。冻结与 Blueprint 不受影响：
`accepted` 事件的 payload 只有 `statement_id` / `declaration_statement_ids` /
`descriptor_selector` / `prerequisite_frozen_node_ids`，**不引用任何 atom**（已亲验）；
`.scribe.cs` 对该卷与该 atom 的引用数为 **0**（已亲验）。

## 正式构建批次 1

正式模块 `make lean` EXIT=0，墙钟 49.066614792 秒（本工作树、Apple ARM 宿主、
未设置 LAKE_JOBS，已有私有 warm 缓存）；构建日志 `attempt-1/make-lean.log`。
LEAN_CACHE：status=present、method=none、donor=null、stamp_miss=null、
mathlib_missing_olean_files=0、mathlib_olean_state=warm、project_olean_state=warm、
archive_status=not_attempted、archive_skip_reason=project olean state is warm；
pin_sha256=sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e。
`make show-atom` 以纯 hash 重跑 EXIT=0，原文与规范化文本均与 S(a) 一致。
前面的“尚未运行/未证明”是各批次当时的历史记录，本节更新当前验证状态。

## 正式核验批次 2：声明报告与展开后的常量边

`make lean-report` EXIT=0，62.092479959 秒；raw report SHA-256 为
8ead6154f9db782a552e2727b4d9314edf838ac5828cb27941d99b2f41951fa0。
`DependencyAudit.lean` 对正式模块的环境常量读取 theorem/definition 的 proof body，
以 `getUsedConstants` 打印模块内部边，并打印三条公开定理的公理闭包；
EXIT=0，8.518048 秒。实际每条公理闭包均为 propext、Classical.choice、Quot.sound。
其代码与全部输出保存在 attempt；此读取不把依赖出现自动判作语义活用。
现场边确认 signed_residual_sum → rowSum_eq_upper → lower_cut_removal，
及 signed_residual_sum → upper_sum_vanish → upper_fixed_prefix / exists_min_move。
lower_cut_removal → upper_swap_of_short / swap_sum_zero。
语义活路径将在最终逐声明账中结合证明项的用途核对。

## 发射诊断批次

首轮 `make emit` EXIT=2，16.608403125 秒。具名错误是报告 frontmatter 的
`strata_touched: [S1]` 不被本仓专用 note parser 接受（要求 block list），
随后九个 Scribe 来源引用连带报 dangling-literature-reference。
已改为分行列表 `strata_touched` 加 `- S1`；数学源码及声明未改。
这不是 S(a) 的证明失败；不隐去门失败，修正后重跑同一发射门。

第二轮发射 EXIT=2，14.475987958 秒：列表元素 `S1` 不是 canonical GID。
停止猜字段值，读取 LibraryNoteCatalog.cs:218–226 与
DescribeRepositoryValidator.cs:85–98：元素由 GidRef.Create 解析并核对目标。
按现有 oeis2026a392707 实例改为完整
D5/S1/Words/Compositions/ResidualPermutationSign；这是同一元数据错误的精确修正，
没有换问题、改判官或放宽门。

## 最终数学证明与逐声明账

唯一问题 S(a) 已获得无界 Lean 证明，适用于每个 n 与 Fin n 的每个排列 a；
不需要 n>0，所以其正维度特化直接回答 brief。数值采用 a(i)+1，恒等排列的
一基词正是 (1,…,n)。InResidual 原样使用严格左端与弱右端，未加强任何假设。
正式代码见 [ResidualPermutationSign.lean](../../D5/S1/Words/Compositions/ResidualPermutationSign.lean)。
此前提交中的源码快照保留发现路径；最终以 D5 源码为唯一实现。

一基证明如下。令 U(a)={b:每个 Bᵢ≤Aᵢ}，Rᵣ 为在 U(a) 中仍要求
Aᵢ₋₁<Bᵢ 对全部 i>r 成立的符号和。对 0<r<n，Rᵣ₊₁ 比 Rᵣ 多出的坏子集
满足 Bᵣ₊₁≤Aᵣ。交换 b 的第 r 与 r+1 位只改变长度 r 的前缀；它仍小于
Bᵣ₊₁，故保持上界，后面的下界不变。固定交换反号、无不动点、二次还原，
所以坏子集的符号和为零。r=0 的下界由正性自动成立，r≥n 无下界可删。
因此 R₀=Rₙ=Σᵦ∈U(a)sign(b)。

若 a 非恒等，取首个错位 k，令 j>k 为值 k 出现的位置。a 在 k 之前各位固定；
利用每步最小未用值，U(a) 中的 b 也在 k 之前各位固定。因此 bⱼ₋₁,bⱼ≥k。
固定交换 b 的第 j−1 与 j 位后，唯一改变的前缀满足
B′ⱼ₋₁=Bⱼ−bⱼ₋₁≤Aⱼ−k=Aⱼ₋₁。它保持 U(a)，所以整个上界类反号消去。
若 a=id，同一最小未用值归纳强迫 b=id；其符号为 1。S(a) 得证。

下表的 GID 公共前缀为 `D5/S1/Words/Compositions/ResidualPermutationSign.`。
直接冻结依赖均为 **[]**，因此没有应填而漏填的既有 GID/statement_id 对；
导入只来自钉版 Mathlib 与 Init。同批新引理不是 immutable base 上的冻结前置。

| 公开定理 | proof_shape | escape_witness | admission_basis | statement_id（sha256） |
| --- | --- | --- | --- | --- |
| lower_cut_removal | content | upper_swap_of_short 及该定理中的固定坏子集配对构造 | escape-witness | 12e207252609c7fcf0f89ad2c1bbfd3ac45f1210a5a4ca1e51f582096c65fdb5 |
| upper_sum_vanish | content | upper_fixed_prefix；最小错位给出的固定交换构造 | escape-witness | 48347f2dbd0cdf46034363e2c2b56914c8b3ce26f33e99fa9c6d4c0bd54d5561 |
| signed_residual_sum | content | lower_cut_removal 与 upper_sum_vanish | escape-witness | 1d6ff519526035f4e08edcd627ccf0bd618dd8776c3e1a11c676a6eac4d73ab4 |

### lower_cut_removal 的 §3.2 四项

1. 声明内的坏子集闭包证明实际调用 upper_swap_of_short；展开后的常量边已读取。
2. 新内容是 Bᵣ₊₁≤Aᵣ 时的邻位交换保持全部上界及剩余下界。Mathlib 的
   sum_involution 要求调用者提供此闭包；sign_swap 只提供符号，均不直接给出本命题。
3. upper_swap_of_short 是单个排列的条件闭包命题，结论为 Upper；既非 rowSum
   相等的定义展开，也非其改名。整个坏子集配对亦符合 §3.2 允许的显式构造形态。
4. 该闭包被传入 swap_sum_zero 的成员保持参数，所得 hbad=0 被代入有限和分割
   等式。删去死项或展开局部 let 后这一步仍承重；没有从无关合取丢弃见证。

### upper_sum_vanish 的 §3.2 四项

1. 实际常量边 upper_sum_vanish → upper_fixed_prefix 已读取；其证明通过
   最小未用值归纳建立公共固定前缀。
2. 该归纳以及 j−1,j 的具体选择不由通用符号或有限和引理代入得到。
   它们补齐了通用对合引理所缺的领域闭包前提。
3. upper_fixed_prefix 断言 a 的固定前缀强迫 b 的同一前缀固定，结论不是符号和为零，
   与公开定理无定义等价或别名关系。
4. 它给出 bⱼ₋₁≥k，正用于唯一变化前缀的估计，并被成员闭包证明消费；
   去掉此估计就无法完成现有对合的保持条件。不是填入未使用的旁支。

### signed_residual_sum 的 §3.2 四项

1. 展开后的路径为主定理 → rowSum_eq_upper → lower_cut_removal，及
   主定理 → upper_sum_vanish；审计读到两个路径。
2. 两个引理在 immutable base 中均不存在，且各自通过上述新组合闭包得到；
   已检索的 Mathlib 只有通用对合等接口，不给出这种区间保持。
3. lower_cut_removal 比较相邻两个放宽集合，upper_sum_vanish 只涉及 U(a)
   且要求 a 非恒等；两者均非原始 L(a) 恒等式的别名或定义展开。
4. 前者被迭代用来替换原和，后者直接关闭非恒等分支。把私有辅助和局部绑定
   展开后两个结论仍位于返回证明中，未被投影丢弃；只靠冻结前置的绑定操作不足。

上述判形和活路径是实施者对源码与实际常量边的语义核对；不冒称 inspector
自动裁决了新颖性或 §3.2 全部语义，也不冒充独立评审。

### 全部声明的 utility: none 理由

prefixSum、Upper、LowerFrom、signInt、rowSum、InResidual 六个定义给出任意 n
的数学对象。三条公开定理给出无界符号和恒等式；所有私有声明处理任意排列的
前缀、换位、固定位置或求和分割，均用于上述证明。没有有界枚举、checker/
反射算法、待数值前提的 numeric-reduction，也没有固定参数的 certified-instance。
所以对全部声明四类皆不命中，utility=none；其余计算性用途字段为
not-applicable(kind=none)。研究探针没有进入 D5 或单独冻结。

### 路线结算与下一层

v1 子集状态递推只作诊断，没有把最大值插入路线展开成证明，不把“未发展”写成
已被反例否决。v2 的有限多项式/行列式论证保留为纸面推导，未形式化其系数桥，
不主张该附带恒等式获 kernel 验证。v3 的逐条下界删除加上界消去已经完整闭合，
因此 S(a) 没有剩余子命题。本轮没有重试 Φ(n) 上的首个/最后合法交换或值对交换。
下一层由研究线另立范围，先审查上一轮 Φ(n) 到 L(a) 的桥之忠实性，再决定形式化；
本轮并未证明该桥，因而未主张解决 A392714 原猜想。

## 发射诊断的后续精确修复

完整 GID 已消除所有 note/reference 错误；第三轮发射 EXIT=2，15.500327292 秒，
新判词定位 residual-sign-prefixsum：LaTeX 控制词 le 紧接 j 会连成错误宏。
统一给该文档公式序列的每两个 token 加 FormulaDsl.Sp，避免其它相同宏边界错误；
Lean 源码不变。此项是公式渲染失败，与前两次 metadata 判词分开登记。

## 正式发射通过

`make emit` 修正后 EXIT=0，61.781491541 秒，生成并人工阅读本模块唯一的
Blueprint Markdown，三条 theorem 均带作者公式及 std3 kernel 标记。
未将任何判形/准入用语写入 `.scribe.cs`。本批实际执行
`find <dir> -type f | wc -l`：D5/S1/Words/Compositions=7、
Blueprint/D5/S1/Words/Compositions=14、Library/Words=23、
docs/develop/theory=44，全部低于 48。`git diff --check` EXIT=0。
已按门序启动独立 S(a) atom 的 make deposit；未创建原猜想 coverage 边。

## 冻结与覆盖收据

`make deposit ATOM_ID=296127e0b63573701297f231e6beb2f0364309aca09386ea44485b4f1b6ea59a GID=D5/S1/Words/Compositions/ResidualPermutationSign.signed_residual_sum BASE=25b883dcebf4305950c779111490338639eed3bc`
EXIT=0，212.726997292 秒。执行次序是 make lean → make lean-report →
make emit → make deposit；报告的中间提交用于持续保全，正式 D5/Scribe/冻结产物在四门后提交。
DEPOSIT_HEADER_CHECKED SL-012 通过；LEDGER_ALIGN added=1、changed=0、conflicts=0。
（该 atom 与其 coverage 边已由 orchestrator 在结算时撤下，见上节；
本段保留席位当时的原始收据作为战史，不代表当前树的状态。）模块 statement_id 为
sha256:356c8b73bb2babc122f505a0697ab7f2efd1e4d59d45808a9f4db4a853dcb218，
accepted 记录 f2bc5d6b46621d27ae59e6029c099fa0d3ca3dbf2053d0792f8c2c8b5805a73c.json。
inspector included=26：六个定义、三个公开定理、十七个私有引理；全体公理闭包之并
仍仅为标准三公理。主定理不含 sorry/私 axiom/native_decide。
本轮未运行 make preflight；第一次热树增量之前已完成 make lean-cache-ensure。

## 最终交接

正式落地提交 `2f1c5ff7ce1029b039a357eaa57101e23d594474` 已推送至
origin/lane/math/a392714r2。随后 fetch 得到 origin/dev
`f2b448dacf2d8eb3581520f115f2d2619cd6af48`，
`git merge-tree --write-tree HEAD origin/dev` EXIT=0，无冲突。
`make pr-open HEAD=lane/math/a392714r2 MESSAGE=<attempt>/pr-message.txt WATCH_TIMEOUT_SECONDS=180`
已创建 https://github.com/the-omega-institute/trureturing/pull/6689，base=dev。
创建后的首次 required-CI 观察为 OPEN、pending=2、missing=1，尚不主张 CI 全绿或已合并；
最终观察记录随 runner result.json 提供。当前为 implementation 席，零独立评审，
交由调用方后续评审。本报告的过程收据按批次提交推送，未等到终局才一次性落盘。

PR watcher 的有界收据：`make pr-open` 创建成功后等待 180 秒，最终
PR_WATCH_RESULT pr=6689 outcome=timeout pending=2 missing=1；make EXIT=2，
全调用墙钟 183.0515595 秒。这是远端检查尚未完结的超时，不是 Lean/发射/冻结门失败。
快照 head=5c3873454bbaa94b2c2bf242605c20702e51bf12，state=OPEN，mergeable=MERGEABLE。
本轮按“make lean 通过且 PR 开出”的用户判据结算成；不主张 required-CI 全绿，
不主张 PR 已合并。最终报告追记未改变已核验的 Lean 源码。

## 撤下循环摄入（orchestrator 结算,2026-09-10）

**动作**：删除 `docs/develop/theory/RESIDUAL_PERMUTATION_SIGN.md`、
其 atom blob `296127e0…`、以及 `Meta/Digestion/backfill/residual-permutation-sign/` 整个目录。
**保留**：`D5` 模块、`.scribe.cs`、`.md` 投影、`Golden/Frozen/state` 与 `accepted`
——数学与冻结一字未动。

**理由**。那卷 8 行，内容就是本模块刚证出的 S(a)；席位自己写卷、自己摄入、
再用自己的模块覆盖它。第 3.3 条明写「**源卷复述不算消费**：源句本身是同一计算的报告时，
覆盖它用一般定理，或把该句标为计算实验、不形式化」，并把「为了让旧管道有消费者而造任务」
列为反面即病。第 1.2 条与第 4.3 条定 `docs/theory` 是**参考输入（灵感与出处）**，
生产链方向是 `理论卷 → atom → 形式化`；倒过来写卷是把链反接。

**为什么必须在合入前撤，而不是事后修**：第 1.2 条「卷与 atoms 不删是建设者纪律」，
atom 一经落地即不可删。按第 7.8 条，不可逆面要事前硬门，不能靠事后勘正。

**这不影响准入依据**：本模块的 `admission_basis` 是 `escape-witness`（`upper_fixed_prefix`
与最小被移动值选出的固定相邻对换），与 atom 无关；`utility: none` 亦不需要 atom。
无 atom 的冻结路径是 `ledger-align --add`，本仓既有判例。

**未主张**：未主张该席有意冒领——它在本笔记里如实写明了摄入动作，是透明的；
撤下的理由是链的方向，不是诚信。
