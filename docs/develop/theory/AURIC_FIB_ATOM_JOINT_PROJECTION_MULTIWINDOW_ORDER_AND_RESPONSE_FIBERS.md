# Auric FIB ATOM：联合投影、多窗关系阶数与响应纤维

**Reference input: open.** 本卷完整保存三份供文的陈述、定义、证明、证明草图、表格、例子、重复说明、历史归属、总结与拟议形式化内容。原作者称为“定理”或“证明”的文字仍是 open 参考输入；Lean 声明、证明项及其公理闭包才承载本库形式系统内的数学真值，本文不认证当前 Lean/Frozen 状态、物理实现或优先权。

**来源。** 供文属 mixed supplied provenance，原始作者及原始模型均 unknown；接收时点为 2026-10-10。来源标识分别为 `joint-projection-source.md`、`multiwindow-relational-order-source.md`、`response-fiber-source.md`。下表的 SHA-256 标识接收的原始文件，正文中的来源边界标识各自完整文本的归属，不把编辑者注释归给原作者。

| 部分 | 原始供文标识 | 原始物理行数 | 原始 SHA-256 |
| --- | --- | ---: | --- |
| I 联合投影 | `joint-projection-source.md` | 1349 | `fce1a430ec465d9c5b0b011034f45589e131c7238c441c1a7e010dff60fb8f5c` |
| II 多窗关系阶数 | `multiwindow-relational-order-source.md` | 1448 | `e2dd759a14ecd006facace8f695ae8a662306c187b4f34289eb9f8c200db3b79` |
| III 响应—纤维 | `response-fiber-source.md` | 931 | `28e92da52776e1f7b13a6b990f09e46e7a31a0a87a14ab2875fa31af8e04afc3` |

**历史读法。** 供文的“当前 HEAD”“当前 dev”“最新”“本次”“本轮”“新增”及 Lean/Frozen 语言一律归属供文及其历史引用：[912f4990050451866c2bb1cf71e33151a637d4b7](https://github.com/the-omega-institute/trureturing/commit/912f4990050451866c2bb1cf71e33151a637d4b7) 与 [3a56aa49697ab7641b7dbe616e0424327c69d2ca](https://github.com/the-omega-institute/trureturing/commit/3a56aa49697ab7641b7dbe616e0424327c69d2ca)。原文链接和历史断言完整保留，不能据它们声称本文取得当前形式化证明或新颖性。给出的 Lean 文件建议只是原作者的拟议工作。

**结构规范化。** 全文只对 Markdown 层级、唯一局部地址及数学入口作结构规范化：原 `\(...\)` 改为 `$...$`，原 `\[...\]` 改为 `$$`，公式中单独成行的等号并入前一公式行以避免 setext 标题，TeX 符号及公式内容保留；代码围栏原样保存。原中文节号、原定理/定义名称与编号保留在标题及下面的对应表。每部分十二、十二、十节分别赋予本卷全局节号 1–12、13–24、25–34；这些号码是本文局部定位，不规定 Lean 名称、依赖或覆盖。

**编者限定。** 所有以“编者限定”开头的引用段均与供文原文分开，限定其支持、定义域、共同来源、观测类型、取得条件与物理解释；不会替换原句或静默修正原式。尤其第一部分原定理 4 的展开分母中 $s_j^{B_J}$ 原样保留，其与 $\pi_H(J,i)$ 定义所需 $s_i^{B_J}$ 的不一致在该定理旁单独标明。数学与物理桥接未被这些注释证明。

## 固定索引字典与局部符号类型

| 固定模式 | legacy 模式标签 | 供文数量列表 | $(x,y,z)$ |
| --- | --- | --- | --- |
| $F[\mathrm{null}]$，亦写 `F[null]` | $0$ | $\mathrm{null}$ | $(0,0,0)$ |
| $F[1]$ | $2$ | $[2]$ | $(1,0,0)$ |
| $F[2]$ | $3$ | $[3]$ | $(0,0,1)$ |
| $F[3]$ | $5$ | $[5]$ | $(0,1,0)$ |
| $F[1,3]$ | $25$ | $[2,5]$ | $(1,1,0)$ |

占位轴固定为索引 $(1,3,2)$，即低端、高端、中位及其数量 $(2,5,3)$。`25` 是联合模式的 legacy 标签，$2+5=7$ 才是相应数量和。模式索引 $F[I]$ 不等于标准 Fibonacci 数 $F_n$ 或 $\mathrm{Fib}_n$ 的下标。确定模式的占位、同一律的均值、实际取得的共同记录、模式—深度联合后验和动态来源分别有其类型与接口，本文不给它们未证的等价。

$\Phi$ 在第一部分表示概率律的联合均值映射，在第二部分表示单次闭包映射，也另有相干相位循环；$\Delta$ 是归一化四角行列式，$C(w)$ 是权重行列式，而 $C(p)$ 在谱节是三阶均值矩阵。$W$ 在静态节指闭包均值，FR 来源的同名字母另循该来源；$\Omega$ 的赔率与 $\Omega_{\mathrm{FR}}$ 的响应窗口分开。占位 $y$ 与内部动力学变量 $y$ 也仅在各自局部定义域内使用。不同部分的 $p$ 如需合并，必须是指定同一边界的实际模式律，不能拿静态先验替代条件后验。

## 部分、节号与原声明的对应

| 部分 | 原节号 | 本卷节号 | 原内容 |
| --- | --- | --- | --- |
| I | 一至十二 | 1–12 | 联合投影、四角对比、数量、计数、未来响应及模式—深度 |
| II | 一至十二 | 13–24 | 事件代数、谱恢复、双窗运输、高阶关系、祖先及物理候选 |
| III | 一至十 | 25–34 | 向量响应、纤维、未来律、深度后验及充分性边界 |

下面的地址只规范化 heading，不改变原局部名称。正文相邻“证明”标题降为所属声明的子标题，供文的粗体证明标记与完整证明保留。

| 供文与原局部节 | 原声明 | 本卷 heading 地址 |
| --- | --- | --- |
| I 原第 3 节 | 定义：FIB 闭包变量 | `definition 3.1` |
| I 原第 3 节 | 定理 1 | `theorem 3.1` |
| I 原第 4 节 | 定义：观测四角对比 | `definition 4.1` |
| I 原第 4 节 | 定理 2 | `theorem 4.1` |
| I 原第 7 节 | 定理 3 | `theorem 7.1` |
| I 原第 8 节 | 定理 4 | `theorem 8.1` |
| II 原第 2 节 | 引理 1 | `lemma 14.1` |
| II 原第 4 节 | 定理 1 | `theorem 16.1` |
| II 原第 6 节 | 定理 2 | `theorem 18.1` |
| II 原第 6 节 | 定理 3 | `theorem 18.2` |
| II 原第 8 节 | 定理 4 | `theorem 20.1` |
| III 原第 2 节 | 定义 1：模式响应向量 | `definition 26.1` |
| III 原第 3 节 | 定义 2：响应四角对比 | `definition 27.1` |
| III 原第 3 节 | 定理 1 | `theorem 27.1` |
| III 原第 4 节 | 数量守恒—闭包分叉定理 | `theorem 28.1` |
| III 原第 5 节 | 推论 1 | `corollary 29.1` |
| III 原第 6 节 | 定义 3：模式—深度联合后验 | `definition 30.1` |
| III 原第 6 节 | 定理 2 | `theorem 30.1` |
| III 原第 10 节 | 定理 A | `theorem 34.1` |
| III 原第 10 节 | 定理 B | `theorem 34.2` |
| III 原第 10 节 | 定理 C | `theorem 34.3` |

## 既有归属、文献与桥接边界

本卷的新增交付是完整三部分参考集合、局部编号对应和条件响应—纤维综合的适用说明，不宣告以下已有标量、谱、运输、奇偶或祖先结论的新证明。既有理论按其纸面论证的实际范围作为 `repo-derived` 参考；其 Lean 源码引用只定位已有声明，本文不据源码引用或供文的 Frozen 语言取得当前内核核验。

| 既有来源 | 本卷采用的范围与未越过的边界 |
| --- | --- |
| [Observer and Arithmetic Relations，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)，A-2.2–A-2.5 | `repo-derived`：归一化五态纤维、确定模式/均值的区别及标量 $J_f$ 展开已有归属；不重命名为本卷的新证明。 |
| [Foundational Formulas and Relations，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，§§2、4、7、42 | `repo-derived`：五函数及纤维、闭包矩阵与 §42.3 的同一律谱恢复已有归属；非线性谱量不是自动取得的三均值后处理。 |
| [Hidden Relations, Statistics, Phase and Seams，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)，C-12、C-16–C-17、C-21–C-22 | `repo-derived`：另供相干资源、原生守卫、端点耦合、全合法核/实际纤维维数、目标差及高阶分离已有归属；四角赔率要求非零分母，物理相干实现另供。 |
| [Determinant and Native Guard Continuation，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)，§5 | `repo-derived`：底面条件独立、未知信息及零条件质量分开；条件律要求正底面质量。 |
| [Correlation and Native Continuation，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)，§§12–13 | `repo-derived`：联合律恢复、仿射维数及高阶 native 分离分别有其域；不扩为完整观察者历史恢复。 |
| [Ancestry Cube and Acquisition Cost，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_ANCESTRY_CUBE_AND_ACQUISITION_COST.md) | `repo-derived`：有序原树、指定缺陷地址家族及祖先面积立方体已有归属；不从共同叶词推断共同括号。 |
| [Future Response Sufficiency，912f499](https://github.com/the-omega-institute/trureturing/blob/912f4990050451866c2bb1cf71e33151a637d4b7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md)，定理 34.2、推论 34.3、定理 35.1、命题 36.1–36.2 及 §37 | `repo-derived`：正整数深度与整数核、一个固定先验的实际活动历史、两点标量逆和记忆/终端边界；不是任意后验混合或模式核实现的定理。定理 34.2 的结论是 FR.34.3，不是行列式编号 FR.34.2。 |
| [JointLaw.lean，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.lean)：`native_reply_injective`、`native_probability_separation` | 既有 Lean 声明归属：已知固定长度合法 source 的精确自然数 reply；$n\ge3$、$0<\mathrm{mix}<1$ 的 lawful separation。完整分布与期望区分，正条件事件与实际初始化保留。 |
| [NullReplyFiber.lean，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.lean)：`null_reply_zero_iff` | 既有 Lean 声明归属：初始化任务追加 null 后 reply 为零当且仅当来源全 null；不扩为未知仪器的零读数判定。 |
| [NativeConditionalControl.lean，3a56aa4](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.lean)：`jointLaw`、`posterior`、`sameK_conditional_tail`、`native_first_pending` | 既有 Lean 声明归属：正整数 Depth、共同隐藏 $K$ 的条件尾部及原 pending/Stop 合同；不提供本卷另拟的五模式—深度共同实现。 |

经典中间结果的范围沿既有引用保留；有文献支持不意味着本卷三部分综合已形式化、已获得实验仪器或具有原创优先权。

| 文献归属 | 支持范围 |
| --- | --- |
| `literature-attested`：[Drton–Sullivant，Algebraic Statistical Models，arXiv:math/0703609v1](https://arxiv.org/abs/math/0703609v1)；[既有引用说明](../../../Library/Estimation/drtonsullivant2007algebraic.md)，§3.2 Example 16、Example 4 | 经典离散条件独立的交叉乘积约束和正概率比坐标；不供应 native FIB 读口、共同来源或物理实现。 |
| `literature-attested`：[De Loera–Kim，Combinatorics and Geometry of Transportation Polytopes: An Update，arXiv:1307.0124v1](https://arxiv.org/abs/1307.0124v1) | 固定边缘非负表、支撑与退化的经典运输多面体背景；特定二十一边原生域、十二核及端点分支归 C 卷，不把普通全矩形定理无条件迁移到禁止格。 |
| `literature-attested`：[Yabuta，A Simple Proof of Carmichael's Theorem on Primitive Divisors，Fibonacci Quarterly 39(5)，2001，Theorem 3](https://www.fq.math.ca/Scanned/39-5/yabuta.pdf)，pp. 441–442 | FR 来源引用的经典 Fibonacci 原始素因子供给，例外下标为 1、2、6、12；这项供给不单独证明新的模式—深度共同模型或其可实现性。 |
| `literature-attested`：[Wootters，Entanglement of Formation of an Arbitrary State of Two Qubits，quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)；[既有引用说明](../../../Library/QuantumStates/wootters1998formationfunction.md) | 明确二量子比特状态模型中的纠缠与振幅矩阵背景；不认证经典 FIB 记录为真实量子系统。 |

向量响应的四角差可在已指定共同空间内作为条件参考推导使用；真实五模式核、模式依赖 Read 历史与固定深度先验是否具有同一实现，仍须独立桥接。时钟、引力、衰变、光及相干相位的候选物理对应保持 open。本文没有 `suspected-novel` 优先权声明。

## 第一部分：联合投影与四角隐藏方向

<!-- supplied-source: joint-projection-source.md -->

### 第一部分导言：先给出本轮的核心结论

Claim status: open.（供文 I 导言及其历史归属。）

> 编者限定（I 导言）：原文的“本轮”“新推论”“当前 HEAD”及 Lean/Frozen 叙述均归属于供文及其所引历史快照；本卷保存这些措辞，不据此认证当前树、数学优先权、形式化或物理实现。下文每一陈述与证明均为 open 参考输入。


当前五态 FIB ATOM 金字塔真正遗漏的不是某个新的 Fibonacci 数，而是唯一的“四角交互方向”

$$
F[\mathrm{null}]+F[1,3]\;\longleftrightarrow\;F[1]+F[3].
$$

在概率坐标中，这个隐藏方向为

$$
d=(1,-1,0,-1,1),
$$

对应于

$$
(p_{\mathrm{null}},p_1,p_2,p_3,p_{13})
\mapsto
(p_{\mathrm{null}}+\delta,\ p_1-\delta,\ p_2,\ p_3-\delta,\ p_{13}+\delta).
$$

它保持端点占用率和中位占用率不变，却改变 $F[1,3]$ 与 $F[1],F[3]$ 之间的联合关系。

本轮最重要的新推论是：

1. 原始均值 $P=(X,Y,Z)$ 只看到三维投影，无法恢复上述隐藏方向。
2. 闭包变量

   $$
   \chi=z+xy
   $$

   的均值

   $$
   W=E[\chi]=Z+p_{13}
   $$

   正好补足唯一遗漏方向。
3. 因而联合观测

   $$
   \Phi(p)=(X,Y,Z,W)
   $$

   对五态概率分布是仿射双射；它把原来的五态单纯形完整嵌入一个四维单纯形。
4. 任意未来响应标量是否能穿透这条隐藏纤维，只由一个四角对比量

   $$
   J_f=f_{13}-f_1-f_3+f_{\mathrm{null}}
   $$

   决定。
5. 你指定的 Fibonacci 数量读出

   $$
   F[\mathrm{null}]=\mathrm{null},\quad
   F[1]=[2],\quad
   F[2]=[3],\quad
   F[3]=[5],\quad
   F[1,3]=[2,5]
   $$

   的 $J$ 恰好为零，所以数量均值本身不能恢复隐藏四角关系。
6. 当前 HEAD 新增的 §§34–37 则说明：在固定的非单例 Fibonacci 深度先验下，未来响应可以恢复 Read 计数和完整活动未来律；但这属于动态层，不能替代静态五态分布中的 $p_{13}$ 恢复。

---

### 1. 一、当前仓库进展的准确定位

Claim status: open.（供文 I 原第 1 节全文。）

> 编者限定（I.1）：此节是供文对 912f4990050451866c2bb1cf71e33151a637d4b7 和 PR #14893 的历史归属；该提交的第一父差分为所引 future-response 文档的 237 行新增。所述已有 Lean 源码与该次文档新增分别归属，未把文档证明升级为 Lean 证明。


我核对到当前工作树的 HEAD 是：

- commit：[`912f4990050451866c2bb1cf71e33151a637d4b7`](https://github.com/the-omega-institute/trureturing/commit/912f4990050451866c2bb1cf71e33151a637d4b7)
- 时间：2026-10-10 05:10（新加坡时间）
- 合并请求：PR #14893
- 相对第一父提交只新增了一份理论文档，新增 §§34–37，约 237 行，没有把旧 Lean 文件重新归因到这次提交。

新增文档是：

[RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md](https://github.com/the-omega-institute/trureturing/blob/912f4990050451866c2bb1cf71e33151a637d4b7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md)

项目主页本身把工作分成 Lean 证明、可复核实验、理论输入和开放问题，并强调“已检查结论”和“仍开放的前沿”必须分开。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

| 内容 | 当前状态 |
|---|---|
| §§34–37 的 Fibonacci 深度计数恢复 | 仓库派生的普通数学证明，依赖 Fibonacci 原始素因子定理；本次提交没有新增 Lean freeze |
| `JointLaw.lean` 中固定长度 native null continuation 注入性 | 已有 Lean/Frozen 证明源码 |
| `NullReplyFiber.lean` 中零回复纤维判定 | 已有 Lean/Frozen 证明源码 |
| 本回答中的联合投影定理、$J_f$ 判据、模式—深度交互定理 | 在现有五态结构上新推导的有限维数学结论，尚未新增 Lean 形式化 |

---

### 2. 二、五态基础代数

Claim status: open.（供文 I 原第 2 节全文。）

> 编者限定（I.2）：这里的未知量是同一五态律的统计共现，确定模式本身可由同一次样本的三个占位区分。所谓唯一核方向是在归一化差空间 $\sum_I\delta p_I=0$ 中计算；若把原始映射视为无归一化的 $\mathbb R^5\to\mathbb R^3$，核维数并非一。


令

$$
x=1_{\{1\in I\}},\qquad
y=1_{\{3\in I\}},\qquad
z=1_{\{2\in I\}},
$$

其中 $x$ 是低端点位，$y$ 是高端点位，$z$ 是中间位。

由于中间位不能和两个端点同时出现，

$$
xz=yz=0.
$$

五个状态的占用表为：

| 模式 | $(x,y,z)$ | 数量 |
|---|---:|---:|
| $F[\mathrm{null}]$ | $(0,0,0)$ | $\mathrm{null}$ |
| $F[1]$ | $(1,0,0)$ | $[2]$ |
| $F[2]$ | $(0,0,1)$ | $[3]$ |
| $F[3]$ | $(0,1,0)$ | $[5]$ |
| $F[1,3]$ | $(1,1,0)$ | $[2,5]$ |

设五态概率为

$$
p=(p_{\mathrm{null}},p_1,p_2,p_3,p_{13}),
\qquad
\sum p_I=1.
$$

定义原始占用均值

$$
X=E[x]=p_1+p_{13},
$$

$$
Y=E[y]=p_3+p_{13},
$$

$$
Z=E[z]=p_2,
$$

并令

$$
\kappa=p_{13}.
$$

于是原始概率反演为

$$
p_{\mathrm{null}}=1-X-Y-Z+\kappa,
$$

$$
p_1=X-\kappa,
$$

$$
p_2=Z,
$$

$$
p_3=Y-\kappa,
$$

$$
p_{13}=\kappa.
$$

所以，在固定 $(X,Y,Z)$ 时，所有可能分布构成一条 $\kappa$-纤维：

$$
\max(0,X+Y+Z-1)
\le \kappa \le
\min(X,Y).
$$

只要这个区间有正长度，$P=(X,Y,Z)$ 就不能唯一确定五态分布。

---

### 3. 三、联合投影横截定理

Claim status: open.（供文 I 原第 3 节全文。）

> 编者限定（I.3）：本节分别使用同一律上的占位均值、闭包均值和归一化概率。核空间解释的 $d,e$ 是归一化仿射域的差方向；横截性不把单独的 $\mathbb R^5\to\mathbb R^3$ 映射变成单射。


#### definition 3.1: 定义：FIB 闭包变量

Claim status: open.（供文 I 原第 3 节「定义」；保留纸面论证及其边界。）


定义闭包变量

$$
\chi=z+xy.
$$

这里 $xy$ 只在 $F[1,3]$ 上取值 $1$，因为 $F[1,3]$ 同时占据两个端点。

因此：

$$
\chi(F[\mathrm{null}])=0,
$$

$$
\chi(F[1])=0,
$$

$$
\chi(F[2])=1,
$$

$$
\chi(F[3])=0,
$$

$$
\chi(F[1,3])=1.
$$

设

$$
W=E[\chi]=Z+\kappa=p_2+p_{13}.
$$

这个 $W$ 不是数量 $[2,5]$，而是闭包后的关系位。它只回答一个问题：

> 当前窗口是否处在中位 $F[2]$ 或联合端点 $F[1,3]$ 这两个闭包类之一？

#### theorem 3.1: 定理 1：联合投影是四维单纯形双射

Claim status: open.（供文 I 原第 3 节「定理 1」；保留纸面论证及其边界。）

> 编者限定（I.3，原定理 1）：联合逆仅恢复同一五态静态律，并限定于五个非负逆坐标组成的可行像；仿射维数四及一个附加标量的最小性不声称取得成本、有限精度或动态历史最小性。


定义

$$
\Phi:\Delta_4\to\mathbb R^4,
\qquad
\Phi(p)=(X,Y,Z,W).
$$

则 $\Phi$ 是五态概率单纯形到其像的仿射双射。其逆为

$$
p_{13}=W-Z,
$$

$$
p_2=Z,
$$

$$
p_1=X-W+Z,
$$

$$
p_3=Y-W+Z,
$$

$$
p_{\mathrm{null}}=1-X-Y-2Z+W.
$$

##### 3.1 证明（I 原定理 1）

五个模式在 $(X,Y,Z,W)$ 中的顶点为

$$
v_{\mathrm{null}}=(0,0,0,0),
$$

$$
v_1=(1,0,0,0),
$$

$$
v_2=(0,0,1,1),
$$

$$
v_3=(0,1,0,0),
$$

$$
v_{13}=(1,1,0,1).
$$

以 $v_{\mathrm{null}}$ 为基点，其他四个差向量组成的 $4\times4$ 矩阵行列式为 $\pm1$，在上述坐标排列下为 $-1$。因此五个顶点仿射独立，$\Phi$ 在概率单纯形上是单射。

另一方面，由

$$
W-Z=p_{13}
$$

先恢复 $p_{13}$，再逐项代入

$$
X=p_1+p_{13},\qquad
Y=p_3+p_{13},\qquad
Z=p_2
$$

即可得到

$$
p_2=Z,\quad
p_1=X-W+Z,\quad
p_3=Y-W+Z.
$$

最后由概率和为 $1$ 得到

$$
p_{\mathrm{null}}
=1-p_1-p_2-p_3-p_{13}
=1-X-Y-2Z+W.
$$

证毕。

联合像的可行性等价于这些逆坐标非负，即

$$
Z\ge0,
$$

$$
W\ge Z,
$$

$$
W\le X+Z,
$$

$$
W\le Y+Z,
$$

$$
W\ge X+Y+2Z-1.
$$

因此 $W$ 正好把原始金字塔中的一维模糊纤维钉死。

---

#### 3.1 节内标题：核空间解释

原始投影

$$
p\mapsto(X,Y,Z)
$$

的核由

$$
d=(1,-1,0,-1,1)
$$

生成，因为

$$
\sum d_I=0,
\qquad
\Delta X=\Delta Y=\Delta Z=0.
$$

闭包投影

$$
p\mapsto(X,Y,W)
$$

的核由

$$
e=(2,-1,-1,-1,1)
$$

生成，因为

$$
\sum e_I=0,
\qquad
\Delta X=\Delta Y=\Delta W=0.
$$

而

$$
\operatorname{span}(d)\cap \operatorname{span}(e)=\{0\}.
$$

所以原始占用投影与闭包投影是横截的：

$$
\ker(P)\cap\ker(Q)=\{0\}.
$$

这就是“原始 FIB 金字塔”和“partition closure”之间最关键的线性关系：两者各自丢失一个方向，但丢失的方向不同；把它们的共享端点坐标合在一起，信息恰好完整。

---

### 4. 四、单个附加观测何时足够

Claim status: open.（供文 I 原第 4 节全文。）


#### definition 4.1: 定义：观测四角对比

Claim status: open.（供文 I 原第 4 节「定义」；保留纸面论证及其边界。）


任取一个五态标量观测 $f$，记

$$
f_{\mathrm{null}},f_1,f_2,f_3,f_{13}
$$

为它在五个模式上的值。

定义四角对比

$$
J_f =
f_{13}-f_1-f_3+f_{\mathrm{null}}.
$$

#### theorem 4.1: 定理 2：单标量补全判据

Claim status: open.（供文 I 原第 4 节「定理 2」；保留纸面论证及其边界。）

> 编者限定（I.4，原定理 2）：此判据在正宽度纤维上区分恢复和恒定；边界纤维塌成单点时 $J_f=0$ 仍可唯一。在整个五态单纯形上，增广仿射观测的全局单射与这一退化局部情形分开。


任意五态分布满足

$$
E[f] =
f_{\mathrm{null}}
+(f_1-f_{\mathrm{null}})X
+(f_3-f_{\mathrm{null}})Y
+(f_2-f_{\mathrm{null}})Z
+J_f\kappa.
$$

在具有正宽度的内部 $\kappa$-纤维上，已知 $(X,Y,Z)$ 后：

- 若 $J_f\neq0$，则 $E[f]$ 唯一恢复 $\kappa$，从而恢复完整五态分布；
- 若 $J_f=0$，则 $E[f]$ 在整条 $\kappa$-纤维上恒定，无法恢复完整分布。

##### 4.1 证明（I 原定理 2）

将

$$
p_{\mathrm{null}}=1-X-Y-Z+\kappa,
\quad
p_1=X-\kappa,
\quad
p_2=Z,
\quad
p_3=Y-\kappa,
\quad
p_{13}=\kappa
$$

代入

$$
E[f]=\sum_I p_I f_I
$$

得到

$$
\begin{aligned}
E[f]
={}&f_{\mathrm{null}}(1-X-Y-Z+\kappa)
+f_1(X-\kappa)\\
&+f_2Z+f_3(Y-\kappa)+f_{13}\kappa.
\end{aligned}
$$

整理 $\kappa$ 的系数，正好得到

$$
f_{\mathrm{null}}-f_1-f_3+f_{13}
=J_f.
$$

因此

$$
E[f]=\text{已知的可见项}+J_f\kappa.
$$

若 $J_f\neq0$，直接解出 $\kappa$；若 $J_f=0$，则 $E[f]$ 不依赖 $\kappa$。证毕。

从线性代数看，给 $(X,Y,Z)$ 再加一行 $E[f]$，消去前三个可见方向后，最后一行只剩 $J_f$ 乘以隐藏坐标；所以增广矩阵满秩当且仅当 $J_f\neq0$。

---

#### 4.1 节内标题：数量读出为什么看不到隐藏关系

数量值是

$$
q_{\mathrm{null}}=0,\qquad
q_1=2,\qquad
q_2=3,\qquad
q_3=5,\qquad
q_{13}=7.
$$

因此

$$
J_q=7-2-5+0=0.
$$

代入定理 2：

$$
E[q]=2X+5Y+3Z.
$$

所以数量读出完全落在

$$
\operatorname{span}\{1,x,y,z\}
$$

中，没有 $xy$ 分量。它可以看到：

- 低端点的边际占用；
- 高端点的边际占用；
- 中位占用；

但不能看到：

- $F[1,3]$ 是否相对于 $F[1]$ 与 $F[3]$ 被额外联合增强；
- 四角关系的符号；
- $p_{13}$ 的具体值。

例如两组分布

$$
p^-=(0.1,0.3,0.2,0.3,0.1),
$$

$$
p^+=(0.3,0.1,0.2,0.1,0.3)
$$

都有

$$
X=Y=0.4,\qquad Z=0.2,
$$

因此都有

$$
E[q]=2(0.4)+5(0.4)+3(0.2)=3.4.
$$

但它们的隐藏参数分别为

$$
\kappa^-=0.1,\qquad \kappa^+=0.3.
$$

对应的底部行列式

$$
\Delta=p_{\mathrm{null}}p_{13}-p_1p_3
$$

分别为

$$
\Delta^-=-0.08,
\qquad
\Delta^+=0.08.
$$

数量均值相同，隐藏相位却相反。

相反，闭包观测 $\chi=z+xy$ 的五态值为

$$
(0,0,1,0,1),
$$

于是

$$
J_\chi=1-0-0+0=1.
$$

因此

$$
E[\chi]=Z+\kappa=W
$$

正好是恢复隐藏方向所需的最小一维附加观测。

---

### 5. 五、计数版本：联合观测是 unimodular 的

Claim status: open.（供文 I 原第 5 节全文。）

> 编者限定（I.5）：整数逆式在整数计数坐标及其可行像上解释，减法不是自然数截断减法；同一总数 $m$ 也是输入。四维仿射完整性和一个附加线性标量的必要性不等于最少样本、比特、取得成本或物理仪器最优性。误差式要求其余三个均值精确，并按所述同一纤维比较。


设总样本数为 $m$，五态计数为

$$
(n_{\mathrm{null}},n_1,n_2,n_3,n_{13}).
$$

记录三种原始占用计数和一个闭包计数：

$$
N_X=n_1+n_{13},
$$

$$
N_Y=n_3+n_{13},
$$

$$
N_Z=n_2,
$$

$$
N_W=n_2+n_{13}.
$$

则有整数级精确逆：

$$
n_{13}=N_W-N_Z,
$$

$$
n_2=N_Z,
$$

$$
n_1=N_X-N_W+N_Z,
$$

$$
n_3=N_Y-N_W+N_Z,
$$

$$
n_{\mathrm{null}}
=m-N_X-N_Y-2N_Z+N_W.
$$

这里的整数矩阵行列式为 $-1$，所以这是 unimodular 变换：

- 不需要除法；
- 不产生分母；
- 不产生整数舍入；
- 计数版比概率版更适合 Lean 形式化。

这也解释了为什么

$$
N_W-N_Z=n_{13}
$$

是一个非常自然的仪器设计：闭包计数减去原中位计数，直接读出联合端点 $F[1,3]$ 的出现次数。

若 $P$ 精确而 $W$ 有误差 $\delta$，则重构误差沿隐藏方向移动：

$$
\delta p =
(\delta,-\delta,0,-\delta,\delta)
=\delta d.
$$

因此

$$
\|\delta p\|_1=4|\delta|,
\qquad
\operatorname{TV}=\frac12\|\delta p\|_1=2|\delta|.
$$

这说明 $W$ 不是任意增加一个坐标，而是正好沿着原始投影看不见的方向补测。

---

### 6. 六、未来响应本身的四角判据

Claim status: open.（供文 I 原第 6 节全文。）

> 编者限定（I.6）：未来标量须由同一个合法未来事件合同定义，模式条件响应固定，期望使用该边界上的实际模式律。只给不同来源的五个数，不能认定它们已属于同一可实现的未来实验。


上面的 $f_I$ 不必是静态物理量，也可以是某个未来事件的模式条件概率。

例如，给每个模式 $F[I]$ 一个未来事件响应值

$$
r_I=P(\text{未来事件}\mid F[I]).
$$

令

$$
J_r=r_{13}-r_1-r_3+r_{\mathrm{null}}.
$$

则

$$
E_p[r] =
r_{\mathrm{null}}
+(r_1-r_{\mathrm{null}})X
+(r_3-r_{\mathrm{null}})Y
+(r_2-r_{\mathrm{null}})Z
+J_r\kappa.
$$

于是：

- $J_r=0$：该未来标量只看到原始金字塔投影；
- $J_r\neq0$：该未来标量能够穿透 $\kappa$-纤维；
- 多个未来标量只要至少有一个 $J_r\neq0$，就足以补出 $\kappa$。

这给出一个比“未来响应是否充分”更精细的判据：

> 未来响应是否能恢复隐藏关系，不取决于它看起来是否复杂，而取决于它是否含有 $F[1,3]$ 相对于 $F[1]$、$F[3]$、$F[\mathrm{null}]$ 的非零四角对比。

---

### 7. 七、局部主效应不会凭空创造隐藏交互

Claim status: open.（供文 I 原第 7 节全文。）


定义未归一化五态权重

$$
w=(w_{\mathrm{null}},w_1,w_2,w_3,w_{13}).
$$

定义四角行列式

$$
C(w)=w_{\mathrm{null}}w_{13}-w_1w_3.
$$

当总权为 $Z_w=\sum_Iw_I$ 时，概率版行列式为

$$
\Delta(p)=\frac{C(w)}{Z_w^2}.
$$

#### theorem 7.1: 定理 3：主效应更新下隐藏交互的相对不变量

Claim status: open.（供文 I 原第 7 节「定理 3」；保留纸面论证及其边界。）

> 编者限定（I.7，原定理 3）：乘积主效应似然是另加假设，不因一个操作名为 Read 而成立。普通赔率 $\Omega(w)$ 及其更新要求 $w_1w_3\ne0$；非负权重模型中这要求两者均正，归一化还要求总权正。行列式恒等式本身不需对零单元取商。


假设某段历史 $H$ 对五个模式的似然具有局部主效应形式：

$$
\ell_I(H) =
\lambda
u^{x(I)}
v^{y(I)}
t^{z(I)}
$$

其中 $\lambda,u,v,t>0$。

则更新后的权重满足

$$
C(w') =
\lambda^2uv\,C(w).
$$

因此：

1. $C(w)$ 的零性和符号保持；
2. 概率行列式 $\Delta$ 的零性和符号保持；
3. 四角赔率

   $$
   \Omega(w) =
   \frac{w_{\mathrm{null}}w_{13}}{w_1w_3}
   $$

   完全不变。

##### 7.1 证明（I 原定理 3）

五个模式的似然分别为

$$
\ell_{\mathrm{null}}=\lambda,
$$

$$
\ell_1=\lambda u,
$$

$$
\ell_2=\lambda t,
$$

$$
\ell_3=\lambda v,
$$

$$
\ell_{13}=\lambda uv.
$$

所以

$$
w'_{\mathrm{null}}=\lambda w_{\mathrm{null}},
$$

$$
w'_1=\lambda u w_1,
$$

$$
w'_3=\lambda v w_3,
$$

$$
w'_{13}=\lambda uv w_{13}.
$$

于是

$$
\begin{aligned}
C(w')
&=w'_{\mathrm{null}}w'_{13}-w'_1w'_3\\
&=(\lambda w_{\mathrm{null}})
(\lambda uvw_{13})
-(\lambda uw_1)(\lambda vw_3)\\
&=\lambda^2uv
(w_{\mathrm{null}}w_{13}-w_1w_3)\\
&=\lambda^2uvC(w).
\end{aligned}
$$

同理，

$$
\Omega(w') =
\frac{(\lambda w_{\mathrm{null}})
(\lambda uvw_{13})}
{(\lambda uw_1)(\lambda vw_3)}
=\Omega(w).
$$

证毕。

这说明，如果初始分布处于乘积完成面

$$
\Delta=0,
$$

那么只含局部主效应的 Read 历史不会凭空生成四角交互。

如果似然额外包含一个真正的联合因子

$$
\eta^{xy},
$$

那么只有 $F[1,3]$ 的权重多出 $\eta$，从而

$$
\Omega'=\eta\Omega.
$$

这才是隐藏 seam 被仪器主动注入或测量的通道。

---

### 8. 八、模式与隐藏 Fibonacci 深度的耦合定理

Claim status: open.（供文 I 原第 8 节全文。）

> 编者限定（I.8）：这里另行假定共同的模式—深度联合模型、同一次运行保留同一个隐藏 $K$、固定深度先验与所示乘积似然。不同模式的计数是否来自同一合法历史接口，仍是桥接义务；静态 law、原始先验与条件历史后的后验模式质量不可互换。


当前 HEAD §§34–35 的新内容可以进一步和五态模式结合。

令隐藏 Fibonacci 深度为 $K$，并定义

$$
r_k=\frac{\mathrm{Fib}_{k+1}}{\mathrm{Fib}_{k+3}},
\qquad
s_k=\frac{\mathrm{Fib}_{k+2}}{\mathrm{Fib}_{k+3}},
\qquad
r_k+s_k=1.
$$

设模式 $I$ 和深度 $k$ 的联合后验未归一化权重具有形式

$$
\pi_H(I,k)
\propto
p_I\mu_k\,c_I\,r_k^{A_I}s_k^{B_I},
$$

其中：

- $p_I$ 是五态模式先验；
- $\mu_k$ 是隐藏深度先验；
- $c_I>0$ 是与深度无关的模式因子；
- $A_I,B_I$ 是历史 $H$ 在模式 $I$ 下诱导的两类 Read 计数。

#### theorem 8.1: 定理 4：模式—深度独立性的刚性判据

Claim status: open.（供文 I 原第 8 节「定理 4」；保留纸面论证及其边界。）

> 编者限定（I.8，原定理 4）：参与交叉比须有 $p_I,p_J,\mu_i,\mu_j,c_I,c_J>0$，两个不同正整数深度 $i,j$ 和非负整数 Read 计数 $A_I,B_I$，故指数差是整数。独立性只约束正概率模式；零质量模式不能靠取消零因子识别计数。所引是 FR 定理 34.2，其整数核结论编号为 FR.34.3，FR.34.2 则是 Fibonacci 行列式恒等式编号。下方原展开式的分母最后一项印作 $p_J\mu_i c_J r_i^{A_J}s_j^{B_J}$，依其定义的 $\pi_H(J,i)$ 应为 $p_J\mu_i c_J r_i^{A_J}s_i^{B_J}$；此索引不一致作为显式原文勘误保留，原式不静默更正，后续定理仍为 open 参考论证。


假设隐藏深度先验至少包含两个不同的正支持点 $i\neq j$。则对任意两个模式 $I,J$，模式与深度的后验交互赔率为

$$
\Xi_{I,J;i,j} =
\frac{\pi_H(I,i)\pi_H(J,j)}
{\pi_H(I,j)\pi_H(J,i)}
$$

并满足

$$
\Xi_{I,J;i,j} =
\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
\left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
$$

进一步，若

$$
\Xi_{I,J;i,j}=1
$$

对所有模式对 $I,J$ 都成立，则

$$
A_I=A_J,\qquad B_I=B_J.
$$

因此：

> 在至少两个 Fibonacci 深度同时有正概率时，模式 $I$ 与隐藏深度 $K$ 后验独立，当且仅当五个模式的 $(A_I,B_I)$ 完全相同。

##### 8.1 证明（I 原定理 4）

将联合后验代入交互赔率：

$$
\begin{aligned}
\Xi_{I,J;i,j}
&=
\frac{
p_I\mu_i c_I r_i^{A_I}s_i^{B_I}
\cdot
p_J\mu_j c_J r_j^{A_J}s_j^{B_J}
}{
p_I\mu_j c_I r_j^{A_I}s_j^{B_I}
\cdot
p_J\mu_i c_J r_i^{A_J}s_j^{B_J}
}\\
&=
\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
\left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
\end{aligned}
$$

当前 HEAD §§34–35 中的定理 34.2 给出：

$$
\left(\frac{r_i}{r_j}\right)^u
\left(\frac{s_i}{s_j}\right)^v=1
\quad\Longrightarrow\quad
u=v=0
$$

对所有 $i\neq j$ 和整数 $u,v$ 成立。

将

$$
u=A_I-A_J,\qquad
v=B_I-B_J
$$

代入，即得

$$
A_I-A_J=0,\qquad B_I-B_J=0.
$$

反方向显然成立。证毕。

这个结果揭示了另一个隐藏关系：

- $\kappa$ 是五态模式内部的四角交互；
- $(A_I,B_I)$ 差异是模式与隐藏深度之间的交互；
- 前者由 $J_f$ 或 $\Delta$ 检测；
- 后者由 $\Xi_{I,J;i,j}$ 检测。

因此，静态 FIB 金字塔和动态 Fibonacci 深度并不是两个互不相关的变量层。只要不同模式经历不同的 Read 计数，它们就会产生可计算的后验耦合。

---

### 9. 九、如何接入当前 §§34–35 的未来响应结果

Claim status: open.（供文 I 原第 9 节全文。）

> 编者限定（I.9）：FR §§34–35 的恢复限定于一个已安装且固定的先验、至少两个不同正整数深度的正支持、实际正概率有限历史、活动第四段、原合法接口及精确响应。单标量恢复限定于两点支持，并非任意混合后验、未知先验或有限精度的稳定逆。相位、活计数、chronology、selected-count bank、隐藏样本 $K$ 以及 active/pending0/pending1/delivered 各有不同的记录或权限；提出的 $(P,W,\text{phase},\text{boundary})$ 不是未指定联合来源的自动充分状态。


当前提交 §§34–37 的主要结论可以压缩成下面的形式。

对固定的非单例深度先验，令

$$
\Omega_{\mathrm{FR}}(h) =
(D_h(1),D_h(2))
$$

表示文档中的两维未来响应窗口。则在活动第四段历史上：

$$
\nu_h=\nu_{h'}
\Longleftrightarrow
(A_h,B_h)=(A_{h'},B_{h'}),
$$

并且

$$
\Omega_{\mathrm{FR}}(h) =
\Omega_{\mathrm{FR}}(h')
$$

等价于：

- 隐藏深度后验相同；
- 已支付 Read 计数 $(A,B)$ 相同；
- 当前 phase 相同；
- 完整合法剩余未来律相同。

这是一项重要的动态充分性结果，但必须满足：

1. 先验已经固定；
2. 支持至少包含两个正深度；
3. 历史位于活动第四段；
4. 响应值是精确值；
5. 使用原始合法接口；
6. 不能把 pending、delivered 和 active 混成同一个状态。

文档还给出了两点支持时的单标量恢复。定义

$$
f_k=\frac{r_k}{1-r_k+r_k^2},
\qquad
g_k=\frac{r_k^2}{1-r_k+r_k^2}.
$$

若当前 phase 为 $p$，则

$$
q_{\mathrm{FR}}(h) =
\nu_h(i)f_i+\nu_h(j)f_j.
$$

若当前 phase 为 $\beta$，则

$$
q_{\mathrm{FR}}(h) =
\nu_h(i)g_i+\nu_h(j)g_j.
$$

两个 phase 的响应区间不相交，因此精确的 $q_{\mathrm{FR}}$ 可以先恢复 phase，再恢复后验，最后通过

$$
x=
\frac{\nu_h(j)/\nu_h(i)}
{\mu_j/\mu_i} =
\left(\frac{r_j}{r_i}\right)^A
\left(\frac{s_j}{s_i}\right)^B
$$

恢复整数计数 $A,B$。

这说明动态未来响应的逻辑顺序应当是：

$$
\text{精确响应}
\to
\text{phase}
\to
\text{posterior}
\to
\text{Read counts}
\to
\text{future law}.
$$

而静态五态层的逻辑顺序是：

$$
(P,W)
\to
\kappa
\to
p_{\mathrm{null}},p_1,p_2,p_3,p_{13}.
$$

两条链不能互相替代。更准确地说，应当使用：

$$
(P,W,\text{phase},\text{boundary})
$$

作为动态未来预测的输入。若还要恢复实际观察者的完整记忆，则还需要：

- chronology；
- selected-count bank；
- 已交付或待交付的 Stop 标签；
- 其他由接口明确声明并实际持有的记录。

---

### 10. 十、Lean 中已存在的两个重要边界结果

Claim status: open.（供文 I 原第 10 节全文。）

> 编者限定（I.10）：所引 native_reply_injective 以已知固定长度、合法初始化来源和实际追加 null 为域，读数是精确自然数 reply；单次 reply、reply 的完整概率律与其一阶期望是三种观察，亦不推出未知长度、模数或噪声解码。proper seam 条件报告须有正条件质量，分别保存的边缘报告不等于共同配对样本档案。非交换式是解释性简写，除非另行给出两边可组合的算子、定义域及边缘对象上的 continuation。


当前仓库已有的 Lean 文件：

- [`JointLaw.lean`](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.lean)
- [`NullReplyFiber.lean`](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.lean)

给出了两类与本轮分析直接相关的结果。

#### 10.1 节内标题：1. 固定长度 native null continuation 的注入性

对固定长度 $n$ 的合法窗口串 $w$，在末尾追加一个 null continuation 后，精确自然数 reply

$$
R_n(w)
$$

是单射。

证明结构是：

1. 组成坐标经过固定的 Fibonacci 变换得到整数；
2. 追加 null 后得到等长的 Zeckendorf 型无相邻 $1$ 编码；
3. 精确 reply 等于该编码的 Fibonacci 值；
4. 固定长度 canonical representation 的唯一性恢复整串编码；
5. 三位窗口编码逐位恢复原始 $w$。

这个结论不与“数量均值看不到 $\kappa$”冲突。两者观察对象不同：

- 精确单次 native reply 是高阶、固定长度、整数值的完整编码；
- $E[q]$ 是五态分布上的一阶期望；
- 一次精确编码可以单射，并不意味着对应的一阶均值能恢复所有混合分布。

#### 10.2 节内标题：2. 局部边缘和线性前缀矩不决定完整未来

`JointLaw.lean` 中已有的概率分离定理构造了两种 full-support 概率律 $P_+$ 与 $P_-$，使得：

- 所有 proper coordinate marginals 相同；
- 所有 proper seam-conditioned marginals 相同；
- 所有固定线性 prefix readout 的期望相同；
- 总体 exact reply expectation 也相同；

但 native null continuation 的完整 reply 分布不同。

其核心是 parity law：

$$
P_\varepsilon(b) =
2^{-n}\bigl(1+\varepsilon(-1)^{b_1+\cdots+b_n}\bigr)
$$

的所有低阶边缘相同，而全局 parity 不同。`NullReplyFiber.lean` 进一步给出：

$$
\mathrm{reply}(w)=0
\Longleftrightarrow
w\text{ 全部为 null}.
$$

所以全零纤维的概率在 $P_+$ 和 $P_-$ 下不同，native future 立即分离。

这给出一个必须保留的非交换性：

$$
\text{先做局部边缘化，再做 continuation}
\neq
\text{先做完整 continuation，再做边缘化}.
$$

因此，不能从“所有局部报告都一致”直接推出“完整未来律一致”。

---

### 11. 十一、对 Auric FIB ATOM 金字塔的分层结论

Claim status: open.（供文 I 原第 11 节全文。）

> 编者限定（I.11）：“最小仿射完备”仅针对五态静态律及允许的仿射读数类别，不认证动态来源、取得接口或全体观察者历史的充分性。


目前可以把系统分成四层。

#### 11.1 节内标题：层 0：数量层

$$
F[\mathrm{null}],F[1],F[2],F[3],F[1,3]
\mapsto
\mathrm{null},[2],[3],[5],[2,5].
$$

数量均值只看到

$$
2X+5Y+3Z.
$$

它对 $\kappa$ 完全盲。

#### 11.2 节内标题：层 1：原始占用金字塔

$$
P=(X,Y,Z).
$$

它比数量层多恢复了端点和中位的边际占用，但仍丢失

$$
d=(1,-1,0,-1,1).
$$

#### 11.3 节内标题：层 2：FIB/partition closure

加入

$$
W=E[z+xy]=Z+\kappa.
$$

于是

$$
(P,W)
$$

完整恢复五态分布。

#### 11.4 节内标题：层 3：动态未来和观察者记忆

即使 $p$ 完整恢复，完整未来还可能依赖：

- hidden depth；
- phase；
- active/pending/delivered 边界；
- chronology；
- selected-count bank；
- native continuation 的高阶关系。

所以正确的最小性陈述应当是：

> $(P,W)$ 是五态静态 law 的最小仿射完备观测；它不是所有动态未来和观察者历史的自动完备观测。

---

### 12. 十二、下一步最值得形式化的三个定理

Claim status: open.（供文 I 原第 12 节全文。）

> 编者限定（I.12）：本节的文件名、代码围栏和形式化顺序完整保留为供文建议，均是 open 的拟议目标，不是本卷已完成的 Lean 工作或本卷发出的实施指令。


建议按以下顺序推进 Lean，而不是立即把整个动态观察者合同一次性编码。

#### 12.1 节内标题：1. `JointProjection.lean`

定义五态结构：

```text
F[null], F[1], F[2], F[3], F[1,3]
```

定义

```text
X = p1 + p13
Y = p3 + p13
Z = p2
W = p2 + p13
```

形式化证明：

```text
p13 = W - Z
p2  = Z
p1  = X - W + Z
p3  = Y - W + Z
p0  = 1 - X - Y - 2Z + W
```

并证明该变换的整数矩阵行列式为 $-1$。

#### 12.2 节内标题：2. `ResponseContrast.lean`

对任意五态函数 $f$，证明：

$$
E[f] =
\text{visible}(X,Y,Z)+J_f\kappa.
$$

然后证明：

```text
J_f ≠ 0  ↔  (X,Y,Z,E[f]) injective on the simplex
```

其中必须明确限定：

- 全体分布恢复；
- 或者存在正宽度的内部纤维。

边界退化纤维上，即使 $J_f=0$，也可能因为纤维宽度为零而唯一。

#### 12.3 节内标题：3. `ModeDepthCrossRatio.lean`

把当前 FR.34.2 的 Fibonacci 深度刚性与五态模式结合，证明：

$$
\Xi_{I,J;i,j}=1
\Longleftrightarrow
(A_I,B_I)=(A_J,B_J).
$$

这会把“静态四角交互”和“动态模式—深度交互”放进同一个后验赔率框架中。

---

最终，Auric FIB ATOM 金字塔的基础关系可以压缩成一句精确的话：

$$
\boxed{
\text{数量层看见 composition，}
\quad
\text{占用层看见边际，}
\quad
\text{闭包层看见四角交互，}
\quad
\text{未来层看见深度与边界。}
}
$$

而你指定的五个基本元素

$$
F[\mathrm{null}],\ F[1],\ F[2],\ F[3],\ F[1,3]
$$

之间最基本的隐藏关系，就是

$$
\boxed{
F[\mathrm{null}]+F[1,3]
-
F[1]-F[3]
}
$$

所代表的唯一四角方向；它的数值读出为零，但它的闭包读出为一。
<!-- end-supplied-source: joint-projection-source.md -->

## 第二部分：从单窗隐藏回路到多窗关系阶数

<!-- supplied-source: multiwindow-relational-order-source.md -->

### 第二部分导言：续篇：从单窗隐藏回路到多窗关系阶数

Claim status: open.（供文 II 导言及其历史归属。）

> 编者限定（II 导言）：续篇中“当前 dev”“最新”指供文所引 3a56aa49697ab7641b7dbe616e0424327c69d2ca 的历史材料。本卷保留组合论断和物理桥接全文；两者的纸面论证或候选解释均不在这里获得形式化、物理或优先权认证。


当前 `dev` 的最新理论文件已经把 Auric FIB ATOM 金字塔推进到了一个更清晰的层级：

$$
\boxed{
\text{五态选择}
\;\longrightarrow\;
\text{单窗统计纤维}
\;\longrightarrow\;
\text{双窗运输循环}
\;\longrightarrow\;
\text{多窗高阶关系}
\;\longrightarrow\;
\text{原树祖先纤维}
\;\longrightarrow\;
\text{相干相位与内部动态}
}
$$

相关最新文件包括：

- [AURIC FIB ATOM Pyramid Foundational Formulas and Relations](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)
- [AURIC FIB ATOM Hidden Relations, Statistics, Phase and Seams](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)
- [AURIC FIB ATOM Pyramid Determinant and Native Guard Continuation](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)
- [AURIC FIB ATOM Pyramid Correlation and Native Continuation](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)
- [AURIC FIB ATOM Ancestry Cube and Acquisition Cost](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_ANCESTRY_CUBE_AND_ACQUISITION_COST.md)

这些文件仍然明确标记为 `repo-derived` 或 `Claim status: open`。因此下面分为两层：

1. 在有限组合模型中可以直接证明的定理；
2. 由这些定理提出的物理桥接，不能直接冒充物理定律。

---

### 13. 一、先修正一个类型问题：单次模式本身并没有隐藏

Claim status: open.（供文 II 原第 1 节全文。）

> 编者限定（II.1）：确定模式的共同样本记录与三个分别均值是不同类型的观察；本节的区别不提供取得共同样本记录的新接口。


继续使用你的记号：

$$
F[\mathrm{null}]=\mathrm{null},
$$

$$
F[1]=[2],
$$

$$
F[2]=[3],
$$

$$
F[3]=[5],
$$

$$
F[1,3]=[2,5].
$$

定义三个单次模式函数：

$$
x(I)=\mathbf 1_{1\in I},
$$

$$
y(I)=\mathbf 1_{3\in I},
$$

$$
z(I)=\mathbf 1_{2\in I}.
$$

于是五种模式的坐标是：

$$
\begin{array}{c|c}
\text{模式}&(x,y,z)\\
\hline
F[\mathrm{null}]&(0,0,0)\\
F[1]&(1,0,0)\\
F[2]&(0,0,1)\\
F[3]&(0,1,0)\\
F[1,3]&(1,1,0)
\end{array}
$$

合法性关系为：

$$
xz=0,
\qquad
yz=0.
$$

注意：

$$
I\longmapsto(x(I),y(I),z(I))
$$

在单次样本上是单射。也就是说，如果同一次事件中 $x,y,z$ 被完整记录，那么五种模式可以直接区分。

真正产生隐藏自由度的是统计投影：

$$
p\longmapsto(X,Y,Z) =
\left(
\mathbb E[x],
\mathbb E[y],
\mathbb E[z]
\right),
$$

因为它只保留三个分别的平均值，忘掉了同一次样本中 $x$ 与 $y$ 是否同时出现。

这一区分很重要：

$$
\boxed{
\text{单次模式没有隐藏}
}
$$

而：

$$
\boxed{
\text{单次共现记录被丢弃后，统计分布出现隐藏纤维}
}
$$

因此，$\kappa$ 不是每个原子内部必然存在的“神秘粒子”，而是一个观察投影的核坐标。

---

### 14. 二、五态事件代数的唯一隐藏基元

Claim status: open.（供文 II 原第 2 节全文。）


考虑有限代数：

$$
\mathcal A =
\mathbb R[x,y,z]\Big/
\left(
x^2-x,\,
y^2-y,\,
z^2-z,\,
xz,\,
yz
\right).
$$

其中：

$$
x^2=x,\qquad y^2=y,\qquad z^2=z
$$

表示三个指标都是布尔变量，而：

$$
xz=yz=0
$$

表示中间模式 $F[2]$ 不能与两个端点模式同时出现。

#### lemma 14.1: 引理 1：五态代数的函数基

Claim status: open.（供文 II 原第 2 节「引理 1」；保留纸面论证及其边界。）

> 编者限定（II.2，原引理 1）：五函数基及单窗纤维已有所引 A 卷 A-2.2–A-2.5、基础公式卷及 C 卷的对应叙述；此处保留供文商代数论证，不重新宣告已有结果的新证明或形式化。


$$
\boxed{
\{1,x,y,z,xy\}
}
$$

构成 $\mathcal A$ 的一组基。

**证明。**

由于 $x^2=x$、$y^2=y$、$z^2=z$，任意高次幂都可以降为一次幂。由于 $xz=yz=0$，所有同时含有 $z$ 与 $x$ 或 $y$ 的项都消失。唯一保留下来的乘积项是：

$$
xy.
$$

因此任意函数都可写成：

$$
f =
a_0+a_1x+a_2y+a_3z+a_{13}xy.
$$

五个模式上的函数空间维数为五，所以这五个函数构成基。证毕。

五个模式的指示函数为：

$$
e_{\mathrm{null}} =
1-x-y-z+xy,
$$

$$
e_1=x-xy,
$$

$$
e_2=z,
$$

$$
e_3=y-xy,
$$

$$
e_{13}=xy.
$$

其中：

$$
e_{13}=xy
$$

明确说明：

$$
F[1,3]
$$

就是唯一的端点联合项。

如果概率律为：

$$
p=
(p_{\mathrm{null}},p_1,p_2,p_3,p_{13}),
$$

则：

$$
X=\mathbb E[x]=p_1+p_{13},
$$

$$
Y=\mathbb E[y]=p_3+p_{13},
$$

$$
Z=\mathbb E[z]=p_2,
$$

$$
\kappa=\mathbb E[xy]=p_{13}.
$$

因此：

$$
\boxed{
\kappa
}
$$

不是额外任意参数，而是五态函数代数中唯一未被一阶边缘读数覆盖的基方向。

---

### 15. 三、分区闭合：$z+xy$ 是第五个结构变量

Claim status: open.（供文 II 原第 3 节全文。）

> 编者限定（II.3）：这里 $\Phi$ 作用于单次合法占位，第一部分的 $\Phi$ 则作用于概率律。二者有明确的同一五态对应，但不是同一类型的函数；$c=z+xy$ 与其均值 $W$ 也须区分。


定义：

$$
a=x,
\qquad
b=y,
\qquad
c=z+xy.
$$

由于合法状态中 $z$ 与 $xy$ 不会同时为 1，所以：

$$
c\in\{0,1\}.
$$

于是得到变换：

$$
\boxed{
\Phi(x,y,z)=(a,b,c)=(x,y,z+xy).
}
$$

其逆变换为：

$$
\boxed{
x=a,\qquad y=b,\qquad z=c-ab.
}
$$

因为在合法状态上：

$$
xy=ab.
$$

五个模式对应：

$$
\begin{array}{c|c}
\text{模式}&(a,b,c)\\
\hline
F[\mathrm{null}]&(0,0,0)\\
F[1]&(1,0,0)\\
F[3]&(0,1,0)\\
F[2]&(0,0,1)\\
F[1,3]&(1,1,1)
\end{array}
$$

这个坐标把五态结构写成：

$$
\boxed{
\text{两个端点联合项 }xy
\text{ 与中间项 }z
\text{ 合并为一个闭合关系变量 }c.
}
$$

这解释了为什么第五个模式不是普通的“第三个单点”：

- $F[1]$ 是左端关系；
- $F[3]$ 是右端关系；
- $F[2]$ 是中间关系；
- $F[1,3]$ 是端点共同关系；
- $z+xy$ 把中间关系与端点联合关系放入同一个五态闭合坐标。

这也是项目中把五种模式与三元素分区结构联系起来的原因。

---

### 16. 四、新的谱读出定理：额外一个二阶量即可恢复 $\kappa$

Claim status: open.（供文 II 原第 4 节全文。）


仅有：

$$
(X,Y,Z)
$$

不能恢复：

$$
\kappa.
$$

但如果增加一个由五态关系构造出的谱量，则可以恢复它。

定义矩阵：

$$
C(p)=
\begin{pmatrix}
1&X&Y\\
X&1&Z+\kappa\\
Y&Z+\kappa&1
\end{pmatrix}.
$$

其中：

$$
Z+\kappa =
\mathbb E[z+xy] =
\mathbb E[c].
$$

定义：

$$
M_2=\operatorname{tr}\left(C(p)^2\right).
$$

直接计算：

$$
\boxed{
M_2 =
3+2\left(
X^2+Y^2+(Z+\kappa)^2
\right).
}
$$

#### theorem 16.1: 定理 1：谱二阶矩恢复隐藏联合坐标

Claim status: open.（供文 II 原第 4 节「定理 1」；保留纸面论证及其边界。）

> 编者限定（II.4，原定理 1）：这里 $M_2=\operatorname{tr}((\sum_Ip_I C_I)^2)$ 是同一律的均值矩阵的非线性量，一般不同于 $\mathbb E_p[\operatorname{tr}(C_I^2)]$。它作为新观测另行给定，不能仅从 $(X,Y,Z)$ 产生；逆式要求精确可行输入及非负根，也不自动实现仪器或噪声稳定性。相同谱恢复已归基础公式卷 §42.3。


给定 $(X,Y,Z)$ 和 $M_2$，在合法概率单纯形上可以唯一恢复 $\kappa$：

$$
\boxed{
\kappa =
\sqrt{
\frac{M_2-3}{2}-X^2-Y^2
}
-Z.
}
$$

**证明。**

由定义：

$$
M_2 =
3+2\left(
X^2+Y^2+(Z+\kappa)^2
\right).
$$

整理：

$$
(Z+\kappa)^2 =
\frac{M_2-3}{2}-X^2-Y^2.
$$

由于：

$$
Z+\kappa\ge0,
$$

必须取非负平方根：

$$
Z+\kappa =
\sqrt{
\frac{M_2-3}{2}-X^2-Y^2
}.
$$

因此：

$$
\kappa =
\sqrt{
\frac{M_2-3}{2}-X^2-Y^2
}
-Z.
$$

证毕。

这给出一个重要的读出设计原则：

$$
\boxed{
\text{隐藏关系不一定要逐格读取，也可以通过额外谱不变量恢复。}
}
$$

但是 $M_2$ 是新读出。它不是从 $(X,Y,Z)$ 自动产生的。

在固定边界纤维上，若两个概率律对应 $\kappa_p,\kappa_q$，则：

$$
\Delta M_2 =
2(\kappa_p-\kappa_q)
\left(
2Z+\kappa_p+\kappa_q
\right).
$$

因此：

$$
\left|\Delta M_2\right|
\ge
2|\kappa_p-\kappa_q|^2.
$$

又因为：

$$
\|p-q\|_1=4|\kappa_p-\kappa_q|,
$$

所以当 $Z>0$ 时：

$$
\boxed{
Z\|p-q\|_1
\le
|\Delta M_2|.
}
$$

中间模式 $F[2]$ 的存在因此提供了谱恢复的稳定性。

---

### 17. 五、$\Delta=0$ 不等于观察者已经知道 $\kappa$

Claim status: open.（供文 II 原第 5 节全文。）

> 编者限定（II.5）：条件底面独立和最大熵候选 $\kappa^\star=XY/(1-Z)$ 需要 $r=1-Z>0$。若 $r=0$，全部质量在 $F[2]$，没有底面条件律或该商；零质量的交叉乘积等式不创造条件分布。$\Delta=0$ 是真实律的性质，只有另加该性质作为假设才可用其选择纤维中的律。


定义：

$$
r=1-Z,
$$

$$
\Delta=r\kappa-XY.
$$

$\Delta=0$ 表示实际底面条件独立：

$$
L\perp R\mid z=0.
$$

但这不表示 $\kappa$ 已经能从 $(X,Y,Z)$ 中恢复。

举一个最简单的例子：五个模式均匀分布：

$$
p_{\mathrm{null}} =
p_1 =
p_2 =
p_3 =
p_{13} =
\frac15.
$$

则：

$$
X=Y=\frac25,
$$

$$
Z=\frac15,
$$

$$
r=\frac45,
$$

$$
\kappa=\frac15.
$$

于是：

$$
\Delta =
\frac45\cdot\frac15
-
\frac25\cdot\frac25 =
0.
$$

但固定的 $(X,Y,Z)$ 允许：

$$
0\le\kappa\le\frac25.
$$

所以：

$$
\boxed{
\text{实际关联为零}
\neq
\text{观察者能够由三均值证明关联为零}.
}
$$

这一区分对应两个不同概念：

- **law property**：真实概率律满足 $\Delta=0$；
- **identifiability**：观察记录是否足以确定真实的 $\kappa$。

最大熵补全：

$$
\kappa^\star=\frac{XY}{r}
$$

只是从纤维中选择的一份特殊概率律。它不是由三均值唯一推出的真实历史。

---

### 18. 六、双窗口不是一个接缝比特，而是一个十二维循环空间

Claim status: open.（供文 II 原第 6 节全文。）

> 编者限定（II.6）：本节原生顺序是 HIGH-to-LOW，第一窗低端占位 $x(i)$ 与第二窗高端占位 $y(j)$ 的守卫为 $x(i)y(j)=0$。记号 $(x,y,z)$ 对应索引 $(1,3,2)$；印字次序 $(x,z,y)$ 与读入次序 $(y,z,x)$ 不可因轴重排而交换这个有向守卫。


原生高到低方向的双窗口守卫为：

$$
\boxed{
x(i)y(j)=0.
}
$$

这里：

- $x(i)=1$ 表示第一窗口含有 $F[1]$ 或 $F[1,3]$；
- $y(j)=1$ 表示第二窗口含有 $F[3]$ 或 $F[1,3]$。

定义：

$$
\mathcal R_1 =
\{F[1],F[1,3]\},
$$

$$
\mathcal C_1 =
\{F[3],F[1,3]\}.
$$

合法双窗口集合为：

$$
\mathcal E =
(\Sigma\times\Sigma)
\setminus
(\mathcal R_1\times\mathcal C_1),
$$

其中：

$$
\Sigma =
\left\{
F[\mathrm{null}],F[1],F[2],F[3],F[1,3]
\right\}.
$$

因为共有 $5\times5=25$ 个有序对，非法块有 $2\times2=4$ 个，所以：

$$
\boxed{
|\mathcal E|=21.
}
$$

令双窗口联合律为 $P_{ij}$，第一窗口边缘为 $\mu_i$，第二窗口边缘为 $\nu_j$。

定义：

$$
a=\sum_{i\in\mathcal R_1}\mu_i,
$$

$$
b=\sum_{j\in\mathcal C_1}\nu_j.
$$

#### theorem 18.1: 定理 2：双窗边缘的存在条件

Claim status: open.（供文 II 原第 6 节「定理 2」；保留纸面论证及其边界。）

> 编者限定（II.6，原定理 2）：原商式分支要求 $a,b<1$。端点 $a=1$ 由可行性强制 $b=0$，仅在 $\mathcal R_1\times\mathcal C_0$ 取 $P_{ij}=\mu_i\nu_j$；端点 $b=1$ 对称地在 $\mathcal R_0\times\mathcal C_1$ 取该乘积，其余格零。不得给 $0/0$ 赋值；$a+b=1$ 且 $a,b<1$ 时余块质量 $c=0$。这些端点分支复用 C 卷 C-16.2，原文分式完整保留。


存在满足守卫条件的双窗口联合律，当且仅当：

$$
\boxed{
a+b\le1.
}
$$

**证明。**

$a$ 是第一窗口要求第二窗口处于 $\mathcal C_0$ 的概率，$b$ 是第二窗口要求第一窗口处于 $\mathcal R_0$ 的概率。两种限制必须在同一个联合样本中同时满足，因此必须有足够的非冲突质量：

$$
1-a-b\ge0.
$$

反过来，当 $a+b\le1$ 时，可以构造如下联合律。令：

$$
c=1-a-b.
$$

非法块取零：

$$
P_{ij}^\star=0,
\qquad
i\in\mathcal R_1,\ j\in\mathcal C_1.
$$

其余四个块取：

$$
P_{ij}^\star =
\frac{\mu_i\nu_j}{1-b},
\qquad
i\in\mathcal R_1,\ j\in\mathcal C_0,
$$

$$
P_{ij}^\star =
\frac{\mu_i\nu_j}{1-a},
\qquad
i\in\mathcal R_0,\ j\in\mathcal C_1,
$$

$$
P_{ij}^\star =
\frac{c\,\mu_i\nu_j}{(1-a)(1-b)},
\qquad
i\in\mathcal R_0,\ j\in\mathcal C_0.
$$

逐行逐列求和即可恢复 $\mu_i,\nu_j$。因此条件也是充分的。证毕。

这说明“最大熵补全”不能简单写成两个窗口的独立乘积。独立乘积可能把质量放入非法的：

$$
\mathcal R_1\times\mathcal C_1
$$

块中。

---

#### theorem 18.2: 定理 3：双窗口固定边缘后有 12 个独立隐藏循环

Claim status: open.（供文 II 原第 6 节「定理 3」；保留纸面论证及其边界。）

> 编者限定（II.6，原定理 3）：十二是全部二十一合法边的线性边缘映射的核维数。非负固定边缘纤维在边缘严格正且 $a+b<1$ 时有此维数；正边缘但 $a+b=1$ 时实际可用图为 $K_{2,3}\sqcup K_{3,2}$，维数四。零边缘、端点或确定性边缘应按整个可行纤维的可用支持图求维数，可能为零；不能用一个稀疏顶点的支持替代整个纤维。归属见 C 卷 C-17.2–C-17.3。


合法联合律空间有 21 个坐标。归一化后维数为：

$$
21-1=20.
$$

边缘约束的独立秩为：

$$
5+5-1=9.
$$

固定两侧边缘后，联合律的隐藏维数为：

$$
20-(9-1)=12.
$$

因此：

$$
\boxed{
\dim\ker(\text{双窗边缘映射})=12.
}
$$

这些隐藏方向可由四角循环生成：

$$
D^{ij} =
E_{ij}+E_{00}-E_{i0}-E_{0j},
$$

其中四个格点都必须是合法格点，$0$ 表示选定的参考模式，例如：

$$
F[\mathrm{null}].
$$

任意两个拥有相同左右边缘的双窗口联合律之差，都可以写成：

$$
P'-P =
\sum_{i,j}\lambda_{ij}D^{ij}.
$$

因此：

$$
\boxed{
\kappa
\text{ 只是单窗口底面上的一维循环；}
}
$$

$$
\boxed{
\text{真实双窗口接缝具有十二个独立循环方向。}
}
$$

这也是为什么只保存每个窗口自己的：

$$
(X,Y,Z)
$$

以及一个接缝比特，仍然可能丢失跨窗口联合历史。

---

### 19. 七、一个实际原生继续反例：相同局部律，不同未来

Claim status: open.（供文 II 原第 7 节全文。）

> 编者限定（II.7）：条件拒绝例要求同一已取得的粗事件 $A$、$Y+Z>0$ 及继续读取 $F[3]$ 的同一原生守卫；在该事件内只有 $F[1,3]$ 触发拒绝。相同粗报告不表示观察者已持有共同配对档案，也不表示可操控真实 $\kappa$。


定义两个五模式概率律，按顺序：

$$
\left(
F[\mathrm{null}],
F[1],
F[2],
F[3],
F[1,3]
\right)
$$

取：

$$
p^-=
(0.1,0.3,0.2,0.3,0.1),
$$

$$
p^+=
(0.3,0.1,0.2,0.1,0.3).
$$

两者都有：

$$
X=0.4,
$$

$$
Y=0.4,
$$

$$
Z=0.2.
$$

但：

$$
\kappa^-=0.1,
\qquad
\kappa^+=0.3.
$$

因此：

$$
\Delta^-=
0.8\cdot0.1-0.4\cdot0.4 =
-\frac{2}{25},
$$

$$
\Delta^+=
0.8\cdot0.3-0.4\cdot0.4 =
\frac{2}{25}.
$$

两者的粗奇偶记录也可以相同。令：

$$
A=
\{F[2],F[3],F[1,3]\}.
$$

则：

$$
p^-(A)=0.2+0.3+0.1=0.6,
$$

$$
p^+(A)=0.2+0.1+0.3=0.6.
$$

设：

$$
m=Y+Z=0.6.
$$

在实际继续规则下，粗记录 $A$ 之后再继续读取固定模式 $F[3]$，拒绝事件的条件概率为：

$$
\Pr(\bot\mid A)=\frac{\kappa}{Y+Z}.
$$

因此：

$$
\Pr_{p^-}(\bot\mid A)=\frac16,
$$

$$
\Pr_{p^+}(\bot\mid A)=\frac12.
$$

而条件独立补全给出的预测是：

$$
\kappa^\star=\frac{XY}{r} =
\frac{0.4\cdot0.4}{0.8} =
0.2,
$$

所以：

$$
\Pr^\star(\bot\mid A)=\frac13.
$$

这给出一个真正的动态结论：

$$
\boxed{
\text{相同 }(X,Y,Z)
+
\text{相同粗接缝记录}
\not\Rightarrow
\text{相同未来继续律}.
}
$$

隐藏的 $\kappa$ 会在未来的守卫返回中重新出现。

---

### 20. 八、任意固定阶局部统计都可能遗漏更高阶全局关系

Claim status: open.（供文 II 原第 8 节全文。）


双窗口有 12 个循环，多窗口还会继续增加关系阶数。

当前项目进一步给出了如下结构性结果：

#### theorem 20.1: 定理 4：所有真子集边缘相同，不保证未来相同

Claim status: open.（供文 II 原第 8 节「定理 4」；保留纸面论证及其边界。）

> 编者限定（II.8，原定理 4）：所引 native_probability_separation 在已初始化的合法固定长度来源上要求 $n\ge3$ 和 $0<\mathrm{mix}<1$；“全支撑”是该合法来源域的全支撑，proper seam 条件事件还要求正质量。这是既有源码与 C 卷高阶分离的适用范围，不认证任意新动态来源。


对任意 $n\ge3$，存在两个全支撑概率律：

$$
P_n^+,\qquad P_n^-,
$$

使得它们在所有严格真子集上的联合边缘完全相同，但在追加一个合法的：

$$
F[\mathrm{null}]
$$

之后，实际终值分布不同。

构造思想是取一个全局奇偶差异：

$$
\mu_n^+-\mu_n^-,
$$

它在任何低于 $n$ 阶的边缘投影下都抵消，但在完整 $n$-项关系上保留非零值。再把它混入统一的合法背景分布，就可以得到全支撑的 $P_n^\pm$。

这说明：

$$
\boxed{
\text{所有局部低阶边缘相同}
\not\Rightarrow
\text{全局未来相同}.
}
$$

换言之：

$$
\text{关系阶数}
$$

本身会随着窗口数量增加。

这不是说必须永远保存完整原始历史，而是说：

$$
\boxed{
\text{任何有限摘要都必须相对于指定未来任务证明充分性。}
}
$$

---

### 21. 九、祖先关系是另一种完全不同的隐藏层

Claim status: open.（供文 II 原第 9 节全文。）

> 编者限定（II.9）：祖先断言的对象是指定的有序原树、$n\ge3$ 的缺陷家族和互不嵌套替换地址；叶词、括号、来源深度及面积向量各是不同读口，不能由占位概率或静态 $\kappa$ 直接恢复。所引祖先立方体归已有祖先卷，不作为本卷新证明或物理来源认证。


统计联合关系还没有涉及原始 FIB 树的括号。

原始树为：

$$
\mathbb T::=\alpha\mid\beta\mid\langle\mathbb T,\mathbb T\rangle,
$$

$$
\rho(\alpha)=\beta,
$$

$$
\rho(\beta)=\langle\beta,\alpha\rangle.
$$

取：

$$
B=
\left\langle
\langle\beta,\alpha\rangle,\beta
\right\rangle =
T_3,
$$

$$
D=
\left\langle
\beta,\langle\alpha,\beta\rangle
\right\rangle.
$$

则：

$$
w(B)=w(D)=\beta\alpha\beta,
$$

但：

$$
\nu(B)=3,
\qquad
\nu(D)=0.
$$

因此：

$$
\boxed{
\text{共同出现关系}
\neq
\text{共同祖先关系}.
}
$$

对 $T_n$，含有三叶块 $B$ 的互不嵌套地址数为：

$$
K_n=\mathrm{Fib}_{n-2}.
$$

在任意子集 $A$ 上把 $B$ 替换成 $D$，得到 $V_A$。则：

$$
w(V_A)=w(T_n),
$$

但：

$$
\nu(V_A) =
\begin{cases}
n,&A=\varnothing,\\
0,&A\neq\varnothing.
\end{cases}
$$

所以同一个叶词可以拥有：

$$
2^{\mathrm{Fib}_{n-2}}
$$

个不同原树。

这个结果说明，以下读数都可能不足以恢复括号：

- 叶标签数量；
- 叶词；
- 由叶词计算的线性组成；
- 结合律下的矩阵乘积；
- 低阶路径面积；
- 单窗口 $\kappa$。

要恢复祖先，需要新的读口，例如祖先面积向量：

$$
\mathcal A(t) =
(\mathcal A_1(t),\ldots,\mathcal A_{m-1}(t)).
$$

最新祖先卷给出：

$$
\mathcal A(V_A)-\mathcal A(T_n) =
\sum_{p\in A}
(e_{i_p}-e_{i_p+1}),
$$

并且：

$$
\left\|
\mathcal A(V_A)-\mathcal A(V_{A'})
\right\|_2^2 =
2|A\triangle A'|.
$$

这形成了一个真正的祖先关系立方体。

---

### 22. 十、如果加入相干层，还会出现隐藏相位 $\Phi$

Claim status: open.（供文 II 原第 10 节全文。）

> 编者限定（II.10）：振幅矩阵另行假定 $r=1-Z>0$、归一化纯二量子比特实现及允许的局部相位标架；四个相位循环的解释需要四个正振幅和共同相位参考。经典五概率本身不供给该纯态、干涉端口或物理纠缠。纯态矩阵中的 $\det A=0$ 条件不能不加状态类型地应用于经典对角混合态或任意混合量子态。


概率 $\kappa$ 和行列式 $\Delta$ 只描述经典概率关系。如果允许端点记录具有相干振幅，还要加入相位。

定义：

$$
A=
\frac1{\sqrt r}
\begin{pmatrix}
\sqrt{p_{\mathrm{null}}}e^{i\theta_0}
&
\sqrt{p_3}e^{i\theta_3}
\\
\sqrt{p_1}e^{i\theta_1}
&
\sqrt{p_{13}}e^{i\theta_{13}}
\end{pmatrix}.
$$

剩余规范不变量为：

$$
\boxed{
\Phi =
\theta_0+\theta_{13}-\theta_1-\theta_3
\pmod{2\pi}.
}
$$

则：

$$
\boxed{
\begin{aligned}
r^2|\det A|^2
={}&
\left(
\sqrt{p_{\mathrm{null}}p_{13}}
-
\sqrt{p_1p_3}
\right)^2
\\
&+
4\sqrt{
p_{\mathrm{null}}p_1p_3p_{13}
}
\sin^2\frac{\Phi}{2}.
\end{aligned}
}
$$

因此：

- $\Delta$ 描述概率幅度之间的关联；
- $\Phi$ 描述相干相位之间的关联；
- 仅知道五个概率 $p_s$，不能恢复 $\Phi$；
- 要恢复 $\Phi$，必须有相干干涉或共同相位参考。

在正支撑条件下：

$$
\det A=0
$$

需要同时满足：

$$
\Delta=0,
\qquad
\Phi=0.
$$

所以：

$$
\boxed{
\Delta=0
\text{ 仍不等于完全无纠缠或完全可分。}
}
$$

它只说明概率底面表满足条件独立；相位还可能保留额外的量子关系。

---

### 23. 十一、当前 Auric FIB ATOM 的隐藏关系层级

Claim status: open.（供文 II 原第 11 节全文。）

> 编者限定（II.11）：各层的纤维分别属于统计律、有向接缝、全局联合、原树及另供相干或动力学模型；同一个“隐藏”称呼不构成共同来源或可操作性等价的证明。


综合当前 `dev`，最清晰的分层是：

#### 23.1 节内标题：$L_0$：原生单次选择

$$
\Sigma_F =
\left\{
F[\mathrm{null}],
F[1],
F[2],
F[3],
F[1,3]
\right\}.
$$

合法性：

$$
xz=yz=0.
$$

单次模式本身可以被 $(x,y,z)$ 完全区分。

#### 23.2 节内标题：$L_1$：单窗统计投影

$$
p\longmapsto(X,Y,Z).
$$

唯一隐藏回路：

$$
(1,-1,0,-1,1).
$$

补充坐标：

$$
\kappa
\quad\text{或}\quad
\Delta.
$$

#### 23.3 节内标题：$L_2$：双窗运输

守卫：

$$
x_i y_{i+1}=0.
$$

合法联合空间：

$$
|\mathcal E|=21.
$$

固定边缘后的循环维数：

$$
12.
$$

#### 23.4 节内标题：$L_3$：多窗高阶关系

所有低阶边缘可能相同，但最高阶奇偶关系不同。随着窗口数增加，需要更高阶的混合矩或完整继续律。

#### 23.5 节内标题：$L_4$：原树来源关系

叶词和数量会忘掉括号。需要：

$$
\nu,\quad e,\quad\mathcal A(t)
$$

等祖先读口。

#### 23.6 节内标题：$L_5$：相干关系

概率 $p_s$ 之外，还存在：

$$
\Phi
$$

这样的相位回路。

#### 23.7 节内标题：$L_6$：内部动态关系

若加入内部变量 $y$，则：

$$
m\dot y=\sum_i c_i u_i-Cy
$$

提供局部记忆、衰变和边界输出。

因此，隐藏关系不是一个单独的“隐藏物质变量”，而是每次观察投影留下的核：

$$
\boxed{
\text{隐藏关系} =
\text{投影映射的非平凡纤维}.
}
$$

---

### 24. 十二、与“时间、引力、衰变、光”的桥接

Claim status: open.（供文 II 原第 12 节全文。）

> 编者限定（II.12）：本节及其最后三个物理方框全部是候选模型定义或假设，状态 $s$、引力样场 $\Gamma$、时钟增量、内部动力学、衰变和光通道须另给同一物理实现、单位、动作/测量接口及可区分的经验预测。合法未来有方向、记录被投影丢弃或有限概率代数，均不自行建立物理时间、引力、衰变、光或不可逆性；这些桥接保持 open。


在这个结构中，你提出的直觉可以被精确翻译为：

$$
\text{时间方向} =
\text{从当前状态出发的合法未来锥}.
$$

一个局部观察者状态可以写成：

$$
s=(I,h,a,\Phi,y).
$$

其中：

- $I$ 决定当前局部模式；
- $h$ 决定接缝合法性；
- $a$ 保存祖先或括号信息；
- $\Phi$ 保存相干关系；
- $y$ 保存内部动态记忆。

局部时钟可以定义为路径泛函：

$$
\boxed{
\tau_\Gamma[\gamma] =
\sum_j
\delta_\Gamma(s_j,s_{j+1}),
}
$$

其中 $\Gamma$ 是一个待定义的引力样局部场。

在这个表达中：

- 引力不必先被看成外部坐标；
- 它可以先被看成对合法转移权重或局部变化率的调制；
- 时间不是全局钟，而是每条路径上的累计变化；
- 衰变是内部记忆向外部输出通道的转移；
- 光可以被定义为离开内部闭合子系统后的边界记录；
- 信息不可恢复意味着观察投影仍存在非平凡纤维。

但必须保持类型区分：

$$
\boxed{
\kappa,\Delta,\Phi,h,\nu,y
}
$$

不是同一个物理量。

它们分别属于：

$$
\text{统计联合},
\quad
\text{条件关联},
\quad
\text{相干相位},
\quad
\text{接缝记忆},
\quad
\text{祖先结构},
\quad
\text{内部动力学}.
$$

真正的统一理论需要证明某个更高层的状态变量能够同时生成它们，而不是直接把它们命名成“时间”或“引力”。

目前最稳固的统一命题是：

$$
\boxed{
\text{时间箭头来自合法未来的方向性，}
}
$$

$$
\boxed{
\text{衰变来自内部关系向观察边界的不可逆投影，}
}
$$

$$
\boxed{
\text{光是外部可取得的输出通道，}
}
$$

$$
\boxed{
\text{而 Auric FIB ATOM 金字塔是识别这些关系纤维的最小局部读出结构。}
}
$$

<!-- end-supplied-source: multiwindow-relational-order-source.md -->

## 第三部分：响应—纤维与模式—深度桥接

<!-- supplied-source: response-fiber-source.md -->

### 第三部分导言

Claim status: open.（供文 III 导言及其历史归属。）

> 编者限定（III 导言）：这里“本轮真正的新结论”保留为供文作者措辞；原始作者/模型未知，现有相似标量结果与原生 continuation 结果仍归其已有来源。本部分收集的是条件响应—纤维综合，不宣告新的优先权、已实现统一来源或新 Lean 证明。

这一步继续向前推进：把前一轮的静态隐藏坐标 $\kappa=p_{13}$，与当前项目最新的 Fibonacci 深度后验、native continuation 和 future law 合并成一个统一的“响应—纤维”理论。

当前仓库的主线仍然是：用明确的定义和可复核证明区分“读数恢复了什么”和“信息还在哪里逸出”。仓库主页也明确把 Lean 证明、理论输入、有限实验和开放义务分开处理。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com) 当前 HEAD 是 [`912f4990050451866c2bb1cf71e33151a637d4b7`](https://github.com/the-omega-institute/trureturing/commit/912f4990050451866c2bb1cf71e33151a637d4b7)，PR #14893 的新增内容集中在 future-response 文档 §§34–37；这些新增结论是仓库派生的普通数学证明，不能误称为本次提交新增的 Lean 定理。

本轮真正的新结论是：

> 原始 FIB ATOM 金字塔的隐藏方向 $\kappa$，不是静态层和动态层各自独立的两个问题。它们通过“未来响应向量的四角对比”连接起来。  
> 对任何未来响应，只要它在 $F[1,3]$ 上相对于 $F[1]$、$F[3]$、$F[\mathrm{null}]$ 产生非零四角差，它就能够穿透 $\kappa$-纤维；否则整条 $\kappa$-纤维会在该未来响应下继续保持不可区分。

---

### 25. 一、从五态静态 law 到未来响应向量

Claim status: open.（供文 III 原第 1 节全文。）

> 编者限定（III.1）：本节的 $p$ 是同一边界上的五态模式律。把静态先验与经过模式依赖历史后的模式后验互换，会改变期望和纤维的对象。


仍然使用你指定的五态记号：

$$
F[\mathrm{null}]=\mathrm{null},
$$

$$
F[1]=[2],
$$

$$
F[2]=[3],
$$

$$
F[3]=[5],
$$

$$
F[1,3]=[2,5].
$$

设五态概率为

$$
p=
(p_{\mathrm{null}},p_1,p_2,p_3,p_{13}).
$$

仍定义

$$
x=1_{\{1\in I\}},
\qquad
y=1_{\{3\in I\}},
\qquad
z=1_{\{2\in I\}}.
$$

五个状态的取值为：

| 状态 | $x$ | $y$ | $z$ |
|---|---:|---:|---:|
| $F[\mathrm{null}]$ | 0 | 0 | 0 |
| $F[1]$ | 1 | 0 | 0 |
| $F[2]$ | 0 | 0 | 1 |
| $F[3]$ | 0 | 1 | 0 |
| $F[1,3]$ | 1 | 1 | 0 |

原始占用均值为

$$
X=E[x]=p_1+p_{13},
$$

$$
Y=E[y]=p_3+p_{13},
$$

$$
Z=E[z]=p_2.
$$

隐藏参数为

$$
\kappa=p_{13}.
$$

于是

$$
p_{\mathrm{null}}=1-X-Y-Z+\kappa,
$$

$$
p_1=X-\kappa,
$$

$$
p_2=Z,
$$

$$
p_3=Y-\kappa,
$$

$$
p_{13}=\kappa.
$$

因此，固定 $P=(X,Y,Z)$ 后，完整分布仍沿一条一维纤维变化：

$$
p(\kappa) =
(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
$$

---

### 26. 二、未来响应的向量化定义

Claim status: open.（供文 III 原第 2 节全文。）

> 编者限定（III.2）：概率律本身构成凸集而非实向量空间；若 $L_I$ 是概率律，应放入共同可测未来域上的有限有符号测度空间，在该环境中作四角差。五个模式须共享同一事件、合法协议及终端职责合同，且变化混合律时保持模式核 $L_I$ 固定；各模式合法未来域不同时，需要明确共同域的实现与合法性编码。


上一轮只讨论了一个标量 $E[f]$。现在把它推广到完整 future law。

#### definition 26.1: 定义 1：模式响应向量

Claim status: open.（供文 III 原第 2 节「定义 1」；保留纸面论证及其边界。）


令 $\mathcal V$ 是一个实向量空间。它可以是：

- $\mathbb R$，表示一个标量概率；
- $\mathbb R^m$，表示有限个未来事件的联合响应；
- 所有合法未来事件的函数空间；
- 概率测度组成的线性空间。

给每个五态模式一个响应向量：

$$
L_{\mathrm{null}},\quad
L_1,\quad
L_2,\quad
L_3,\quad
L_{13}
\in\mathcal V.
$$

对混合分布 $p$，定义平均响应

$$
\overline L(p) =
p_{\mathrm{null}}L_{\mathrm{null}}
+p_1L_1
+p_2L_2
+p_3L_3
+p_{13}L_{13}.
$$

如果 $L_I$ 是完整未来概率律，那么 $\overline L(p)$ 就是五态混合后的完整 future law。

---

### 27. 三、响应—纤维定理

Claim status: open.（供文 III 原第 3 节全文。）

> 编者限定（III.3）：“信息逃逸维数”指归一化五态仿射域的差空间和固定响应核，不是无约束 $\mathbb R^5$ 的核或任意非负边界纤维的维数。单点边界纤维中即使 $J_L=0$ 也已唯一；正宽度纤维上的必要充分性及整个单纯形上的增广单射须分开陈述。


#### definition 27.1: 定义 2：响应四角对比

Claim status: open.（供文 III 原第 3 节「定义 2」；保留纸面论证及其边界。）


定义

$$
J_L =
L_{13}-L_1-L_3+L_{\mathrm{null}}
\in\mathcal V.
$$

这个 $J_L$ 是标量 $J_f$ 的向量版本。

当 $\mathcal V=\mathbb R$ 时，它退化为

$$
J_f=f_{13}-f_1-f_3+f_{\mathrm{null}}.
$$

#### theorem 27.1: 定理 1：未来响应的纤维分解定理

Claim status: open.（供文 III 原第 3 节「定理 1」；保留纸面论证及其边界。）

> 编者限定（III.3，原定理 1）：五个 $L_I$ 须固定在同一实向量空间或共同未来域的有符号测度空间中，$p$ 是该边界的当前实际模式律。在此条件下讨论沿 $J_L$ 的实标量差，不是除以一个向量，也不是从先验与后验的不同核间直接转移注入性。


对任意模式响应向量 $L_I$，有

$$
\begin{aligned}
\overline L(p)
={}&
L_{\mathrm{null}}
+(L_1-L_{\mathrm{null}})X\\
&+(L_3-L_{\mathrm{null}})Y
+(L_2-L_{\mathrm{null}})Z
+J_L\kappa.
\end{aligned}
$$

因此，在原始占用均值 $P=(X,Y,Z)$ 固定时：

1. 若

   $$
   J_L\neq0,
   $$

   则 $\overline L(p)$ 能够唯一恢复 $\kappa$；

2. 若

   $$
   J_L=0,
   $$

   则 $\overline L(p)$ 在整条 $\kappa$-纤维上恒定，任何仅依赖该响应的未来预测都无法区分这条纤维中的不同分布。

##### 27.1 证明（III 原定理 1）

将

$$
p_{\mathrm{null}}=1-X-Y-Z+\kappa,
$$

$$
p_1=X-\kappa,\qquad
p_2=Z,\qquad
p_3=Y-\kappa,\qquad
p_{13}=\kappa
$$

代入

$$
\overline L(p)=\sum_Ip_IL_I.
$$

得到

$$
\begin{aligned}
\overline L(p)
={}&
(1-X-Y-Z+\kappa)L_{\mathrm{null}}\\
&+(X-\kappa)L_1
+ZL_2
+(Y-\kappa)L_3
+\kappa L_{13}.
\end{aligned}
$$

整理后得到

$$
\begin{aligned}
\overline L(p)
={}&L_{\mathrm{null}}
+(L_1-L_{\mathrm{null}})X\\
&+(L_3-L_{\mathrm{null}})Y
+(L_2-L_{\mathrm{null}})Z\\
&+\kappa
(L_{13}-L_1-L_3+L_{\mathrm{null}}).
\end{aligned}
$$

最后一项就是 $J_L\kappa$。

如果 $J_L\neq0$，则在向量空间中沿 $J_L$ 的方向可以唯一解出 $\kappa$。

如果 $J_L=0$，则 $\overline L(p)$ 完全不含 $\kappa$，因此所有具有相同 $(X,Y,Z)$ 的分布都产生相同响应。证毕。

---

#### 27.1 节内标题：信息逃逸维数的精确形式

原始占用观测 $P$ 的隐藏方向是

$$
d=(1,-1,0,-1,1).
$$

对这条方向，未来响应的变化为

$$
\delta\overline L =
J_L\delta.
$$

因此：

$$
\dim\ker(P,\overline L) =
\begin{cases}
0,&J_L\neq0,\\
1,&J_L=0.
\end{cases}
$$

这把“信息逃逸”从直觉变成了一个秩判据：

- $J_L=0$：响应仍然保留一维不可辨识纤维；
- $J_L\neq0$：响应补足最后一个静态缺失方向。

这也给出一个与仓库 information-escape 思路一致的严格版本：一个新读数是否真正减少不可辨识状态，不看它形式上多复杂，只看它是否在当前核方向上产生非零变化。

---

### 28. 四、静态闭包只是未来响应的一种特殊情况

Claim status: open.（供文 III 原第 4 节全文。）

> 编者限定（III.4）：数量加法与闭包差都在同一个五态函数域解释；$J_q=0$ 仅否定此一阶期望读数的辨识力，不否定精确原生 reply 或完整 reply 分布的辨识力。


定义闭包变量

$$
\chi=z+xy.
$$

五个模式上的取值为

$$
\chi=
(0,0,1,0,1).
$$

因此

$$
J_\chi =
1-0-0+0
=1.
$$

其均值为

$$
W=E[\chi]=Z+\kappa.
$$

所以静态闭包坐标的响应四角对比为非零：

$$
J_\chi=1.
$$

这说明联合坐标

$$
(X,Y,Z,W)
$$

能够恢复完整五态分布。

而 Fibonacci 数量响应

$$
q=
(0,2,3,5,7)
$$

满足

$$
J_q=7-2-5+0=0.
$$

因此

$$
E[q]=2X+5Y+3Z
$$

无法穿透 $\kappa$-纤维。

这可以被称为：

#### theorem 28.1: 数量守恒—闭包分叉定理

Claim status: open.（供文 III 原第 4 节「数量守恒—闭包分叉定理」；保留纸面论证及其边界。）

> 编者限定（III.4，原数量守恒—闭包分叉定理）：这是供文未编号的标题；这里只给它唯一局部地址并保持陈述全文。已有标量四角展开仍归 A-2.4–A-2.5，此处加法读数的应用不宣告优先权。


任何满足

$$
q(F[\mathrm{null}])=0,
$$

$$
q(F[1,3])=q(F[1])+q(F[3])
$$

的 additive quantity，都有

$$
J_q=0.
$$

因此，这类 quantity 的期望只能看到边际占用，不能看到端点共同激活。

只有引入一个非加法 seam 变量，例如

$$
\chi(F[1,3])\neq
\chi(F[1])+\chi(F[3]),
$$

才能离开原始可见子空间

$$
\operatorname{span}\{1,x,y,z\}.
$$

---

### 29. 五、把当前 future law 接入四角判据

Claim status: open.（供文 III 原第 5 节全文。）

> 编者限定（III.5）：将 FR 接入这里仍须给出同一实际来源与未来合同；计数注入性或模式响应彼此不同，均不推出四角 $J_{\mathscr L}\ne0$。在后文联合模型中，历史后的模式混合质量为 $\widehat p_H(I)\propto p_I c_I\sum_k\mu_k r_k^{A_I}s_k^{B_I}$，一般不是原先验 $p_I$。应以当前实际模式律混合相应的条件未来核，再按其均值讨论纤维；该共同实现及非零四角响应保持 open 桥接义务。


现在考虑最新文档 §§34–35 中的 future response。

设某个固定 phase 下，历史 $h$ 已经诱导出两个 Read 计数

$$
\theta=(A,B).
$$

当前文档中的 Fibonacci 深度响应为

$$
r_k=\frac{\mathrm{Fib}_{k+1}}{\mathrm{Fib}_{k+3}},
\qquad
s_k=\frac{\mathrm{Fib}_{k+2}}{\mathrm{Fib}_{k+3}}.
$$

在固定隐藏深度 $k$ 时，一段历史的似然具有形式

$$
r_k^A s_k^B.
$$

如果每个五态模式 $F[I]$ 可能对应不同的历史计数

$$
\theta_I=(A_I,B_I),
$$

则可以定义每个模式的 future law：

$$
L_I =
\mathscr L_{\mathrm{phase},A_I,B_I}.
$$

然后混合未来律为

$$
\overline{\mathscr L}(p) =
\sum_Ip_IL_I.
$$

根据定理 1，

$$
\overline{\mathscr L}(p) =
\mathscr L_{\mathrm{null}}
+\cdots
+J_{\mathscr L}\kappa,
$$

其中

$$
J_{\mathscr L} =
\mathscr L_{1,3}
-\mathscr L_1
-\mathscr L_3
+\mathscr L_{\mathrm{null}}.
$$

这里 $J_{\mathscr L}$ 是一个未来概率律向量。

#### corollary 29.1: 推论 1：完整未来律恢复 $\kappa$ 的必要充分条件

Claim status: open.（供文 III 原第 5 节「推论 1」；保留纸面论证及其边界。）

> 编者限定（III.5，原推论 1）：必要充分性在固定共同响应核、同一实际模式律、精确均值及正宽度纤维上解释；完整未来律的差应在其共同有符号测度域内比较。FR 的计数恢复本身不完成所需模式核实现或 $J_{\mathscr L}\ne0$ 的证明。


在 $(X,Y,Z)$ 固定且纤维具有正宽度时：

$$
\boxed{
\text{完整未来律能恢复 }\kappa
\Longleftrightarrow
J_{\mathscr L}\neq0.
}
$$

等价地，存在某个合法未来事件 $E$，使得

$$
P(E\mid F[1,3])
-
P(E\mid F[1])
-
P(E\mid F[3])
+
P(E\mid F[\mathrm{null}])
\neq0.
$$

如果所有事件都满足四角差为零，那么完整 future law 仍然无法区分原始金字塔的 $\kappa$-纤维。

这点非常重要：

> 当前 §§34–35 证明了未来响应对 Fibonacci Read 计数 $(A,B)$ 的注入性，但这本身不自动推出未来响应对五态隐藏参数 $\kappa$ 的注入性。

这是两个不同的核：

1. 深度计数核；
2. 五态四角核。

最新 FR 结果解决的是第一种；本轮 $J_{\mathscr L}$ 定理解决的是第二种。

---

### 30. 六、模式—深度分离刚性

Claim status: open.（供文 III 原第 6 节全文。）


下面把最新提交中的 Fibonacci 整数核结果与五态模式进一步合并。

#### definition 30.1: 定义 3：模式—深度联合后验

Claim status: open.（供文 III 原第 6 节「定义 3」；保留纸面论证及其边界。）


令

$$
I\in
\{
F[\mathrm{null}],F[1],F[2],F[3],F[1,3]
\},
$$

隐藏深度为 $K$，其先验为 $\mu_k$。

假设某段历史 $H$ 在模式 $I$、深度 $k$ 下的似然为

$$
L_H(I,k) =
c_I r_k^{A_I}s_k^{B_I},
$$

其中

$$
c_I>0
$$

与深度无关，而

$$
A_I,B_I\in\mathbb N_0.
$$

于是联合后验满足

$$
\pi_H(I,k)
\propto
p_I\mu_kc_Ir_k^{A_I}s_k^{B_I}.
$$

#### theorem 30.1: 定理 2：模式—深度独立性的刚性

Claim status: open.（供文 III 原第 6 节「定理 2」；保留纸面论证及其边界。）

> 编者限定（III.6，原定理 2）：这里已写“正概率模式”，交叉比仍只对 $p_I,p_J,\mu_i,\mu_j,c_I,c_J>0$ 的单元定义；两个深度是不同正整数，Read 计数是非负整数，指数差在 $\mathbb Z$ 中。固定先验、深度无关正因子、同一个 $K$ 和所示乘积似然共同构成条件模型；任意零模式、未知先验或非整数指数不由 FR.34.3 覆盖。


假设深度先验在两个不同深度 $i\neq j$ 上都有正质量。

则模式 $I$ 和深度 $K$ 的后验独立，当且仅当所有正概率模式都具有相同的计数对：

$$
(A_I,B_I)=(A_J,B_J)
$$

对任意正概率模式 $I,J$ 成立。

##### 30.1 证明（III 原定理 2）

定义交叉赔率

$$
\Xi_{I,J;i,j} =
\frac{
\pi_H(I,i)\pi_H(J,j)
}{
\pi_H(I,j)\pi_H(J,i)
}.
$$

代入联合后验，所有先验因子 $p_I,p_J,\mu_i,\mu_j,c_I,c_J$ 消去，得到

$$
\Xi_{I,J;i,j} =
\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
\left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
$$

若模式与深度独立，则交叉赔率必须等于 $1$，所以

$$
\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
\left(\frac{s_i}{s_j}\right)^{B_I-B_J}
=1.
$$

当前 HEAD §§34–35 使用 Fibonacci 行列式恒等式和 Carmichael 原始素因子定理，证明了：

$$
\left(\frac{r_i}{r_j}\right)^u
\left(\frac{s_i}{s_j}\right)^v
=1
\quad\Longrightarrow\quad
u=v=0.
$$

因此

$$
A_I-A_J=0,
\qquad
B_I-B_J=0.
$$

反方向显然成立：若所有模式的 $(A_I,B_I)$ 相同，则后验可以分解成模式因子与深度因子的乘积。证毕。

---

#### 30.1 节内标题：解释

这个定理揭示了一个新的隐藏通道：

$$
\text{五态模式}
\longleftrightarrow
\text{Fibonacci 隐藏深度}.
$$

如果不同模式经历不同的 Read 计数，那么即使初始先验满足

$$
I\perp K,
$$

经过历史更新后也会产生

$$
I\not\perp K.
$$

这种耦合不是普通的边际变化，而是后验交互结构。它可以通过交叉赔率

$$
\Xi_{I,J;i,j}
$$

直接检测。

因此，五态金字塔不应只看成一个静态概率多面体；在动态读取过程中，它会和隐藏 Fibonacci 深度形成一个更大的联合几何体。

---

### 31. 七、三种不同的“充分性”必须分开

Claim status: open.（供文 III 原第 7 节全文。）

> 编者限定（III.7）：固定先验实际活动域上的未来律恢复、计数恢复和完整观察者记忆恢复不同。chronology、selected bank、隐藏一次抽样的 $K$、pending0/pending1 的不同 Stop 职责和 delivered 的空转录，不能用相同剩余 Read 长度或相同活动未来律替代。此处不供给免费的精确概率测量端口。


当前项目中至少有三种不同含义的充分性。

#### 31.1 节内标题：1. 静态 law 充分性

给定

$$
(P,W)=(X,Y,Z,W),
$$

可以恢复

$$
p_{\mathrm{null}},p_1,p_2,p_3,p_{13}.
$$

这是四维单纯形层面的完整恢复。

#### 31.2 节内标题：2. 动态深度充分性

在固定的非单例 Fibonacci 深度先验和活动 phase 中，最新 §§34–35 证明：

- 两个精确未来矩可以恢复后验；
- 后验可以恢复计数 $(A,B)$；
- 计数和 phase 可以恢复完整活动 future law。

这是“深度—计数轴”的充分性。

#### 31.3 节内标题：3. 观察者历史充分性

即使静态 law 和动态 future law 都恢复，仍可能无法恢复：

- Read 的实际 chronology；
- selected-count bank；
- hidden sample identity $K$；
- pending0、pending1、delivered 的边界义务；
- 已被接口声明为必须保持的过去记录。

因此必须区分：

$$
\text{未来律恢复}
\neq
\text{完整历史恢复}.
$$

当前文档 §§36–37 已明确给出边界反例：

- 相同 live counts、phase 和 future law，可以有不同 chronology；
- 相同 future law，可以有不同 selected-count bank；
- 非单例正支持下，单次抽取的隐藏深度 $K$ 不能被零误差识别；
- pending0、pending1、delivered 都可能有剩余 Read 数 $0$，但未来义务分别是 Stop0、Stop1 和空转录。

---

### 32. 八、与 Lean native continuation 的关系

Claim status: open.（供文 III 原第 8 节全文。）

> 编者限定（III.8）：引用固定长度原生合法来源的已有 separation 与 null-reply 结果；完整 exact reply 律、reply 均值和低阶边缘分别保留。所示非交换算式是解释性关系，尚需共同定义域及可组合映射才能成为字面算子等式的否定。


当前已有 Lean/Frozen 结果表明：

1. 固定长度合法 source 在追加 null 后的 exact natural reply 是单射；
2. 但所有 proper local marginals、seam-conditioned local tables 和固定线性 prefix moments 相同，并不保证完整 native continuation 相同；
3. parity-conditioned full-support laws 可以在低阶局部观察完全一致的情况下，让全局 null reply 分布发生差异。

这可以用本轮的响应—纤维语言重新表达：

- 局部边缘观察只约束部分低阶坐标；
- parity law 把差异放在更高阶联合方向；
- native continuation 访问了这个高阶方向；
- 因此局部闭包与完整 continuation 不交换。

形式上：

$$
\operatorname{Continuation}
\circ
\operatorname{Marginalization}
\neq
\operatorname{Marginalization}
\circ
\operatorname{Continuation}.
$$

而在五态 FIB ATOM 层，最小的高阶方向就是 $xy$，也就是

$$
E[xy]=\kappa.
$$

因此可以把 $\kappa$ 看成三位窗口的第一阶“高阶信息逃逸坐标”：

- $X,Y,Z$ 是一阶占用；
- $\kappa=E[xy]$ 是端点共同激活的二阶矩；
- 更长窗口还会出现三阶、四阶甚至全局 parity 型关系。

---

### 33. 九、递归闭包的下一层猜想

Claim status: open.（供文 III 原第 9 节全文。）

> 编者限定（III.9）：本节标题和观察链仍是供文猜想式组织。表中的静态维数不能转用作无限动态历史的信息维数；一个已知非零核变化判据也不自动授予取得仪器、混合模型或任意观察者合同的充分性。$\mathcal O_3$–$\mathcal O_5$ 的能力须在指定的共同来源、先验、权限和边界上逐项证明。


根据上述结构，可以定义一个逐级读出链：

$$
\mathcal O_0=E[q],
$$

$$
\mathcal O_1=(X,Y,Z),
$$

$$
\mathcal O_2=(X,Y,Z,W),
$$

$$
\mathcal O_3=(X,Y,Z,W,\overline{\mathscr L}),
$$

$$
\mathcal O_4=
(X,Y,Z,W,\overline{\mathscr L},
\text{phase},
\text{boundary}),
$$

$$
\mathcal O_5=
\mathcal O_4+
\text{chronology}
+
\text{selected bank}
+
\text{native history}.
$$

对应的信息逃逸维数大致为：

| 观测层 | 能恢复的对象 | 仍可能逸出的信息 |
|---|---|---|
| $\mathcal O_0$ | 数量均值 | 端点边际、$\kappa$、历史 |
| $\mathcal O_1$ | 原始边际占用 | $\kappa$ |
| $\mathcal O_2$ | 完整五态静态 law | 动态深度、phase、历史 |
| $\mathcal O_3$ | 依赖 $J_{\mathscr L}$ 的未来 law | boundary、chronology |
| $\mathcal O_4$ | 活动 future law | selected bank、过去顺序 |
| $\mathcal O_5$ | 完整声明的观察者历史 | 更高窗口的全局关系 |

这不是简单的“坐标越多越完整”。每增加一个读数，都必须检查它是否真的在当前核方向上非零：

$$
\text{新读数有用}
\Longleftrightarrow
\text{新读数在当前不可辨识方向上的变化不为零}.
$$

对于五态窗口，这个判据就是 $J_L\neq0$。

---

### 34. 十、下一步最值得形式化的定理

Claim status: open.（供文 III 原第 10 节全文。）

> 编者限定（III.10）：本节 A/B/C 定理是保留的 open 形式化建议。第一部分的静态仿射逆、FR 的深度计数刚性和此处拟议的向量综合分别有各自前提；本卷不执行这些建议，也不把它们拼接成未证的来源等价。


当前最有价值的形式化顺序是：

#### theorem 34.1: 定理 A：响应向量纤维定理

Claim status: open.（供文 III 原第 10 节「定理 A」；形式化建议。）


在 Lean 中定义一个有限响应向量 $L_I$，证明

$$
\overline L(p) =
L_{\mathrm{null}}
+(L_1-L_{\mathrm{null}})X
+(L_3-L_{\mathrm{null}})Y
+(L_2-L_{\mathrm{null}})Z
+J_L\kappa.
$$

然后证明：

$$
J_L\neq0
\Longrightarrow
(P,\overline L)\text{ injective}.
$$

#### theorem 34.2: 定理 B：模式—深度交叉赔率定理

Claim status: open.（供文 III 原第 10 节「定理 B」；形式化建议。）


在现有 `NativeConditionalControl.lean` 的 likelihood 结构基础上，形式化

$$
\Xi_{I,J;i,j} =
\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
\left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
$$

再接入 FR.34.2 的 Fibonacci 整数核定理。

#### theorem 34.3: 定理 C：动态响应的四角判据

Claim status: open.（供文 III 原第 10 节「定理 C」；形式化建议。）


给定每个模式的完整 future law

$$
\mathscr L_{\mathrm{null}},
\mathscr L_1,
\mathscr L_2,
\mathscr L_3,
\mathscr L_{13},
$$

定义

$$
J_{\mathscr L} =
\mathscr L_{13}
-\mathscr L_1
-\mathscr L_3
+\mathscr L_{\mathrm{null}}.
$$

证明：

$$
J_{\mathscr L}=0
\Longleftrightarrow
\text{未来律在原始 }\kappa\text{-纤维上不变}.
$$

这三条定理连起来，就得到一个清晰的统一结构：

$$
\boxed{
\begin{aligned}
&\text{FIB 数量读出：} &&J_q=0,\\
&\text{闭包关系读出：} &&J_\chi=1,\\
&\text{动态未来读出：} &&J_{\mathscr L}\text{ 决定是否穿透 }\kappa,\\
&\text{Fibonacci 深度：} &&\Xi_{I,J;i,j}\text{ 决定模式—深度是否耦合}.
\end{aligned}
}
$$

所以，Auric FIB ATOM 金字塔的真正递归结构不是单纯的

$$
\mathrm{null}\to2\to3\to5\to[2,5],
$$

而是：

$$
\boxed{
\text{一阶占用}
\;\longrightarrow\;
\text{二阶共同激活}
\;\longrightarrow\;
\text{深度后验}
\;\longrightarrow\;
\text{未来响应}
\;\longrightarrow\;
\text{观察者历史}.
}
$$

其中第一条不可见轴就是

$$
\boxed{
\kappa =
p_{13} =
E[xy] =
W-Z.
}
$$

这条等式把静态闭包、四角交互、未来响应和信息逸出统一到了同一个基础元素上。
<!-- end-supplied-source: response-fiber-source.md -->

## 追加锚（本行以下为增补区）

## 35. 正支撑联合后验的交叉比索引澄清

本节给出 `theorem 8.1`（供文 I 原定理 4）所定义交叉比的完整展开，与 `definition 30.1` 的模式—深度联合后验使用同一索引。分母中的 $\pi_H(J,i)$ 对应 $p_J\mu_i c_J r_i^{A_J}s_i^{B_J}$；其中 $s$ 的下标是 $i$。本节仍属 open 参考输入，是既有条件模型的普通代数澄清，原定义、量词和结论的范围均保留。

### 35.1 正支撑上的完整展开与普通证明

令

$$
\mathcal M=
\{F[\mathrm{null}],F[1],F[2],F[3],F[1,3]\}.
$$

沿用 §§8、30 的共同模型：$p=(p_M)_{M\in\mathcal M}$ 是固定的五态模式先验，$\mu=(\mu_k)_{k\ge1}$ 是固定的正整数深度先验，均为归一化概率律，联合先验为 $p_M\mu_k$。同一次运行中的隐藏深度为同一个 $K$。对同一实际合法有限历史 $H$，所给条件似然为

$$
L_H(M,k)=c_M r_k^{A_M}s_k^{B_M},
\qquad
c_M>0,\qquad A_M,B_M\in\mathbb N_0,
$$

其中 $c_M$ 与深度无关，两类 Read 计数由该历史在模式 $M$ 下诱导，并且

$$
r_k=\frac{\mathrm{Fib}_{k+1}}{\mathrm{Fib}_{k+3}},
\qquad
s_k=\frac{\mathrm{Fib}_{k+2}}{\mathrm{Fib}_{k+3}},
\qquad k\ge1.
$$

这些深度上 $r_k,s_k>0$ 且 $r_k+s_k=1$。$H$ 的条件化须合法且有正概率；联合后验使用同一个有限正归一化常数

$$
\begin{aligned}
\mathcal Z_H
&=\sum_{M\in\mathcal M}\sum_{k\ge1}
 p_M\mu_k c_M r_k^{A_M}s_k^{B_M},
\qquad 0<\mathcal Z_H<\infty,\\
\pi_H(M,k)
&=\frac{p_M\mu_k c_M r_k^{A_M}s_k^{B_M}}{\mathcal Z_H}.
\end{aligned}
$$

这里的归一化是整个共同模式—深度联合律的归一化，不是分别在各模式下归一化。模式条件似然能否在所需原生接口中共同实现，仍须另行桥接。

对任意 $I,J\in\mathcal M$ 和两个不同正整数深度 $i\ne j$，仅在原有正支撑条件

$$
p_I,p_J,\mu_i,\mu_j,c_I,c_J>0
$$

下定义

$$
\Xi_{I,J;i,j}
=\frac{\pi_H(I,i)\pi_H(J,j)}{\pi_H(I,j)\pi_H(J,i)}.
$$

此时四个后验单元都严格为正，交叉比合法，并有

$$
\boxed{
\Xi_{I,J;i,j}
=\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
 \left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
}
$$

指数差属于 $\mathbb Z$；正底数的负整数幂按倒数解释。未要求五个模式全部具有正质量，也未把结论扩至零质量模式、未知先验或非整数计数。

证明。把同一联合后验的四个单元逐项代入。分子与分母各含 $\mathcal Z_H^{-2}$，消去后得到

$$
\begin{aligned}
\Xi_{I,J;i,j}
&=\frac{
 (p_I\mu_i c_I r_i^{A_I}s_i^{B_I})
 (p_J\mu_j c_J r_j^{A_J}s_j^{B_J})
}{
 (p_I\mu_j c_I r_j^{A_I}s_j^{B_I})
 (p_J\mu_i c_J r_i^{A_J}s_i^{B_J})
}\\
&=\frac{r_i^{A_I}r_j^{A_J}}{r_j^{A_I}r_i^{A_J}}
  \frac{s_i^{B_I}s_j^{B_J}}{s_j^{B_I}s_i^{B_J}}\\
&=\left(\frac{r_i}{r_j}\right)^{A_I-A_J}
  \left(\frac{s_i}{s_j}\right)^{B_I-B_J}.
\end{aligned}
$$

第二步消去的 $p_Ip_J\mu_i\mu_jc_Ic_J$ 严格为正；第三步使用正底数的整数幂运算法则。分母最后一个单元的两个深度因子均取 $i$，所以该单元是 $r_i^{A_J}s_i^{B_J}$。这完成所定义交叉比的普通证明。若参与单元的模式或深度先验质量为零，则上述交叉比的分母为零，不能通过取消零因子定义它，也不能据此约束零质量模式的计数。

### 35.2 来源与保留边界

来源为 `repo-derived`：§8 的原交叉比定义、`definition 30.1` 的共同联合模型及 `theorem 30.1` 的同一交叉比表达式。此代数澄清不主张新颖性、优先权、Lean 形式化、内核核验、冻结或物理实现；§8 与 §30 引用的 FR 整数核和独立性刚性仍保留其既有归属与正支撑、正整数深度、整数指数条件，未由本节另行认证。

固定响应方面，§§26–29 的共同实向量空间或共同未来域上的有符号测度空间、同一实际边界模式律、固定模式核、合法未来事件及终端合同、精确响应和正宽度纤维条件全部保留。该交叉比不提供 $J_{\mathscr L}\ne0$、共同五模式响应实现或免费精确测量接口；历史后的实际模式质量与原先验不能互换，单点边界纤维与正宽度纤维仍须分开。FR 的固定先验、两点标量恢复、活动 phase、Read 计数与深度支持条件不扩为完整 chronology、selected-count bank、隐藏样本 $K$ 或 pending0/pending1/delivered 的 Stop 与记录职责恢复。

物理 programme 的继承义务全部保持未解决：同一来源、原固定 cap、实际已 populated 的完整空间 particle/Fock/field/reference/auxiliary 载体上的 state-independent controlled operation，真正 accepted 的非空 $\beta$ whole-$\rho$、已取得的 enable/alignment 数据与原始记录更新；完整 domain/collision/ground/mixed-trace 保持，以及每个固定完整联合向量经实际 raw/restricted identifications 对应原 66.2 tensor-field/auxiliary identity 的桥接。全部 complements、两个 cross blocks、旧 mass-one amplitudes、任意 particle/field/reference/auxiliary correlations、bank、actual balanced stiffness、78.53 的 LINEAR same-inverse-diagonal compensation（particle/reference 两支）和 reference evolution 均保留。finite-energy/number-class tolerances、ingress/alignment、preinstallation/control precision、service/paid holds、physical/service clocks 与总 lifetime/storage/maintenance resources 仍须分别履行，不能升级为 unit-ball、source-growing 或联合极限结论。refusal、$\beta$-empty、Read、Stop、chronological record covariances、Left/Right graft laws 及 unique physical-three closure 也未由本节完成。

## 追加锚（本行以下为增补区）
