# Lean 4 单次编译内生信息逃逸定理系统

## 纯数学理论与工程实现规范

**文档状态：** 规范性草案（Normative Draft）  
**版本：** 4.3 — Single-Compilation / C-IRPT Primitive-Complete / Arena-Invariant / No-Baseline / No-Scoring / Shared-Arena / Layered-Capture / Analysis-v3 / Kernel-Lattice / Layered-Hierarchy / Dispositions
**适用对象：** `the-omega-institute/trureturing` 中由 Lean 4 定义、证明、登记和编译的数学定理族  
**核心约束：** D5 承载数学定义与证明；Reg 以接口契约类型声明登记和封印，编译期由内核检查数学义务。`make lean-report` 读取编译产物并作有界结构评定，输出登记绑定与声明材料。Reg 不含也不调用判官实现。

---

# 摘要

本规范定义一个完全位于 Lean 4 内部的数学系统。系统的输入不是论文、自然语言标签、人工评分或历史版本差分，而是同一次编译中已经 elaborated 的 Lean 定理对象及其数学概念读出。

“当前完整定理族”是 sealing root $R$ 的 import closure 与 canonical object
`Arena` declaration $A$ 下的单个最大 catalog：

$$
\mathcal T_{R,A}=\{\tau_o\}_{o\in I_{R,A}}.
$$

这里的成员是 $R$ 的 import closure 中持久可见的登记 occurrence，而不是裸 theorem 名。
occurrence identity 是 `(canonical Arena declaration, theoremName)`。所有未显式写出上标、下标的
$I,K,E,U,\delta,D_A$ 都是固定同一个 $(R,A)$ 后的简写；不同 arena 之间不存在
默认标量。共享 arena 分析包括 exclusive-capture vector、overlap、kernel
refinement、multiplicity spectrum、role histogram 与 ordered layered capture。数学分析由库内定义与证明承载；生产报告只输出第 30 节的登记绑定数据，
不生成 seal 统计产物。冻结数学声明的身份与证明保持不变。

在上述 flat 与 ordered analysis 上，层级对象的定义如下：每个 maximal canonical catalog 的
generated joint kernels 按**关系外延相等**取商，形成有限闭包格；其全部 strict generator
transitions 组成可含 shortcut edges 的 DAG，Hasse cover graph 是该格的传递约简。Hasse diagram
为 path（因而为 tree）当且仅当格为 chain；存在不可比 kernels 时出现 diamond，因而同一终局
允许多条合法分解。有限 arena 的数学分析使用精确计数，
任意 State 的结构分析使用 strict-inclusion witness。

每个定理对象包含：

$$
\tau_i=(P_i,p_i,c_i),
$$

其中：

- $P_i:\mathrm{Prop}$ 是原定理陈述；
- $p_i:P_i$ 是 Lean kernel 接受的证明；
- $c_i:X\to O_i$ 是该定理在其数学语义空间 $X$ 上建立、约束或公开的概念读出；
- $O_i$ 可以依赖于 $i$，只要求其相等关系可判定。

在本版本中，$c_i$ 不再被视为可自由附加的 readout。每个 theorem 必须首先在 Lean 中给出由 `CUT`、`FLOW`、`ADMIT`、`ANCHOR` 组成的有限 primitive bundle $\Pi_i$；系统从该 bundle 的联合不可区分核规范导出 $c_i$。只要两个 primitive representations 诱导相同 kernel，它们产生完全相同的信息逃逸结果。

对任意定理子族 $S\subseteq I$，定义其联合不可区分核：

$$
K_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
\forall i\in S,\ c_i(x)=c_i(y)
\right\}.
$$

去除对角线后，定义该定理子族尚未消除的信息逃逸：

$$
E_S
=
K_S\setminus\Delta_X,
\qquad
\Delta_X=\{(x,x):x\in X\}.
$$

在有限非平凡状态空间上，信息逃逸率唯一地取为均匀有序非对角 pair 的碰撞概率：

$$
\varepsilon(S)
=
\frac{|E_S|}{|X|(|X|-1)}.
$$

本系统不使用历史基线。对当前定理族中的每个 $i$，在同一个完整族中构造其**留一反事实族**：

$$
I^{-i}=I\setminus\{i\}.
$$

定理 $\tau_i$ 的内生信息增益定义为：

$$
\delta_i(\mathcal T)
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

等价地，定义该定理独有捕获的状态对：

$$
U_i
=
E_{I^{-i}}\setminus E_I.
$$

则：

$$
\delta_i(\mathcal T)
=
\frac{|U_i|}{|X|(|X|-1)}.
$$

因此定理的伴随信息命题为：

$$
G_i(\mathcal T)
:\Longleftrightarrow
\varepsilon(I)<\varepsilon(I^{-i}),
$$

也即：

$$
G_i(\mathcal T)
\Longleftrightarrow
U_i\neq\varnothing.
$$

正成员满足下列增强命题。指定 maximal catalogs 的全称正性是数学上的不可约条件；`Contract.SealCatalog` 的逐成员与目录结论字段携带相应证明，由 Reg 编译期内核检查：

$$
\widehat\tau_i
:
P_i\land G_i(\mathcal T).
$$

其证明为：

$$
\widehat p_i
=
\langle p_i,g_i\rangle,
$$

其中 $g_i:G_i(\mathcal T)$ 由同一次 Lean 编译对当前完整定理族精确计算并由 kernel 检查。

指定系统 root $R_\star$ 的 maximal catalogs 的全称正性表示下列数学条件。目录的冗余或不可约证明保存在 `SealCatalog.conclusion` 中：

$$
\boxed{
\forall A\in\operatorname{Arenas}(R_\star),\
\forall o\in I_{R_\star,A},\quad
\delta^{R_\star}_{A,o}(\mathcal T_{R_\star,A})>0
}
$$

即该全称条件要求指定 root 的每个 canonical maximal catalog 中删除任意 occurrence 都使信息逃逸率严格上升。辅助 root 与 analysis view 不替代该证明。Seal 保留完整 peers，`SealRow.conclusion` 对每个成员携带降低逃逸或平凡性证明；零成员另携剩余目录的语义闭包归属证明。冗余目录仍可提供合法 Seal。本节的全称正性是数学命题，不构成额外生产准入门。

本规范明确取消以下对象：

- 历史 baseline；
- parent catalog；
- 前后 commit 差分；
- 人工 novelty score；
- 用户可调权重；
- 用户可调 target；
- 用户可调阈值；
- 研究价值等级；
- 外部 C#／Python 判官；
- 两阶段生成源码再编译；
- 按提交顺序计算的边际贡献。

所有判断只来自当前完整 Lean 定理族自身所诱导的 C-IRPT primitive kernels、联合核、残余、有限计数和严格不等式。`FLOW`、`ADMIT`、`ANCHOR` 进入计算时都先在 Lean 内规范化为 kernel；外部不存在第二套角色评分器。

---

# 第一部　纯数学理论

## 1. 基本对象

### 1.1 数学状态空间

固定一个类型：

$$
X:\mathrm{Type}.
$$

$X$ 不是评价者选择的测试集，而是该组数学概念共同作用的本体状态空间。若研究对象是有限自动机，则 $X$ 是自动机状态；若研究对象是有限编码，则 $X$ 是编码状态；若研究对象是有限模型，则 $X$ 是模型状态。

数值硬门要求：

$$
2\le |X|<\infty.
$$

一般无限理论仍可使用严格核包含版本，但不能伪装成可执行的有限逃逸率。

### 1.2 定理索引族

固定 sealing root $R$ 与 canonical object `Arena` declaration $A$。其有限 occurrence
索引类型为：

$$
I_{R,A}:\mathrm{Type},
\qquad |I_{R,A}|<\infty.
$$

$I_{R,A}$ 中每个元素对应 $R$ 的 import closure 中持久可见、显式归属于 $A$ 的一个
被登记 theorem occurrence。同一个 theorem declaration 可以在不同 canonical arenas 中
出现，但每次都必须有分别命名、由 kernel 检查的 realization。

### 1.3 异构定理读出

对每个 $i\in I$，给定一个输出类型：

$$
O_i:\mathrm{Type},
$$

以及概念读出：

$$
c_i:X\to O_i.
$$

不同定理可以有不同输出类型。联合核只逐坐标比较同一个定理的输出，因此无需把所有 $O_i$ 强制编码进同一总类型。

规范上，每个 $c_i$ 必须实现 theorem primitive bundle $\Pi_i$ 的 joint kernel：

$$
\ker(c_i)
=
\bigcap_{p\in\Pi_i}\kappa_p.
$$

其中 $\kappa_p$ 是 `CUT`、`FLOW`、`ADMIT` 或 `ANCHOR` primitive 的 canonical kernel。计算引擎的首要输入是该 kernel；`c_i` 只作为兼容既有 `Concept` API 的实现。

### 1.4 定理对象

一个可分析定理对象写作：

$$
\tau_i=(P_i,p_i,c_i),
$$

其中：

$$
P_i:\mathrm{Prop},
\qquad
p_i:P_i.
$$

$c_i$ 是定理数学内容的概念侧，而不是外部评价字段。原 theorem 与 primitive bundle 的联系必须在 Lean 中由其标准 `PrimitiveLaw` 陈述形式或一个 kernel-checked realization theorem 建立；系统不得从自然语言标签猜测 primitive 角色。

系统不得接受：

```text
importance = high
novelty = 0.91
weight = 37
```

系统只接受 Lean 项与 Lean 证明。

### 1.5 Canonical arena、occurrence 与最大 catalog

`Arena` 是被研究数学对象的 canonical typed declaration；`PrimitiveLawArena` 只是定理
law 的 presentation。分组键是 canonical `Arena` declaration，不是恰好相同的 carrier
type，不是 namespace，也不是 `PrimitiveLawArena` 名称。若声称两个表示是同一对象，
必须给出 `CIRPT-IE-022` 所要求的 `Equiv` 与 kernel transport；carrier coincidence、等势
或相同 kernel address 都不够。

一个登记 occurrence 记为：

$$
o=(A,\operatorname{theoremName},\operatorname{unit},\Pi,K,
\operatorname{realization}).
$$

其唯一键为：

$$
(\operatorname{canonicalArenaDeclaration},\operatorname{theoremName}).
$$

该键在一个 sealing root 的整个 import closure 中恰出现一次；同一 theorem 在同一 canonical
arena 的第二次登记是 IE-C002 collision。一个 theorem 只有通过另一个具名、kernel-checked
realization 登记到不同 canonical arena 时才形成新的合法 occurrence。每个 occurrence 都有
独立的 catalog-qualified unit、realization 与 companion names，因此同一 theorem 的两个合法
occurrences 不会产生 generated-name collision；IE-C025 专门保留给 qualified-name collision。

对每个 $(R,A)$，定义 $C_{R,A}$ 为包含 $R$ 的 import closure 中所有归属于 $A$ 的 occurrence 的唯一
**canonical maximal catalog**。同 arena 的 sub-catalog 只可声明为 `analysis_view`，不得
替代 $C_{R,A}$，不得用于证明 positivity。seal 不得比它的 import closure 少看任何同 arena
member（工程优化规范 v1 §16）。用 namespace、另一个 auxiliary root、wrapper、克隆 arena
或“在别处为正”拆开本应同组的 peers，均不改变 designated system root 的义务。

---

## 2. 联合观察与不可区分核

### 2.1 子族联合读出

对任意 $S\subseteq I$，联合读出可抽象写作：

$$
C_S(x)=(c_i(x))_{i\in S}.
$$

因输出依赖于 $i$，严格类型是一个 dependent function：

$$
C_S(x):\prod_{i:S}O_i.
$$

### 2.2 联合核

定义：

$$
K_S
=
\ker C_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
C_S(x)=C_S(y)
\right\}.
$$

展开后：

$$
(x,y)\in K_S
\Longleftrightarrow
\forall i\in S,\ c_i(x)=c_i(y).
$$

$K_S$ 表示定理子族 $S$ 仍无法区分的全部状态对。

### 2.3 核的反单调性

若：

$$
S\subseteq T,
$$

则：

$$
K_T\subseteq K_S.
$$

证明直接来自量词范围扩大：更多概念坐标只会增加相等约束，不可能制造新的不可区分状态对。

### 2.4 对角线

定义：

$$
\Delta_X
=
\{(x,x):x\in X\}.
$$

对角线不是信息逃逸，因为任何正确观察都应允许状态与自身不可区分。

---

## 3. 内生信息逃逸

### 3.1 逃逸集合

定义定理子族 $S$ 的内生信息逃逸集合：

$$
E_S
=
K_S\setminus\Delta_X.
$$

等价地：

$$
E_S
=
\left\{
(x,y)\in X^2
\;\middle|\;
x\neq y
\land
\forall i\in S,\ c_i(x)=c_i(y)
\right\}.
$$

本定义不需要外部 target。目标固定为状态身份本身：不同状态应当被完整概念族尽可能区分。

在仓库既有概念语言中，它等价于：

$$
E_S
=
\operatorname{defectRelation}(C_S,\operatorname{id}_X).
$$

因此这是已有 `defectRelation` 在固定 identity target 上的内生特化，而不是新增一套平行定义。

### 3.2 逃逸单调性

若：

$$
S\subseteq T,
$$

则：

$$
E_T\subseteq E_S.
$$

加入定理只能缩小或保持逃逸集合。

### 3.3 完全区分

定理族 $S$ 完全区分状态，当且仅当：

$$
E_S=\varnothing.
$$

等价地：

$$
K_S=\Delta_X.
$$

等价地：

$$
C_S:X\to\prod_{i:S}O_i
$$

为单射。

完整系统不要求当前数学必须已经完备，因此 positive admission 不强制 $E_I=\varnothing$。level-0 seal 对完整、非退化且合法的 catalog 成功，保留全部成员；零成员认证为 `trivial_in_catalog`，`SealCatalog.conclusion` 携带冗余证明；待首次冻结对象自身为零时不获 positive admission。

---

## 4. 唯一无权重逃逸率

### 4.1 有序非对角状态对

定义：

$$
D_X=X^2\setminus\Delta_X.
$$

若 $|X|=n$，则：

$$
|D_X|=n(n-1).
$$

### 4.2 均匀逃逸率

定义：

$$
\varepsilon(S)
=
\frac{|E_S|}{|D_X|}
=
\frac{|E_S|}{|X|(|X|-1)}.
$$

因此：

$$
0\le\varepsilon(S)\le1.
$$

### 4.3 概率解释

从 $D_X$ 上均匀抽取一个有序不同状态对 $(X_1,X_2)$。则：

$$
\varepsilon(S)
=
\Pr[C_S(X_1)=C_S(X_2)].
$$

所以信息逃逸率就是：

> 两个真实不同状态在当前定理概念族下仍发生观察碰撞的概率。

### 4.4 为什么没有权重参数

在有限 $D_X$ 上，要求测度同时满足：

1. 非负；
2. 有限可加；
3. 总质量为 $1$；
4. 对 $D_X$ 的任意置换不变；

则每个单点必须具有相同质量：

$$
\mu(\{p\})=\frac1{|D_X|}.
$$

因而对任意 $A\subseteq D_X$：

$$
\mu(A)=\frac{|A|}{|D_X|}.
$$

故在“不允许对任意状态 pair 赋予特殊优先权”的对称性原则下，均匀计数率是唯一选择。

这里不存在：

- 人工权重；
- 领域权重；
- theorem 权重；
- 风险系数；
- 成本系数；
- 手工阈值。

---

## 5. 单次编译中的留一反事实

**v4.2 作用域约定。** 本节 5.1--5.6 中沿用的 $I,K,E,U,\delta$ 是固定 sealing
root $R$ 与 canonical object arena $A$ 后的简写，规范全名如下：

$$
I=I_{R,A},\quad
K_S=K^R_{A,S},\quad
E_S=E^R_{A,S}=K^R_{A,S}\cap D_A,
\quad D_A=A.\mathrm{State}^2\setminus\Delta_A,
$$

$$
U_i=U^R_{A,i}
=D_A\cap\bigl(K^R_{A,I_{R,A}\setminus\{i\}}\setminus K^R_{A,i}\bigr),
\qquad
\delta_i=\delta^R_{A,i}=|U^R_{A,i}|/|D_A|.
$$

这里的“完整族”是 sealing root $R$ 的 import closure 中全部持久可见、归属于 $A$ 的 theorem
occurrences 所成的 canonical maximal catalog $C_{R,A}$。imported `.olean` 中持久可见的登记
就是该 seal 的成员；analysis sub-catalog 不能替代它或用于证明 positivity。
registry 的导入行为构成 import-closure seal membership contract；相关 seal checks 见第 25.2、37、39 节。

### 5.1 完整族

当前编译完成后，完整被分析定理族是：

$$
I.
$$

这里的完整意味着 root 的 import closure 中全部持久可见的 registry entries；它不是历史仓库
状态，也不能仅凭任意局部环境冒充仓库级 registration closure。

### 5.2 留一族

对每个 $i\in I$，定义：

$$
I^{-i}=I\setminus\{i\}.
$$

$I^{-i}$ 不是 baseline，不保存、不导入、不来自旧 commit。它只是当前有限族 $I$ 内部的一个反事实删除子集。

### 5.3 完整逃逸与留一逃逸

定义：

$$
E=E_I,
$$

$$
E^{-i}=E_{I^{-i}}.
$$

由单调性：

$$
E\subseteq E^{-i}.
$$

### 5.4 定理独有捕获集

定义：

$$
U_i
=
E^{-i}\setminus E.
$$

展开：

$$
U_i
=
\left\{
(x,y)\in X^2
\;\middle|\;
\begin{array}{l}
x\neq y,\\
\forall j\neq i,\ c_j(x)=c_j(y),\\
c_i(x)\neq c_i(y)
\end{array}
\right\}.
$$

$U_i$ 中的每一个 pair 都是：

- 其他所有定理联合仍无法区分；
- 只有保留 $i$ 才能区分；
- 因而构成 $i$ 在当前完整族中的不可替代信息。

### 5.5 留一信息增益

定义：

$$
\delta_i
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

由 $E\subseteq E^{-i}$：

$$
\delta_i\ge0.
$$

又由有限不交分割：

$$
E^{-i}=E\;\dot\cup\;U_i,
$$

所以：

$$
|E^{-i}|=|E|+|U_i|.
$$

因此：

$$
\boxed{
\delta_i
=
\frac{|U_i|}{|X|(|X|-1)}
}
$$

### 5.6 严格降低命题

定义：

$$
\operatorname{LowersEscape}(\mathcal T,i)
:\Longleftrightarrow
\varepsilon(I)<\varepsilon(I^{-i}).
$$

等价地：

$$
\operatorname{LowersEscape}(\mathcal T,i)
\Longleftrightarrow
\delta_i>0.
$$

等价地：

$$
\operatorname{LowersEscape}(\mathcal T,i)
\Longleftrightarrow
U_i\neq\varnothing.
$$

### 5.7 共享 arena 分析量

以下量全部只在同一个 $(R,A)$ 内定义。令 occurrence $i$ 的 separation/capture set 为：

$$
\operatorname{Cap}^R_{A,i}=D_A\setminus K^R_{A,i}.
$$

则 peer-relative exclusive capture 也可写为：

$$
U^R_{A,i}
=\operatorname{Cap}^R_{A,i}\setminus
\bigcup_{j\neq i}\operatorname{Cap}^R_{A,j}.
$$

exclusive-capture vector 与 exact gain vector 分别为：

$$
u^R_A=(|U^R_{A,i}|)_{i\in I_{R,A}},
\qquad
g^R_A=(|U^R_{A,i}|/|D_A|)_{i\in I_{R,A}}.
$$

两 occurrence 的 pairwise capture overlap 为：

$$
O^R_{A,ij}=\operatorname{Cap}^R_{A,i}\cap
\operatorname{Cap}^R_{A,j},
\quad
o^R_{A,ij}=|O^R_{A,ij}|,
\quad
\omega^R_{A,ij}=o^R_{A,ij}/|D_A|.
$$

该矩阵对称，且 $O^R_{A,ii}=\operatorname{Cap}^R_{A,i}$。overlap 只描述共同捕获，单独不构成
冗余判词。

定义 kernel refinement：

$$
\operatorname{KernelRefines}_{R,A}(i,j)
:\Longleftrightarrow K^R_{A,i}\subseteq K^R_{A,j}.
$$

即 $i$ 至少与 $j$ 一样细。它是 preorder；互相 refinement 等价于 kernel equality。
有向矩阵中的每一 pair 必须 proof-backed 地分类为 `equal`、`strictly_finer`、
`strictly_coarser` 或 `incomparable`。若 peer $j\neq i$ 满足
$\operatorname{KernelRefines}(j,i)$，则 $U^R_{A,i}=\varnothing$。特别地，refinement
成立时 $O_{ij}$ 等于较粗 readout 的 capture set。

所有 rate 都以同一个 $|D_A|$ 为分母并使用 exact rational。非等价 arena 的数值只可
各 arena 的数学结果分别解释，不得求和、平均或排序；经 `CIRPT-IE-022` 证明的 arena transport 才允许声明
这些数值保持不变。

### 5.8 捕获重数谱

对 $p\in D_A$ 定义其被 theorem occurrences 捕获的重数：

$$
m^R_A(p)=|\{i\in I_{R,A}\mid p\in\operatorname{Cap}^R_{A,i}\}|.
$$

capture-multiplicity spectrum 为：

$$
h^R_A(k)=|\{p\in D_A\mid m^R_A(p)=k\}|,
\qquad 0\le k\le |I_{R,A}|.
$$

它满足：

$$
\sum_k h^R_A(k)=|D_A|,
\qquad
h^R_A(0)=|E^R_A|,
\qquad
h^R_A(1)=\sum_i|U^R_{A,i}|,
$$

$$
\sum_k k\,h^R_A(k)=\sum_i|\operatorname{Cap}^R_{A,i}|,
$$

以及 order-free second-moment identity：

$$
\sum_{i\in I_{R,A}}\ \sum_{j\in I_{R,A}\setminus\{i\}}
|O^R_{A,ij}|
=
\sum_k k(k-1)h^R_A(k).
$$

左侧对每个 unordered pair 计数两次，因此不需要给 `Catalog.Index` 增加次序。若实现为
canonical upper triangle，则可在局部显式引入 `[LinearOrder catalog.Index]`，但其结果必须由
上式证明与所选次序无关；规范 API 不要求或冻结该次序。

$h(k\ge2)$ 描述多重捕获 pair，不单独判定 theorem 冗余。

### 5.9 有序分层捕获

平坦 catalog 的 $U_i$ 回答“相对于所有 peers，谁是唯一 owner”；它不回答一条
逐层增强的观测链中“每一层新增多少”。后者必须由一个携带 inclusion proofs 的有序
kernel chain 给出。

设：

$$
K_\ell\subseteq\cdots\subseteq K_1\subseteq K_0.
$$

定义 ordered layered capture：

$$
L_0=D_A\setminus K_0,
\qquad
L_r=D_A\cap(K_{r-1}\setminus K_r)\quad(1\le r\le\ell),
$$

及 finest unresolved set：

$$
R_\ell=D_A\cap K_\ell=K_\ell\setminus\Delta_A.
$$

定义 ordered layered-capture spectrum 与 exact rate spectrum：

$$
\Lambda^R_A(r)=|L_r|,
\qquad
\lambda^R_A(r)=|L_r|/|D_A|
\quad(0\le r\le\ell).
$$

`unresolved` 的 $|R_\ell|$ 与 $|R_\ell|/|D_A|$ 单列，不混入 capture spectrum。

$L_0,\ldots,L_\ell$ 两两不交并分割 $D_A\setminus K_\ell$；再加 $R_\ell$ 后分割
整个 $D_A$。初层满足：

$$
L_0\neq\varnothing
\Longleftrightarrow
D_A\nsubseteq K_0
\Longleftrightarrow
\exists x\ne y,\ \neg K_0(x,y).
$$

对 $r>0$：

$$
L_r\neq\varnothing
\Longleftrightarrow
K_r\subsetneq K_{r-1}.
$$

因此“观测 $\subsetneq$ 干预 $\subsetneq$ 反事实各自拥有多少”在本规范中指 ordered
layered counts $(|L_0|,\ldots,|L_\ell|)$，不是把累计 readouts 放进平坦共享 catalog 后的
leave-one-out counts。若平坦 catalog 同时含 $K_j\subsetneq K_i$，则较粗成员 $i$ 的
$U_i$ 为零。对含有 $K_{cf}\subsetneq K_{int}\subsetneq K_{obs}$ 的任意 flat catalog，必有
$U_{obs}=U_{int}=\varnothing$，而一般式为：

$$
U_{cf}=\bigl(D_A\cap(K_{int}\setminus K_{cf})\bigr)
\setminus
\bigcup_{k\in I_{R,A}\setminus\{obs,int,cf\}}\operatorname{Cap}^R_{A,k}.
$$

只有当该 analysis view 恰有 `obs`、`int`、`cf` 三个 members 时，才可化简为
$U_{cf}=D_A\cap(K_{int}\setminus K_{cf})$。

### 5.10 生成核闭包格与分层 DAG

固定一个 maximal canonical catalog $C_{R,A}$，简写其有限索引集为 $I$。定义 generated
kernel family：

$$
\mathcal L_C
=
\{K_S\mid S\subseteq I\}/\!=_{\rm rel},
$$

其中 $K_S=K_T$ 的含义是关系外延相等：

$$
\forall x,y:A.\mathrm{State},\quad K_S(x,y)\leftrightarrow K_T(x,y).
$$

因此不同 generator subsets 若产生同一个关系，只是同一个 node。有限 engine 必须用完整
reflected truth table 判定该等式；`sha256` address 只作 diagnostic，不是 node identity 或
数学证据。

在 $\mathcal L_C$ 上规定“越细越小”：

$$
[S]\le[T]\quad\Longleftrightarrow\quad K_S\subseteq K_T.
$$

于是 top 是 $K_\varnothing$，所有 states 尚不可区分；bottom 是 $K_I$。meet 是关系交：

$$
K_S\wedge K_T=K_S\cap K_T=K_{S\cup T}.
$$

join **只在 generated closure 内**取：它是 $\mathcal L_C$ 中包含 $K_S\cup K_T$ 的最细
generated kernel，等价于所有此类 generated upper bounds 的交。不得把 ambient partition
lattice 的 join 写入本对象。因为 $I$ 有限、$K_\varnothing\in\mathcal L_C$ 且该 family 对任意
有限交封闭，$\mathcal L_C$ 是有限格。

若 $P=[S]$，加入 occurrence $i$ 得：

$$
Q=[S\cup\{i\}],\qquad K_Q=K_P\cap K_i.
$$

当 $K_Q\subsetneq K_P$ 时，记一条带 label $i$ 的 strict generator transition
$P\xrightarrow{i}Q$；若 $K_Q=K_P$，该次加入记为 `collapsed_addition`／stutter，绝不伪造为
edge。定义两个不同的图，禁止混称：

1. **full strict generator-transition DAG** $G_{\rm gen}$ 保留每个上述严格单生成元步骤；一次
   generator step 可以跨过若干 Hasse levels，所以 $G_{\rm gen}$ 可含 shortcut edges；
2. **Hasse cover graph** $G_{\rm cov}$ 只保留 lattice order 的 covers，即
   $Q\subsetneq P$ 且不存在 $R$ 使 $Q\subsetneq R\subsetneq P$。它是 generated lattice 的
   transitive reduction。

artifact 的 bounded `edges` 只承载已认证且两个 endpoints 都在 materialized node set 中的 strict
generator transitions；它总是包含每个 certified-schedule strict transition 与每个显式请求的
transition。其不变量是 `edges ⊆ strict transitions of the full DAG restricted to materialized nodes`：
bounded projection 因而是 full strict DAG 的 subgraph，但每个 `is_cover` 仍相对于完整 generated
lattice 全局证明。只有 `complete_lattice_materialized=true` 时，`edges` 才必须是 $G_{\rm gen}$
的完整 edge array。ASCII projection 只绘制 `is_cover: true` 的 covers；因此 full strict DAG 不是
Hasse diagram，也不能由 renderer layout 冒充 Hasse diagram。
定义 node 与 edge payload：

$$
\operatorname{escapeAt}(P)=D_A\cap K_P,
$$

$$
\operatorname{edgeCapture}(P,Q)
=\operatorname{escapeAt}(P)\setminus\operatorname{escapeAt}(Q)
=D_A\cap(K_P\setminus K_Q).
$$

沿 strict generator transitions 的 path 是一种 decomposition。不同加入次序可以给出不同
paths，但都落到 $K_I$。用户面对的对象因此一般是 DAG／lattice，不是预先假定的树。正确的
tree／chain 等价只施于 Hasse diagram：

$$
G_{\rm cov}\text{ 是 path（因而是 tree）}
\Longleftrightarrow
\mathcal L_C\text{ 是 chain}
\Longleftrightarrow
\{K_i\}_{i\in I}\text{ 经闭包后两两可比}.
$$

即使 $\mathcal L_C$ 是 chain，$G_{\rm gen}$ 仍可因 $K_\varnothing\to K_{int}$ 等跨层
generator steps 含 shortcut edges，因而一般不是 tree。两个不可比 generated kernels 由 meet
与 internal join 产生 diamond，表示多种合法分解。
terminal kernel/escape、leave-one-out $U_i$、capture multiplicity spectrum $h(k)$、
overlap/refinement matrices 与 catalog verdict 都与选取哪条 chain 无关；chain 只分配“在哪一层
捕获”，不改 terminal truth。

对 $N=|A.\mathrm{State}|$，一条 equivalence-kernel strict refinement 每步至少把一个
equivalence class 分裂，class 数从 $1$ 至多增到 $N$，所以任何 strict chain 的长度满足：

$$
\boxed{\ell\le N-1.}
$$

这是工程优化规范 v1 §19 的容量事实，不是可调预算。`kernel_projection` 只能投影这套已认证
数学；依工程优化规范 v1 §4 与本规范 §30.5，它绝不成为 admission input。

---

## 6. 结构版本：不依赖有限计数

在任意类型 $X$ 上，定义：

$$
\operatorname{StructurallyLowersEscape}(\mathcal T,i)
:\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}.
$$

因为：

$$
K_I
=
K_{I^{-i}}\cap\ker(c_i),
$$

严格包含等价于存在：

$$
\exists x,y,
\quad
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y).
$$

若额外要求 $x\neq y$，该 witness 自动成立，因为 $c_i(x)\neq c_i(y)$ 已推出 $x\neq y$。

有限非平凡 $X$ 上：

$$
\operatorname{StructurallyLowersEscape}(\mathcal T,i)
\Longleftrightarrow
\operatorname{LowersEscape}(\mathcal T,i).
$$

因此：

- 严格核缩小是基础数学命题；
- 精确逃逸率差是有限可执行实现；
- 二者不是两套评价体系，而是同一命题的结构层与计数层。

### 6.1 StructuralArena / StructuralCatalog

`Catalog.StructurallyLowersEscape` 以 finite `Arena` 为参数，因而
`D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lean` **只是 finite catalog 的
Set-level characterization，不是 universal structural engine**。v4.3 另设不要求
`Fintype State`、`DecidableEq State` 或关系可计算的层：

```lean
universe u v w

structure StructuralArena where
  State : Type u

structure StructuralKernel (X : Type u) where
  relation : X → X → Prop
  equivalence : Equivalence relation

structure StructuralTheoremUnit (arena : StructuralArena) where
  PrimitiveIndex : Type v
  primitiveIndexFintype : Fintype PrimitiveIndex
  primitiveKernel : PrimitiveIndex → StructuralKernel arena.State
  Statement : Prop
  proof : Statement

structure StructuralCatalog (arena : StructuralArena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → StructuralTheoremUnit arena
```

每个 theorem bundle 的 primitive index 与每个 catalog index 仍有限；只有 object State 可以
无限，且不要求枚举。statement 到 primitives 的 `NativeTheoremUnit`／
`LegacyPrimitiveRealization` 对应物仍是必需数学输入，不能只附自然语言标签。对
$S\subseteq I$ 定义：

$$
K^{\rm str}_S(x,y)
\Longleftrightarrow
\forall i\in S,\ \forall a,
\operatorname{primitiveKernel}_{i,a}(x,y).
$$

structural occurrence $i$ 的 acceptance proposition 使用 curried relations 上的 pointwise order：

$$
K^{\rm str}_I\le K^{\rm str}_{I\setminus\{i\}}
\quad\land\quad
\neg\left(K^{\rm str}_{I\setminus\{i\}}\le K^{\rm str}_I\right),
$$

其中 $r\le s$ 表示 $\forall x\,y,\ r(x,y)\to s(x,y)$；这里不对
`X → X → Prop` 应用 Set 的 strict-subset operator。

其 certificate 必须同时给出 inclusion proof 与 pair witness：

$$
\exists x,y,
\left(\forall j\ne i,\ K_j^{\rm str}(x,y)\right)
\land\neg K_i^{\rm str}(x,y).
$$

此层不报告 cardinality、rate、truth table 或 kernel hash。有限 `Arena`、`TheoremUnit` 与
`Catalog` 分别有规范 embedding `Arena.toStructuralArena`、
`TheoremUnit.toStructuralTheoremUnit`、`Catalog.toStructuralCatalog`；embedding 后的 joint
kernel 外延相等，且 finite `LowersEscape` 与 structural strict inclusion 等价。因此 finite
engine 是 universal structural layer 的有计数特化，不是平行判词。

### 6.2 结构化观测接口 Γ 与相对逃逸处

**接口契约。** 结构化观测接口 $\Gamma$ 由带结构的 carrier、允许的保结构 transports、
每个站点的显式状态构造、localization mode 与 observation language 组成。
观测语言规定 permitted operations 与模板的 slot grammar。
站点族记为 $B_\Gamma$，站点 $b$ 的状态类型记为 $S_b$；站点标签不充当状态枚举。
carrier 的类型、实例与参数共同确定可用的 registry entry，裸类型不确定逃逸处。
canonical 的含义是站点、状态构造与读数在已登记 transports 下的交换性；它不指定代表元。
声称两个 frame 等价时，必须另给状态 `Equiv` 与 kernel transport proof。

固定 sealing root 与站点的 canonical arena 后，$I$ 是 §5.1 的完整 catalog 索引。
认证模板只实例化其声明并实际消费的有限读数 $c_{i,a}:S_b\to O_{i,a}$；
$i\in I$，每个 occurrence 的 slot $a$ 有限，$S_b$ 与 $O_{i,a}$ 无有限性要求。
registry 提供一个 quotient constructor 不授权给每条定理追加完整 quotient readout。
对 $J\subseteq I$，catalog-relative kernel、其商与相对逃逸处满足：

$$
K_{b,J}(s,t)\ \Longleftrightarrow
\forall i\in J,\ \forall a,\ c_{i,a}(s)=c_{i,a}(t),
\qquad Q_{b,J}=S_b/K_{b,J},
$$

$$
L_{\Gamma,J}(b)
=\bigl(S_b\times_{Q_{b,J}}S_b\bigr)\setminus\Delta_{S_b}
=\{(s,t)\mid s\ne t\ \land\ K_{b,J}(s,t)\}.
$$

这是站点索引的 off-diagonal kernel pair，不要求是原 carrier 的子集。
有限 pointwise 情形恰好退化为 §5.1 的完整族及其 §5 构造：只有一个站点，$S_b=X$，
$L_J$ 就是 off-diagonal joint-kernel relation $E_J$；leave-one-out capture 仍为
$U_i=L_{I\setminus\{i\}}\setminus L_I$。本款不重定义 §5，不增加任何量，
有限非退化 arena 的 pair denominator、counts、exact rates 与 admission 判词沿用 §5。

**规范性 entries。** 下列条目是带适用假设的规范例，不是穷尽 registry；Mathlib 名称是绑定标识。

- **实数有序拓扑。** 站点是 $+\infty$ 与 $-\infty$，分别由
  `(Filter.atTop : Filter ℝ)` 与 `(Filter.atBot : Filter ℝ)` 实现；对声明的值类型 $Y$，
  站点状态是 `Filter.Germ (Filter.atTop : Filter ℝ) Y` 与
  `Filter.Germ (Filter.atBot : Filter ℝ) Y`。全局函数到状态的构造是 `Filter.Germ.ofFun`，
  其 kernel 是对应 filter 上的 `Filter.EventuallyEq`。
  `Filter.Tendsto f F G` 分别记录 source $F$ 的局部化与 target $G$ 的收敛角色；
  source `atTop` 与 target `atTop` 不互相替代。站点上的读数是模板声明的 germ 操作，
  如 `Filter.Germ.map`；保 filter 的预复合由 `Filter.Germ.compTendsto` 及其 `Tendsto` 证明绑定。
  读数 kernel 是所得 germs 相等，不是两个端点标签的相等；`EReal` 嵌入本身是单射。
- **自然数有序尾部。** 站点是 `(Filter.atTop : Filter ℕ)`，状态是
  `Filter.Germ (Filter.atTop : Filter ℕ) Y`；局部化 kernel 是 eventual equality，
  即存在 $N$ 使所有 $n\ge N$ 上的函数值相等。有限值类型不使轨迹或 germ 状态自动有限。
- **复数与局部紧 Hausdorff 空间。** 对 `LocallyCompactSpace X`、`T2Space X`，
  cocompact mode 的站点是一个 $\infty$，绑定 `Filter.cocompact X`，状态是
  `Filter.Germ (Filter.cocompact X) Y`；局部化 kernel 是紧集之外的 eventual equality。
  `OnePoint X` 的无穷远邻域解释使用对应 filter 传输；`ℂ` 使用此单站点接口。
  非平凡无穷远解释要求相应 `Filter.NeBot`；紧空间的底 filter 不冒充空间端点。
  `OnePoint` 嵌入的 pointwise kernel 是对角线。范数趋于 `atTop` 与 cocompact 收敛的互推
  要求 properness／紧闭球假设；范数读数的 kernel 是范数相等，该收敛互推不证明 kernels 相等。
- **圆的覆盖接口。** 对实参数 $p>0$，令 $\Theta=\texttt{AddCircle}\ p$。
  站点是指定覆盖 $q:\mathbb R\to\Theta$，状态是实数 lift；读数 $q(t)=(t:\Theta)$ 的
  kernel 是 $t-s\in p\mathbb Z$，即 $\exists n:\mathbb Z,\ t-s=np$，
  绑定 `AddCircle.coe_sub` 与 `AddCircle.coe_eq_zero_iff`。
  它丢失 lift 的整数绕行，保留模 $p$ 的相位；`Real.Angle` 是周期 $2\pi$ 的表示。
- **圆的旋转盲接口。** 这是与覆盖不同的 $\Gamma$。站点是声明的 diagonal rotation action，
  状态是 $\Theta^m$（`Fin m → AddCircle p`），$m>0$，作用是 $z_j\mapsto z_j+\delta$。
  完整 invariant classifier 是 orbit quotient，其 kernel 是
  $z\sim w\Longleftrightarrow\exists\delta:\Theta,\ \forall j,\ w_j=z_j+\delta$。
  全部 pairwise differences $z_j-z_k$ 分类这些 orbits；相等差分以任一坐标确定共同平移。
  $m=1$ 时 quotient 只有一类，全部绝对相位不可见。只取部分 invariant readouts 时，
  orbit relation 仅包含于观测 kernel；声称相等须有 observational-completeness proof。
  普通紧圆无空间端点；全体 rotations 也不是保持加法零点的 automorphisms。
- **测度陈述。** 站点是 `MeasureTheory.ae μ`，绑定确切的 measure $\mu$ 与 measurable space；
  状态是 `Filter.Germ (MeasureTheory.ae μ) Y`，局部化 kernel 是 `f =ᶠ[MeasureTheory.ae μ] g`，
  即 $\mu(\{x\mid f(x)\ne g(x)\})=0$。`MeasureTheory.AEEqFun` 另要求其 a.e. 强可测域，
  不与任意函数的 filter germs 混同。积分模板只取实际积分读数，不自动附加完整 a.e. class。
- **积。** 乘积读数的安全规则是
  $\ker(q_X\times q_Y)((x,y),(x',y'))\Longleftrightarrow
  \ker(q_X)(x,x')\land\ker(q_Y)(y,y')$。
  diagonal actions 不是 independent product actions：圆对的共同旋转保留相对相位，独立旋转不保留。
  不得推断 $\operatorname{End}(X\times Y)=\operatorname{End}(X)\times\operatorname{End}(Y)$；
  这里 End 指空间 ends，$\mathbb R$ 有两端而 $\mathbb R^2$ 有一端，故该积等式不成立。
  有限积的 germ 构造可用有限个 eventual domains 的交；无限积交换必须另证，不由逐坐标相等推出。

**机械分工与策略边界。** elaboration 决定陈述实际使用的 carrier、结构实例、filter、
period、measure 与参数位置，包括 `Tendsto` 的 source／target；表面出现或 binder 数不建立 arena。
registry 按结构与参数提供 sites、state constructors、kernel／factorization lemmas 和适用假设。
policy 决定 observation language，必须每个 $\Gamma$ 一次冻结，绝不逐 theorem 选择。
registry lookup key 不取代 canonical arena declaration 的 catalog ownership；
同一 arena 的 peers 不因 theorem 名称、读数表达式或系数不同而拆开。
支持范围外的陈述保留未解决的语义选择，不把 inference 失败当作不可达证明。

三个规范性反例固定如下，任何自动选择规则必须保留其区别；圆反例取 $p:\mathbb R$、$p>0$、
$\Theta=\texttt{AddCircle}\ p$：

1. **carrier 不定 locus。** 在同一 `Bool` pointwise arena，identity readout 的 kernel 是
   对角线，escape 为空；constant readout 的 kernel 是全关系，escape 恰为
   `(false, true)` 与 `(true, false)` 两个有序对。carrier 相同不使逃逸处相同。
2. **覆盖不等于相位。** `AddCircle p` 的出现只给出指定商表示，不授权删除相位。
   覆盖 kernel 是 $p\mathbb Z$ 的 lift 歧义；旋转盲 kernel 是共同相位的 orbit 歧义。
   不存在选取代表点的 rotation-equivariant section $\{*\}\to\Theta$：等变要求所选点被每个
   rotation 固定，而非零 rotation 没有固定点；选参考点或 branch 必须属于显式 $\Gamma$。
3. **同一陈述有两种忠实读法。** 在同一状态空间 $S=\Theta\times\Theta$，
   令 $T_\theta(x)=x+\theta$，陈述是 `Function.Injective Tθ`。
   本反例的 intervention domain 是全部函数 $h:\Theta\to\Theta$；绝对读数
   $c_{\rm abs}^h(x,y)=(h(x),h(y))$ 的 Law 是
   $\forall x\,y,\ \pi_1(c_{\rm abs}^h(x,y))=\pi_2(c_{\rm abs}^h(x,y))\to x=y$；
   相对读数 $c_{\rm rel}^h(x,y)=h(x)-h(y)$ 的 Law 是
   $\forall x\,y,\ c_{\rm rel}^h(x,y)=0\to x=y$。
   两个 Law 都对所有 $h$ uniformly equivalent 于 `Function.Injective h`，bridge 不用定理 proof；
   translation 满足 Law，constant function 不满足，且各读法的 generated slots 与声明坐标均 exact-use。
   在 $h=T_\theta$ 时，$K_{\rm abs}$ 是对角线，$K_{\rm rel}$ 是差分相等；
   对任意 $a\ne0$，$(0,0)\sim(a,a)$ 仅在相对读法成立，故两个 kernels 不等价。
   Law variation 与 exact-use 不选择 observation language，也不把这两种读法变成输出重编码。

**Γ 的数学证据要求。** 一个观测模型的解释须给出 statement／Law 对应、
允许 intervention domain 上的正负 realizations、逐槽 sensitivity 与适用 transports。
slot 出现不证明敏感性，carrier 名称不确定观测语言；全局函数到 germ 的局部化与
germ 到观测商的读数是不同映射。使用极限作为读数时，存在性与唯一性是该解释的前提。

生产登记通过具体 `Contract.Registration`、已 enrollment 的模板与源选择字段给出
解释。dependent-family 路径核对完整原 statement、实际 Law、equivalence、
whole-family intervention／sensitivity 与 observational dependence。
这些具体检查不构成按 carrier 自动选择任意 Γ 的通用算法。
`StructuralTheoremUnit` 作为数学对象的构造仍不等于完整登记或目录 strictness 证明。

**§5 的无限载体边界。** 在 §6.1 下，relations、kernel inclusion／equality／incomparability、
添加读数的单调性、由 separating pair 证明的 strictness、leave-one-out capture 与 overlap 的集合定义保留。
有限 catalog 上每个 pair 被多少 occurrences 分离的 multiplicity 仍是自然数，其 strata 构成 partition；
有序 capture layers 仍是不交集合。按关系外延相等取商的 generated family 仍有限，至多 $2^{|I|}$ 项；
meet 是交，join 必须是 §5.10 的 internal generated-closure join，不是 ambient equivalence-relation join。
数学上的有限 generated family 不给出无限状态上 kernel equality、inclusion 或完整 Hasse 图的可执行判定。
pair counts、denominators、exact rates、数值 gain／overlap／spectra 没有本契约提供的无限替代；
无限 cardinality 不能检测 strict inclusion，不能用基数相减恢复 unique capture。
本款不引入 entropy、measure 或概率；测度接口中的 $\mu$ 只绑定该接口，不产生逃逸率。

**诊断边界。** 生产诊断按第 31 节的具体编译输入与评定触发条件解释。
Γ 的抽象数学条件不自动成为生产诊断或准入检查。

---

### 6.3 Law-content layer

本层是 level 1 的 Law-content contract。level 0 是 §5 与 §6.2 的 states/readouts；level 1
是本款定义的 Law layer；level ≥ 2 是关于 level-1 objects 的 statements，并各自冻结
自己的 Γ、domain、support 与 variation certificates。每一层定义自己的 escape relation（可为空）：一对不同的 admissible objects 在该层所有
选定 readouts 上相等；非空 escape 须有这样一对的见证。上层不消除下层 escape；层间没有
completeness 或 progress guarantee。

固定 root、canonical arena $A$ 与 bundle signature $\sigma$。冻结 Law interface
$\Gamma_1$ 指定 operation slots、固定 definitions/hypotheses 与 transports，并给出
$\Omega_\Gamma\subseteq\operatorname{PrimitiveRealization}\ \sigma$。异构 bundles 在 $A$
上共用一个 domain；差异只能由 certified restriction maps 表达。occurrence catalog $I$
绑定 complete root/arena manifest。

对每个 occurrence $i$，在 theorem proof 生成前且不使用该 proof，生成 open statement
schema $P_i$ 与 $\operatorname{OpenLaw}_i:\Omega_\Gamma\to\operatorname{Prop}$，并给出
uniform certificate

$$
\forall r\in\Omega_\Gamma,\quad P_i(r)\leftrightarrow\operatorname{OpenLaw}_i(r),
$$

以及在 actual realization 的 exact specialization。native assertions 共用一个 actual
realization $a$，且 $\operatorname{OpenLaw}_i(a)$ 对所有 $i$ 成立；这同时固定 orientation
与 consistency。记 $L_i=\operatorname{OpenLaw}_i$。

定义

$$
\operatorname{LawForbidden}_i=\{r\in\Omega_\Gamma\mid\neg L_i(r)\},\qquad
\operatorname{LawModels}(S)=\{r\mid\forall i\in S,\ L_i(r)\},
$$

$$
\operatorname{LawUniqueExclusion}_i
=\operatorname{LawModels}(I\setminus\{i\})\setminus\operatorname{LawModels}(I).
$$

并定义

$$
\operatorname{LawEntailedInCatalog}_i\;\Longleftrightarrow\;
\operatorname{LawUniqueExclusion}_i=\varnothing\;\Longleftrightarrow\;
\forall r,\ (\forall j\ne i,\ L_j(r))\to L_i(r).
$$

蕴含偏序 $\operatorname{LawEntails}(P,Q):\Longleftrightarrow
\forall r\in\Omega_\Gamma, P(r)\to Q(r)$ 仅作 strength/redundancy report。作为 kernel
companion，定义 $\operatorname{LawAgreement}_i(r,s):\Longleftrightarrow
(L_i(r)\leftrightarrow L_i(s))$、

$$
KL_S=\bigcap_{i\in S}\operatorname{LawAgreement}_i,\qquad
\operatorname{LawPairEscape}(S)=KL_S\setminus\Delta_{\Omega_\Gamma},\qquad
\operatorname{LawUniquePair}_i=KL_{I\setminus\{i\}}\setminus KL_I.
$$

这是 §5 在 realizations 作 states、Laws 作 readouts 上的逐字 specialization。以 common
positive point $a$ 定向，因为 $P$ 与 $\neg P$ 有相同 kernel。exclusion-zero 与 pair-zero
是不同 verdict：在 $\mathrm{Bool}\times\mathrm{Bool}$ 上令 $L(a,b)=a$、
$Q(a,b)=a\land b$，则 $Q\Rightarrow L$，所以 $L$ 无 unique exclusion，但 pair
$((\mathrm{false},\mathrm{false}),(\mathrm{true},\mathrm{false}))$ 对 $Q$ agreement 而对 $L$
disagreement，故 $L$ 有 positive pair capture。$\operatorname{LawUniquePair}_i=\varnothing$（等价于 $KL_I=KL_{I\setminus\{i\}}$）在 common positive point
下蕴含 exclusion triviality，反之不成立。

§5 的精确实例取 $Z=D_X=\{(x,y)\mid x\ne y\}$ 与
$L_i(x,y):=K_i(x,y)$。于是 $\operatorname{LawModels}(S)=E_S$、
$\operatorname{LawForbidden}_i=Cap_i$、$\operatorname{LawUniqueExclusion}_i=U_i$，其
denominator 为 $|X|(|X|-1)$。这是 mathematical instance 而非 native registration，且
不需要 common satisfying point；在 $Z\times Z$ 上不增加第二个 pair denominator。

证书形式如下：exclusion-positive 是 admissible $r$，满足所有 peer Laws 且 $\neg L_i(r)$；
exclusion-zero 是 $\forall r$，peers 蕴含 $L_i(r)$；pair-positive 是
$KL_I\subseteq KL_{I\setminus\{i\}}$ 加上 admissible pair $(r,s)$，其 peers agreement
且在 $i$ 上 disagreement；pair-zero 是
$\forall r\ s,\ KL_{I\setminus\{i\}}(r,s)\to\operatorname{LawAgreement}_i(r,s)$。
有限 classifier $q:\Omega\to Q$ 在每个 Law factor through $q$ 且每个 classifier value 有
certified representative 时，可证 implication/equality/strictness；它不产生 $\Omega$ 上的
rate。realization spaces 即使 arena finite 也通常 infinite（function-space outputs），故
`decide` 不是 default；不使用 `native_decide` 或 new axioms。除非 $\Omega$ finite 且
enumerable，level 1 不定义 pair counts、rates、spectra 或其他 counted quantities。

下列 vacuity conditions 是 contract：closed truth/proof/certificate 只能作为 Law，且须
报告 Law-tautological；inconsistent peer conjunction 不得得分，必须有 common satisfying
point；每个 occurrence 使用同一个 frozen $\Omega_\Gamma$，per-theorem restriction、hypothesis
insertion 或 fixed-definition reinterpretation 触发 CHANGE-Γ；peers 绑定 complete manifest，
不得为制造 uniqueness 而挑选；unused/cancelled slots 需 exact support 与 Γ-declared
sensitivity。presentation collapse 也改变 level-1 object：registration bridge 不得用 actual
realization 的 proved facts 把 open statement（例如 reverse inclusion ∧ separation）简化为
separation；registered OpenLaw 必须是 uniform open schema，template library 不得以 theorem
truth reduction。这些数学模型的证据要求不改变第 31 节的具体生产诊断。

Law exclusion、entailment、pair capture 与 pair escape 是本节定义的数学关系，
不属于第 30 节的生产报告字段或 Seal 输入。

规范 fixture：取 $A=\mathrm{Fin}\,3$，$\sigma$ 为两个 Bool 值 readouts $f,g$，$\Omega_\Gamma$ 为全部
$(f,g)$ 对。下列两个开放 schema 是 distinct level-1 objects，当且仅当 $\Omega_\Gamma$ 含满足
separation 而不满足 reverse inclusion 的 realization；此域中 $f=(\mathrm{false},\mathrm{false},\mathrm{true})$、
$g=(\mathrm{false},\mathrm{true},\mathrm{true})$ 即是：pair $(0,1)$ 见证 separation，pair $(1,2)$ 反驳 reverse
inclusion。common positive realization 取 $f=(\mathrm{false},\mathrm{false},\mathrm{false})$、
$g=(\mathrm{false},\mathrm{true},\mathrm{true})$，它同时满足两个 schema：

$$
\text{separation}:\ \exists x\ y,\ f(x)=f(y)\land g(x)\ne g(y),
$$

$$
\text{strict refinement}:\ \text{separation}\land
\forall x\ y,\ g(x)=g(y)\to f(x)=f(y).
$$

strict refinement entails separation。所有与 separation uniform equivalent 的四种
presentations 是同一个 level-1 object。

## 7. 语义闭包刻画

### 7.1 其他定理的语义闭包

定义：

$$
\operatorname{SemanticClosure}(I^{-i})
=
\left\{
q:X\to Q
\;\middle|\;
K_{I^{-i}}\subseteq\ker(q)
\right\}.
$$

即 $q$ 在其他所有定理无法区分的每个 fiber 上保持常值。

### 7.2 零增益等价

有：

$$
\delta_i=0
\Longleftrightarrow
U_i=\varnothing
\Longleftrightarrow
K_I=K_{I^{-i}}
\Longleftrightarrow
c_i\in\operatorname{SemanticClosure}(I^{-i}).
$$

### 7.3 正增益等价

有：

$$
\delta_i>0
\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}
\Longleftrightarrow
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

这正是严格核新颖性准则在“当前完整族减去自身”上的内生应用。

---

## 8. 定理族不可约性

本节中的 $\mathcal T$、$I$ 与 $\delta_i$ 均指固定 $(R,A)$ 的 canonical maximal
catalog $C_{R,A}$；不可约性是 catalog-relative，而不是 theorem declaration 的全局属性。

### 8.1 定义

定义当前完整定理族语义不可约：

$$
\operatorname{Irredundant}(\mathcal T)
:\Longleftrightarrow
\forall i\in I,\quad\delta_i>0.
$$

### 8.2 闭包形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\quad
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

### 8.3 核形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\quad
K_I\subsetneq K_{I^{-i}}.
$$

### 8.4 witness 形式

等价地：

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i\in I,
\ \exists x_i,y_i,
\quad
\begin{cases}
\forall j\neq i,\ c_j(x_i)=c_j(y_i),\\
c_i(x_i)\neq c_i(y_i).
\end{cases}
$$

### 8.5 Catalog 全正判词

固定 catalog 的全正数学条件为下式；seal 成功只要求完整合法 catalog 的每个 occurrence 均获 kernel-certified positive 或 trivial disposition：

$$
\boxed{
\operatorname{CatalogIrredundant}(C_{R,A})
}
$$

系统不比较哪个定理“更漂亮”，也不规定增益必须大于某个人工阈值。严格正值已经是无任意参数的平凡／非平凡分界。

### 8.6 冗余索引与系统全正

定义完整零成员集合与 catalog 冗余判词：

$$
Z_{R,A}=\{i\in I_{R,A}\mid U^R_{A,i}=\varnothing\},
$$

$$
\operatorname{CatalogRedundant}(C_{R,A})
:\Longleftrightarrow Z_{R,A}\neq\varnothing.
$$

在有限非空 catalog 上：

$$
\operatorname{CatalogIrredundant}(C_{R,A})
\Longleftrightarrow Z_{R,A}=\varnothing
\Longleftrightarrow
\neg\operatorname{CatalogRedundant}(C_{R,A}).
$$

v4.2 指定恰好一个 canonical system root $R_\star$。定义：

$$
\operatorname{SystemCatalogIrredundant}(R_\star)
:\Longleftrightarrow
\bigwedge_{A\in\operatorname{Arenas}(R_\star)}
\operatorname{CatalogIrredundant}(C_{R_\star,A}).
$$

`InformationEscapeHierarchy.LayeredCapture` 的 `DesignatedRootCatalogSuite`
以 dependent `PackedCatalog` 承载同一 root 下各 arena 的目录；
`SystemCatalogIrredundant` 是这些目录不可约性的数学合取。
该数学命题不成为生产报告字段或 seal 的额外前置。

生产 seal 的 scope 取其所在 root 的实际 import closure。
局部 root 的完整成员核对不证明仓库全局覆盖。

### 8.7 Catalog-relative triviality

object arena 是显式 semantic input；系统不得从 theorem statement 的表面类型推断 arena，
canonical identity 是 `Arena`／`StructuralArena` declaration。替代表示只有经
`CIRPT-IE-022` 的具名 `Equiv` transport 才能声明同一分析。

`TrivialInCatalog` 是相对于固定完整 catalog 的零 unique capture；structural 版本是
`¬ StructurallyLowersEscape`。分类 seal 为每个 occurrence 携带 kernel-checked 的
`LowersEscape` 或 `TrivialInCatalog` 分支。zero unique capture 是 catalog-relative result，
分类成功、catalog irredundancy 与 first-freeze admission 是独立命题；all-zero catalog
不提供 positivity 或 scalar credit。

固定既有 kernels 时，$I\subseteq J$ 蕴含 $U_i(J)\subseteq U_i(I)$；加入 peer
不能恢复旧 occurrence 的 positivity。成员变化要求受影响的完整 catalog 重新 seal。
冻结 pin 绑定 theorem statement identity，不绑定 catalog-relative disposition。
每个 theorem 的观测集合包含其全部已登记 arenas 与逃逸处；全部 occurrence 均为 trivial
才能汇总为 trivial。任一固定 catalog 中的 positive occurrence 反驳保留该 occurrence 及
其 catalog 的观测集合上的全 trivial 汇总，不宣称对任意观测集合选择不变。
本节不建立标准 arena 覆盖或 transparent theorem 的完备性；缺少 realization 或
certificate 不构成 closed reason，也不证明不存在 faithful carrier。

level-0 trivial occurrence 的 `law_*` 按 §6.3 在同一完整 catalog 与冻结 Γ 上计算；
open schema 不预先加入待测 law 的 inclusion 假设，level-1 verdict 不把 level-0 trivial
升级为 level-0 positive，也不履行 `ObjectNovelty`。

本判词与 `CLAUDE.md` §3.2 的 `proof_shape` 正交，互不蕴含。content theorem 仍可能在
catalog 中零 unique capture；bind-only companion 不能仅凭 object-level positive escape
取得首次冻结资格。生产准入由现行 StrataLint 规则执行。

---

## 9. 平凡与冗余的纯数学定义

本节每个“平凡”“冗余”“可恢复”判词均相对于 occurrence 所在的 $(R,A,C_{R,A})$。
同一个 occurrence（`(canonical arena declaration, theoremName)`）可以出现在多个 root import
closures 或 analysis views 中而不改变其 identity；其 $K_{-i},U_i,\delta_i$ 必须针对它出现于其中的
每个 $C_{R,A}$ 重新计算。只有通过另一个具名、kernel-checked realization 登记到不同 canonical
arena 上，才产生新的 occurrence；“在某处为正”不蕴含它在当前 $C_{R,A}$ 中为正。

### 9.1 平凡定理对象

相对于当前完整族，定义：

$$
\operatorname{TrivialInCatalog}(i)
:\Longleftrightarrow
\delta_i=0.
$$

这不等价于 proof 很短，也不等价于 theorem 名称简单。

### 9.2 常值概念

若 $c_i$ 为常值函数，则：

$$
\ker(c_i)=X^2.
$$

因此：

$$
K_I=K_{I^{-i}},
$$

从而：

$$
\delta_i=0.
$$

### 9.3 可由其他联合读出恢复

若存在函数：

$$
r:\prod_{j\neq i}O_j\to O_i
$$

使：

$$
c_i=r\circ C_{I^{-i}},
$$

则：

$$
c_i\in\operatorname{SemanticClosure}(I^{-i}),
$$

从而：

$$
\delta_i=0.
$$

### 9.4 同核重述

若存在 $j\neq i$，且：

$$
\ker(c_i)=\ker(c_j),
$$

则在同时保留 $i,j$ 时：

$$
\delta_i=\delta_j=0.
$$

以下同核形式在完整数学 catalog 内具有零独有捕获。SealRow 可携带平凡性与闭包归属证明，SealCatalog 的 collisions 与 conclusion 可携带同核和冗余证明：

- 可逆改名；
- 输出类型同构；
- 布尔取反；
- 坐标重新编码；
- theorem alias；
- 完全相同 concept 的不同 proof；
- 只改变 theorem 名称的重复声明。

### 9.5 超集包装

若 $c_i$ 是其他读出的 product 包装，而包装中的每个坐标都已由别的定理独立存在，则 $c_i$ 可由其他联合读出恢复，故：

$$
\delta_i=0.
$$

反过来，如果只保留 product theorem，删除各坐标 theorem，则 product theorem 可以具有正增益。

系统不选择或删减不可约基；完整、非退化且合法的过完备族成功 seal，零成员认证为 `trivial_in_catalog`，catalog 的 `SealCatalog.conclusion` 携带冗余证明；待首次冻结对象自身为零时不获 positive admission。

更一般地，只要同一 catalog 中存在 $j\neq i$ 且 $K^R_{A,j}\subseteq K^R_{A,i}$，较细的
$j$ 已捕获 $i$ 能捕获的全部 pair，故 $U^R_{A,i}=\varnothing$。这包括但不限于同核
重述与 product 包装。

---

## 10. 重复、替代与基选择

以下结论全部是 maximal-catalog occurrence-relative；不同 canonical arenas 中的 theorem
名称相同或不同都不直接构成替代证据。只有同一 canonical arena 的 import-closure peers，
或经 `CIRPT-IE-022` 证明 transport 后的 kernels，才进入语义比较。

### 10.1 重复双方同时为零

若两个定理提供同一个核，留一计算会得到：

$$
\delta_i=0,
\qquad
\delta_j=0.
$$

这是正确结果，而不是系统无法决定“保留谁”。当前族确实不是不可约族。

完整目录保留双方；SealRow 携带各自的平凡性与闭包归属证明，SealCatalog.conclusion 携带冗余证明，collisions 可携带同核证明。报告核对完整目录，不生成逐成员统计。

### 10.2 不设置名称优先级

系统不得通过以下方式自动挑选重复代表：

- 文件路径字典序；
- theorem 名称长度；
- 提交时间；
- 作者身份；
- proof term 长度；
- 是否先出现；
- 人工 owner。

这些规则都不是信息逃逸数学。

### 10.3 多个不可约基

同一个联合核可能存在多个不同不可约生成族。系统允许每一个不可约族通过，但不在它们之间创造无根据的总排名。

因此系统解决的是：

$$
\text{当前族是否包含零边际成员？}
$$

而不是：

$$
\text{所有数学表达中哪一个基具有唯一审美最优性？}
$$

---

## 11. 次序、名称与表示不变性

### 11.1 索引置换不变性

若 $\pi:I\simeq I'$ 是索引等价，并据此重排定理族，则：

$$
\varepsilon(S)
=
\varepsilon(\pi(S)).
$$

对应定理的 $\delta_i$ 保持不变。

### 11.2 theorem 名称不变性

重命名 theorem declaration 不改变 $c_i$，因此不改变：

$$
K_S,
\quad
E_S,
\quad
\varepsilon(S),
\quad
\delta_i.
$$

### 11.3 输出双射不变性

若：

$$
f_i:O_i\simeq O_i',
$$

并替换：

$$
c_i'=f_i\circ c_i,
$$

则：

$$
\ker(c_i')=\ker(c_i),
$$

所有逃逸量不变。

### 11.4 proof term 不变性

只要原 theorem 的数学 concept 不变，替换证明项不会改变信息逃逸率。

所以系统不会因为：

- proof 更长；
- tactic 更多；
- 使用自动化；
- 手写 term；

而改变数学增益。

---

## 12. 信息熵解释

### 12.1 均匀状态变量

令随机变量 $X_0$ 在有限状态空间 $X$ 上均匀分布。

对 $S\subseteq I$，定义联合观察随机变量：

$$
Y_S=C_S(X_0).
$$

### 12.2 状态残余熵

定义：

$$
H_S=H(X_0\mid Y_S).
$$

加入更多 theorem concept 不会增加残余熵：

$$
S\subseteq T
\Longrightarrow
H_T\le H_S.
$$

### 12.3 留一条件信息

定理 $i$ 的熵增益是：

$$
\Delta H_i
=
H(X_0\mid Y_{I^{-i}})
-
H(X_0\mid Y_I).
$$

由于 $c_i(X_0)$ 是 $X_0$ 的确定函数：

$$
\Delta H_i
=
I(X_0;c_i(X_0)\mid Y_{I^{-i}})
=
H(c_i(X_0)\mid Y_{I^{-i}}).
$$

### 12.4 正值等价

在均匀全支撑有限分布下：

$$
\Delta H_i>0
\Longleftrightarrow
U_i\neq\varnothing.
$$

所以 kernel-counting 版本与 Shannon 版本在“是否严格提供独有信息”上完全一致。

### 12.5 有限非平凡性的 pair counting 刻画

Shannon entropy 包含对数和实数运算，通常是 `noncomputable` 或需要额外解析证明。pair counting：

- 完全精确；
- 只使用 `Nat` 与 `Rat`；
- 可由 `decide`／`native_decide` 计算；
- 与严格正条件等价；
- 不引入浮点误差。

故有限目录的正增益条件可由 $|U_i|>0$ 刻画；熵值是数学等价投影。

---

## 13. 增强定理

### 13.1 原定理

对每个 $i\in I$：

$$
p_i:P_i.
$$

### 13.2 伴随逃逸降低命题

定义：

$$
G_i
:=
\operatorname{LowersEscape}(\mathcal T,i).
$$

### 13.3 增强陈述

定义：

$$
\widehat P_i
:=
P_i\land G_i.
$$

### 13.4 增强证明

若编译计算得到：

$$
g_i:G_i,
$$

则：

$$
\widehat p_i
:=
\langle p_i,g_i\rangle
:
\widehat P_i.
$$

### 13.5 原声明与契约证据

原 theorem 保持原名、陈述与证明。增强命题是上述数学构造，不要求生成额外的具名定理。
`Contract.SealRow.conclusion` 在 exact catalog/index 上保存 positive 的降低逃逸证明，
或 zero 的平凡性与剩余目录闭包归属证明。报告只核对编译字段与登记目录的对应关系。

---

## 14. 一次编译而非历史比较

### 14.1 内部反事实

系统唯一比较的是：

$$
\mathcal T
\quad\text{与}\quad
\mathcal T\setminus\{\tau_i\}.
$$

二者都由当前编译中的同一个有限 catalog 纯函数生成。

### 14.2 不存在持久 baseline

规范中禁止：

```text
previous_snapshot
parent_commit
baseline_catalog
accepted_before
candidate_after
```

### 14.3 不存在顺序边际

系统不按：

$$
\tau_1,\tau_2,\ldots,\tau_n
$$

依次计算贡献。所有 $\delta_i$ 都相对于同一个完整族同步计算，因此结果与声明顺序无关。

### 14.4 新 theorem 可以使旧 theorem 变零

若加入新 theorem 后，旧 theorem 已可由其余族恢复，则旧 theorem 的 leave-one-out 增益会变为零。

这不是评价体系变化，而是当前数学族从不可约变成过完备。

完整合法族重新构造 Seal，旧 theorem 在扩大的目录内可成为平凡成员，冗余证明由 `SealCatalog.conclusion` 携带。旧成员仍保留；报告核对不另设首次冻结正性准入门。

特别地，若新 peer 的 kernel 严格细化旧 occurrence 的 kernel，则旧 occurrence 的
leave-one-out capture 必为零。严格 refinement chain 的每个相邻增量可以非空，同时
它的累计粗层在 flat catalog 中为零；两种量不得混称。

---

## 15. 系统自应用

### 15.1 系统数学也是定理对象

定义 `jointKernel`、`escapePairs`、`uniqueCapture`、`LowersEscape` 并证明其性质的 Lean theorem，与其他数学 theorem 没有本体差异。

只要它们被构造成相应数学 arena 中的 theorem unit，就由同一公式计算：

$$
\delta_i
=
\varepsilon(I^{-i})-\varepsilon(I).
$$

### 15.2 不特殊豁免系统 theorem

系统不得写：

```text
if theorem.namespace == ResearchAudit then accept
```

系统核心 authored theorem 与普通 authored theorem 使用同一个 registry 和同一个 `LowersEscape` 定义。

no-exemption 同时覆盖 namespace、auxiliary root、alternate catalog、cloned/wrapper
arena 与 positive-elsewhere。任何一项都不得用来避开同一 canonical arena 的 maximal
peer grouping；一个 theorem 只有在不同 canonical arenas 上经独立、kernel-checked
realizations 才可有多个 designated occurrences，并必须在每个 occurrence 所在的 maximal
catalog 中分别为正。

### 15.3 封印数据不是数学 theorem

`Contract.Seal` 是带类型的契约数据声明，不作为被分析 concept 加入 catalog。Lean 编译期检查同一目录上的非退化性、bundle 非空、逐成员降低逃逸或平凡性及闭包归属、kernel 碰撞与目录结论的数学义务；报告期只读取编译产物并核对登记、目录及证据的结构对应。

其数学正确性由普通 Lean theorem 证明，而这些 soundness theorem 本身可以进入 catalog 接受自应用。

这样避免：

$$
\text{seal theorem 必须为自己生成 seal theorem}
$$

的无穷回归。

### 15.4 契约证明字段不是新信息 concept

Seal 的数学字段是现有 theorem unit 性质的证明项，不被重新登记为 theorem primitive unit。
被观察概念与其性质的证明项分别承担对象与证据职责；报告不生成降低逃逸、增强、
平凡性或系统冗余的具名伴随定理。

---

## 16. 纯数学核心定理清单

以下 theorem 必须在 Lean 内正式证明。

### IE-001　联合核反单调

$$
S\subseteq T
\Longrightarrow
K_T\subseteq K_S.
$$

### IE-002　逃逸集合反单调

$$
S\subseteq T
\Longrightarrow
E_T\subseteq E_S.
$$

### IE-003　单 theorem 加入律

$$
K_{S\cup\{i\}}
=
K_S\cap\ker(c_i).
$$

### IE-004　单 theorem 逃逸加入律

$$
E_{S\cup\{i\}}
=
E_S\cap\ker(c_i).
$$

### IE-005　留一包含

$$
E_I\subseteq E_{I^{-i}}.
$$

### IE-006　独有捕获分割

$$
E_{I^{-i}}
=
E_I\;\dot\cup\;U_i.
$$

### IE-007　精确计数差

$$
|E_{I^{-i}}|
=
|E_I|+|U_i|.
$$

### IE-008　增益公式

$$
\delta_i
=
\frac{|U_i|}{|X|(|X|-1)}.
$$

### IE-009　正增益 witness

$$
\delta_i>0
\Longleftrightarrow
\exists x,y,
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y).
$$

### IE-010　严格核等价

$$
\delta_i>0
\Longleftrightarrow
K_I\subsetneq K_{I^{-i}}.
$$

### IE-011　语义闭包零增益

$$
\delta_i=0
\Longleftrightarrow
c_i\in\operatorname{SemanticClosure}(I^{-i}).
$$

### IE-012　可恢复概念零增益

若：

$$
c_i=r\circ C_{I^{-i}},
$$

则：

$$
\delta_i=0.
$$

### IE-013　同核双零

若 $i\neq j$ 且：

$$
\ker(c_i)=\ker(c_j),
$$

则：

$$
\delta_i=\delta_j=0.
$$

### IE-014　常值零增益

若 $c_i$ 为常值，则：

$$
\delta_i=0.
$$

### IE-015　索引置换不变

定理重排不改变对应增益。

### IE-016　输出等价不变

对输出施加双射不改变增益。

### IE-017　全族不可约等价

$$
\operatorname{Irredundant}(\mathcal T)
\Longleftrightarrow
\forall i,\delta_i>0.
$$

### IE-018　碰撞概率表示

$$
\varepsilon(S)
=
\Pr[C_S(X_1)=C_S(X_2)\mid X_1\neq X_2].
$$

### IE-019　条件信息表示

$$
\Delta H_i
=
I(X_0;c_i(X_0)\mid C_{I^{-i}}(X_0)).
$$

### IE-020　正熵与正 pair 增益等价

在有限均匀全支撑条件下：

$$
\Delta H_i>0
\Longleftrightarrow
|U_i|>0.
$$

### IE-021　均匀测度唯一性

有限非对角 pair 空间上，置换不变概率测度唯一等于归一化计数测度。

### IE-022　增强 theorem 构造

$$
P_i\to G_i\to(P_i\land G_i).
$$

### IE-023　全 catalog 增强

若：

$$
\forall i,\ G_i,
$$

则：

$$
\forall i,\ \widehat P_i.
$$

### IE-024　`uniqueCapturePairs_pairwise_disjoint`

同一 $(R,A)$ 中 $i\neq j$ 时：

$$
U^R_{A,i}\cap U^R_{A,j}=\varnothing.
$$

### IE-025　`sum_uniqueCaptureCount_le_capturedCount`

$$
\sum_{i\in I_{R,A}}|U^R_{A,i}|
\le |D_A\setminus E^R_A|.
$$

### IE-026　`pairwiseCaptureOverlap_comm`

$$
O^R_{A,ij}=O^R_{A,ji},
\qquad
O^R_{A,ii}=\operatorname{Cap}^R_{A,i}.
$$

### IE-027　`kernelRefines_preorder`

`KernelRefines` 自反且传递；按 kernel equality 取商后为 partial order。并且：

$$
K^R_{A,i}\subseteq K^R_{A,j}
\Longleftrightarrow
\operatorname{Cap}^R_{A,j}\subseteq\operatorname{Cap}^R_{A,i}.
$$

### IE-028　`kernelRefines_implies_zero_uniqueCapture`

若 $i\neq j$ 且 $K^R_{A,i}\subseteq K^R_{A,j}$，则：

$$
U^R_{A,j}=\varnothing,
\qquad |U^R_{A,j}|=0.
$$

### IE-029　`catalogRedundant_iff_exists_zero`

有限非空 catalog 上：

$$
\operatorname{CatalogRedundant}(C_{R,A})
\Longleftrightarrow
\exists i,\ |U^R_{A,i}|=0
\Longleftrightarrow
\neg\operatorname{CatalogIrredundant}(C_{R,A}).
$$

### IE-030　`captureSpectrum_sum_eq_denominator`

$$
\sum_k h^R_A(k)=|D_A|.
$$

### IE-031　`captureSpectrum_zero_eq_fullEscape`

$$
h^R_A(0)=|E^R_A|.
$$

### IE-032　`captureSpectrum_one_eq_sum_unique`

$$
h^R_A(1)=\sum_i|U^R_{A,i}|.
$$

### IE-033　`captureSpectrum_incidence_double_count`

$$
\sum_k k\,h^R_A(k)=\sum_i|\operatorname{Cap}^R_{A,i}|.
$$

### IE-034　`Catalog.pairwiseOverlap_spectrum_doubleCount`

$$
\sum_{i\in I_{R,A}}\ \sum_{j\in I_{R,A}\setminus\{i\}}
|O^R_{A,ij}|
=\sum_k k(k-1)h^R_A(k).
$$

规范 Lean signature 不假设 `Catalog.Index` 有序，并把所有 typeclass 使用封装在可执行定义体内：

```lean
def Catalog.orderedDistinctOverlapTotal (catalog : Catalog arena) : Nat := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  exact ∑ i : catalog.Index,
    ∑ j in (Finset.univ : Finset catalog.Index).erase i,
      catalog.pairwiseCaptureOverlapCount i j

def Catalog.captureSpectrumSecondFactorialMoment
    (catalog : Catalog arena) : Nat := by
  letI := catalog.indexFintype
  exact ∑ k : Fin (@Fintype.card catalog.Index catalog.indexFintype + 1),
    k.1 * (k.1 - 1) * catalog.captureSpectrum k

theorem Catalog.pairwiseOverlap_spectrum_doubleCount
    (catalog : Catalog arena) :
    catalog.orderedDistinctOverlapTotal =
      catalog.captureSpectrumSecondFactorialMoment := by
  ...
```

左侧是 unordered-pair overlap 总量的两倍，故 theorem 对任何额外选择的
`[LinearOrder catalog.Index]` 都不变。

### IE-035　`catalogRoleHistogram_sum`

若 $H^R_{A,i}(s)$ 是 occurrence $i$ 在非零四位 role signature $s$ 上的 unique-capture
histogram，且 $H^R_A(s)=\sum_iH^R_{A,i}(s)$，则：

$$
\sum_sH^R_A(s)=\sum_i|U^R_{A,i}|=h^R_A(1).
$$

### IE-036　`layeredCapture_partition`

对任何 certified chain $K_\ell\subseteq\cdots\subseteq K_0$：

$$
D_A=L_0\;\dot\cup\cdots\dot\cup\;L_\ell\;\dot\cup\;R_\ell.
$$

### IE-037　`strictRefinement_iff_layeredCapture_nonempty`

初层及后续层的完整非空判据为：

$$
L_0\neq\varnothing
\Longleftrightarrow D_A\nsubseteq K_0
\Longleftrightarrow \exists x\ne y,\ \neg K_0(x,y),
$$

且对 $1\le r\le\ell$：

$$
K_r\subsetneq K_{r-1}
\Longleftrightarrow
L_r\neq\varnothing.
$$

### IE-038　`cumulativeChain_coarser_uniqueCapture_zero`

若 flat catalog 中有 $i\neq j$ 且 $K_j\subseteq K_i$，则 $U_i=\varnothing$。因此
strict cumulative chain 不蕴含每个 flat member 的 leave-one-out capture 为正。

### IE-039　`systemWidePositive_iff_systemCatalogIrredundant`

对显式指定的 system root $R_\star$：

$$
\operatorname{SystemCatalogIrredundant}(R_\star)
\Longleftrightarrow
\forall A\in\operatorname{Arenas}(R_\star),\
\operatorname{CatalogIrredundant}(C_{R_\star,A}).
$$

### IE-040　`generatedKernel_union`

对任意 $S,T\subseteq I$：

$$
K_{S\cup T}=K_S\cap K_T.
$$

等式是关系外延等式，并使 generated family 对 meet 封闭。

### IE-041　`generatedKernel_finite_lattice`

`GeneratedKernel C` 按 relation equality 取商、按 relation inclusion 排序后是 finite lattice；
top 为 $K_\varnothing$，bottom 为 $K_I$，meet 为 intersection，join 为 generated closure 内的
least upper bound。它的 Hasse diagram（lattice order 的 transitive reduction）为 path、因而
为 tree，当且仅当全部 generated kernels 两两可比；full strict generator-transition DAG
可含跨 Hasse levels 的 shortcut edges，即使 lattice 是 chain 也一般不是 tree。存在不可比
kernels 时其 internal meet/join 给出 diamond。对 $N$-state arena，任何 strict refinement
chain 长度至多 $N-1$。

### IE-042　`generatorStep_wellDefined`

若 $K_S=K_T$，则对任意 $i$：

$$
K_{S\cup\{i\}}=K_{T\cup\{i\}}.
$$

因此“加入 $i$”在 extensional quotient 上良定义；相等结果只能记
`collapsed_addition`，严格结果才能记 edge。

### IE-043　`escape_antitone_on_step`

若 $P\xrightarrow{i}Q$，则：

$$
\operatorname{escapeAt}(Q)\subseteq\operatorname{escapeAt}(P).
$$

### IE-044　`strict_kernel_iff_nonempty_increment`

对 generator step $Q\le P$：

$$
K_Q\subsetneq K_P
\Longleftrightarrow
\operatorname{edgeCapture}(P,Q)\ne\varnothing.
$$

在 finite arena 上又等价于其 reflected count 严格为正。

### IE-045　`chain_increment_pairwise_disjoint`

任一 certified `GeneratorSchedule` 的逐步 increments 两两不交；classified `collapsed` step 的
increment 是空集并贡献 $0$。

### IE-046　`chain_increment_union`

若 `GeneratorSchedule` 从 $P_0$ 到 $P_\ell$，则：

$$
\mathop{\dot\bigcup}_{r=1}^{\ell}
\operatorname{edgeCapture}(P_{r-1},P_r)
=
\operatorname{escapeAt}(P_0)\setminus\operatorname{escapeAt}(P_\ell).
$$

### IE-047　`chain_count_telescopes`

有限 arena 的 `GeneratorSchedule` 上（含 collapsed steps）：

$$
\sum_{r=1}^{\ell}|\operatorname{edgeCapture}(P_{r-1},P_r)|
=|\operatorname{escapeAt}(P_0)|-|\operatorname{escapeAt}(P_\ell)|.
$$

实现可使用无截断加法等式表达，不能用 `Nat` 截断减法掩盖 inclusion failure。

### IE-048　`terminal_order_independent`

从有效 `GeneratorSchedule` 删除 classified `collapsed` steps 得 `StrictKernelChain`。任何由
恰好加入同一 generator set $S$ 的 schedules 得到的 strict chains，其 terminal node 都是同一个
extensional $K_S$；特别地，加入全部 $I$ 的每条 strict decomposition 都终止于 $K_I$，terminal
escape 与总 capture 不依赖 strict path。

### IE-049　`last_step_eq_uniqueCapture`

若一个完整 `GeneratorSchedule` 先恰好加入 $I\setminus\{i\}$、最后加入 $i$，则最后 increment
（无论 classified `strict` 或 `collapsed`）为：

$$
\operatorname{edgeCapture}(K_{I\setminus\{i\}},K_I)=U_i.
$$

它把 chain marginal 与 order-free leave-one-out invariant 精确连接；其他顺序中的 $i$-step
不得冒称 $U_i$。

### IE-050　`nested_flat_coarse_zero`

若 flat catalog 中 $i\ne j$ 且 $K_j\subseteq K_i$，则 $U_i=\varnothing$。这重述并推广
IE-038 到 generated-kernel hierarchy 的 node language。

### IE-051　`spectrum_total` / `spectrum_zero`

full-catalog spectrum 满足：

$$
\sum_k h(k)=|D_A|,
\qquad h(0)=|\operatorname{escapeAt}(K_I)|.
$$

### IE-052　`spectrum_unique`

$$
h(1)=\sum_i|U_i|.
$$

### IE-053　`spectrum_first_moment`

$$
\sum_k k h(k)=\sum_i|\operatorname{Cap}_i|.
$$

### IE-054　`spectrum_second_moment` / `overlap_symmetric_diagonal`

$$
\sum_k k(k-1)h(k)
=\sum_i\sum_{j\ne i}|O_{ij}|,
$$

并且 $O_{ij}=O_{ji}$、$O_{ii}=\operatorname{Cap}_i$。这些量只由 full catalog 决定，
与 certified chain 的选择无关。

### IE-055　`refinement_overlap`

若 $K_i\subseteq K_j$，则：

$$
\operatorname{Cap}_j\subseteq\operatorname{Cap}_i,
\qquad O_{ij}=\operatorname{Cap}_j.
$$

true refinement cell 必须携 inclusion proof；false cell 必须携反例 pair。hash、layout 或
heuristic order 均不能证明本律。

---

# 第二部　C-IRPT 概念原语与统一信息逃逸演算

## 本部地位

本部把 `docs/develop/theory/CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md` 中的四个模型角色

$$
\mathsf{CUT},\qquad
\mathsf{FLOW},\qquad
\mathsf{ADMIT},\qquad
\mathsf{ANCHOR}
$$

接入前述单次编译信息逃逸体系。

本部不把四者声明为新的逻辑公理。它们仍然递归展开为类型、函数、谓词、依赖项和相等证明。新增结论是：

$$
\boxed{
\text{四种角色虽然语义职责不同，但其信息区分能力都有统一的 kernel 正规形。}
}
$$

因此，系统不需要为 CUT、FLOW、ADMIT、ANCHOR 各写一套评分器。它只需要一套作用于等价核、联合核与核差的数学演算。

本部使用的源文档版本为：

```text
docs/develop/theory/CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md
version: v5.0
git blob: 9910c3d1b7efd16ae9587ad14368de781a7319a9
```

---

## CIRPT-1　统一计算的第一对象不是输出值，而是不可区分核

固定状态类型：

$$
X:\mathrm{Type}.
$$

任意读出：

$$
f:X\to Y
$$

诱导等价关系：

$$
\ker(f)
=
\{(x,y)\in X^2:f(x)=f(y)\}.
$$

信息逃逸只依赖该等价关系，而不依赖：

- 输出类型名称；
- 输出值的编码；
- theorem 名称；
- proof term 的写法；
- 使用哪一种与原输出双射的坐标表示。

若：

$$
\ker(f)=\ker(g),
$$

则 $f$ 与 $g$ 在本体系中具有完全相同的区分能力，并对任意 catalog 产生完全相同的信息逃逸数、留一增益和伴随命题真假值。

因此本部采用：

$$
\boxed{
\text{kernel 是统一计算接口，readout 是 kernel 的一种实现。}
}
$$

---

## CIRPT-2　四原语的 kernel 化

### CIRPT-2.1　CUT kernel

给定 CUT：

$$
q:X\to B,
$$

定义：

$$
\kappa_{\mathsf C}(q)(x,y)
\iff
q(x)=q(y).
$$

这就是项目已有的 `conceptKernel`／`Setoid.ker q`。

### CIRPT-2.2　FLOW kernel

给定单步 FLOW：

$$
F:X\to Y,
$$

其完整输出 kernel 为：

$$
\kappa_{\mathsf F}(F)(x,y)
\iff
F(x)=F(y).
$$

若目标只观察 $Y$ 上的 CUT：

$$
q_Y:Y\to C,
$$

则可见 FLOW kernel 为：

$$
\kappa_{\mathsf F}(F;q_Y)(x,y)
\iff
q_Y(Fx)=q_Y(Fy).
$$

对动作族：

$$
F:U\to X\to Y,
$$

其联合 FLOW kernel 为：

$$
\kappa_{\mathsf F}^{U}(F)(x,y)
\iff
\forall u:U,\quad F_u(x)=F_u(y).
$$

它等于联合读出：

$$
\beta_F(x)(u)=F_u(x)
$$

的 kernel。

### CIRPT-2.3　ADMIT kernel

给定 ADMIT：

$$
A:X\to\mathsf{Prop},
$$

定义：

$$
\kappa_{\mathsf A}(A)(x,y)
\iff
\bigl(A(x)\leftrightarrow A(y)\bigr).
$$

该关系只判断两个状态是否具有相同准入真值，不把 ADMIT 当作删除状态的过滤器。

在有限可执行层，若有：

$$
\forall x,\ \mathrm{Decidable}(A(x)),
$$

则定义 canonical Boolean readout：

$$
\chi_A(x)=\mathrm{decide}(A(x)):\mathrm{Bool},
$$

并有：

$$
\ker(\chi_A)=\kappa_{\mathsf A}(A).
$$

### CIRPT-2.4　ANCHOR kernel

给定 ANCHOR：

$$
a:X,
$$

定义 pointed equality profile：

$$
\delta_a(x)
\iff
x=a.
$$

其 kernel 为：

$$
\kappa_{\mathsf H}(a)(x,y)
\iff
\bigl((x=a)\leftrightarrow(y=a)\bigr).
$$

在有限可执行层，若 `DecidableEq X`，则：

$$
\delta_a^b(x)=\mathrm{decide}(x=a):\mathrm{Bool}.
$$

这里下标 $\mathsf H$ 表示 anchor/history 轴，沿用 C-IRPT 四重缺陷记号。

---

## CIRPT-3　四原语 kernel 都是等价关系

### 定理 CIRPT-IE-001　Primitive-kernel equivalence

对任意合法类型参数：

$$
\kappa_{\mathsf C}(q),
\quad
\kappa_{\mathsf F}(F),
\quad
\kappa_{\mathsf A}(A),
\quad
\kappa_{\mathsf H}(a)
$$

均满足自反、对称和传递。

因此四种角色都定义一个：

$$
\operatorname{Setoid}(X).
$$

证明不使用任何信息论假设，只使用：

- 输出相等的等价性；
- 命题双蕴涵的等价性；
- pointed equality truth value 的等价性。

---

## CIRPT-4　kernel 正规形定理：全部角色都可 CUT 化

给定任意 setoid：

$$
K:\operatorname{Setoid}(X),
$$

定义商投影：

$$
\pi_K:X\to X/K.
$$

则：

$$
\boxed{
\pi_K(x)=\pi_K(y)
\iff
K(x,y).
}
$$

### 定理 CIRPT-IE-002　Quotient CUT normal form

每个 C-IRPT primitive kernel 都存在一个 canonical CUT：

$$
q_K:X\to\operatorname{Quotient}(K),
$$

使：

$$
\ker(q_K)=K.
$$

所以：

$$
\boxed{
\mathsf{CUT},\mathsf{FLOW},\mathsf{ADMIT},\mathsf{ANCHOR}
\text{ 在信息区分层都可正规化为一个 CUT。}
}
$$

这不表示四个角色在模型语义上相同。它只表示：

> 当问题限定为“哪些状态对仍无法区分”时，四者共享同一 kernel 计算接口。

角色标签仍然保留：

- CUT 表示分类接口；
- FLOW 表示作用；
- ADMIT 表示合法性；
- ANCHOR 表示实际见证。

kernel 正规形只抽取它们的区分结构，不取代其完整语义。

---

## CIRPT-5　有限 primitive bundle 与联合 kernel

一个 primitive bundle 是有限依赖族：

$$
\Pi=(J,\alpha,\kappa),
$$

其中：

- $J$ 是有限 primitive 索引类型；
- $\alpha:J\to\{\mathsf C,\mathsf F,\mathsf A,\mathsf H\}$ 是角色轴；
- $\kappa_j$ 是相应 primitive 在 $X$ 上的 kernel。

定义 bundle 联合 kernel：

$$
\boxed{
K_\Pi(x,y)
\iff
\forall j:J,\quad \kappa_j(x,y).
}
$$

### 定理 CIRPT-IE-003　Bundle joint-kernel law

若每个 primitive 通过 CUT 正规形表示为 $q_j$，则：

$$
K_\Pi
=
\ker\left(x\mapsto(j\mapsto q_j(x))\right)
=
\bigcap_{j:J}\kappa_j.
$$

因此任意有限 primitive bundle 仍然等价于一个联合 CUT。

---

## CIRPT-6　C-IRPT 表达式的统一 kernel 语义

本规范允许由 primitive 通过以下保守操作形成表达式：

1. 有限或依赖联合；
2. 函数组合；
3. FLOW 迭代；
4. 动作词行为 trace；
5. CUT 精化；
6. 目标 readout 配对；
7. ADMIT Boolean 化；
8. ANCHOR pointed profile；
9. 已有 `conceptJoin`、`jointReadout` 和 `controlledBehavior`。

每个表达式 $e$ 都递归产生一个等价核：

$$
\llbracket e\rrbracket_K:\operatorname{Setoid}(X).
$$

### 定理 CIRPT-IE-004　Primitive-expression kernel normalization

对每个由上述构造形成的 C-IRPT 表达式 $e$，存在 CUT：

$$
N(e):X\to Q_e
$$

满足：

$$
\ker N(e)=\llbracket e\rrbracket_K.
$$

证明可以采用两条等价路线：

- 对表达式递归构造联合 readout；
- 先递归构造 setoid，再取 quotient CUT。

第二条路线给出最一般的结构定理；第一条路线给出有限可执行实现。

---

## CIRPT-7　统一目标残差

给定当前可见 kernel $K$ 与目标 kernel $L$，定义：

$$
\boxed{
\operatorname{Residual}(K,L)
=
K\setminus L.
}
$$

即：

$$
(x,y)\in\operatorname{Residual}(K,L)
\iff
K(x,y)\land\neg L(x,y).
$$

若：

$$
K=\ker q,
\qquad
L=\ker T,
$$

则恢复项目 canonical 定义：

$$
\operatorname{Residual}(K,L)
=
\operatorname{defectRelation}(q,T).
$$

所以本规范的统一计算器不新建第二个 residual 概念；它只是把现有 `defectRelation` 提升为 kernel 参数化形式。

### 定理 CIRPT-IE-005　Residual extensionality

若：

$$
K=K',
\qquad
L=L',
$$

则：

$$
\operatorname{Residual}(K,L)
=
\operatorname{Residual}(K',L').
$$

因此所有计算都对同核表示不变。

---

## CIRPT-8　绝对逃逸只是 identity target 特化

令离散 identity kernel：

$$
\Delta_X(x,y)\iff x=y.
$$

定义 kernel $K$ 的绝对信息逃逸：

$$
\boxed{
\operatorname{Escape}(K)
=
\operatorname{Residual}(K,\Delta_X)
=K\setminus\Delta_X.
}
$$

因此本文第一部的：

$$
E_S=K_S\setminus\Delta_X
$$

是统一 residual 演算的 identity-target 特例。

---

## CIRPT-9　多目标统一：残差的并定理

设目标 primitive family 为：

$$
L_j,\qquad j:J,
$$

联合目标 kernel 为：

$$
L_J=\bigcap_{j:J}L_j.
$$

### 定理 CIRPT-IE-006　Residual of a joint target

$$
\boxed{
\operatorname{Residual}(K,L_J)
=
\bigcup_{j:J}\operatorname{Residual}(K,L_j).
}
$$

证明是集合恒等式：

$$
K\setminus\bigcap_jL_j
=
K\cap\bigcup_jL_j^c
=
\bigcup_j(K\setminus L_j).
$$

这一定理是统一计算能力的中心：

> 任意数量、任意角色的目标 primitive 可以先联合，再用同一个 residual 函数计算；其总残差恰好是各角色残差的并。

总量不是各分量简单相加，因为同一个 pair 可以同时违反多个角色。统一计算必须对并集精确计数，从而自动避免重复记账。

---

## CIRPT-10　四角色缺陷全部是同一 residual 的实例

固定：

$$
q:X\to B,
\qquad
T:X\to Z,
\qquad
F:X\to Y,
\qquad
q_Y:Y\to C,
\qquad
A:X\to\mathsf{Prop},
\qquad
a:X.
$$

令当前 kernel：

$$
K_q=\ker q.
$$

### CIRPT-10.1　CUT 缺陷

$$
\boxed{
D_{\mathsf C}(q,T)
=
\operatorname{Residual}(K_q,\ker T).
}
$$

即：

$$
q(x)=q(y),
\qquad
T(x)\ne T(y).
$$

### CIRPT-10.2　FLOW 缺陷

$$
\boxed{
D_{\mathsf F}(F;q,q_Y)
=
\operatorname{Residual}
\bigl(K_q,\ker(q_Y\circ F)\bigr).
}
$$

即 C-IRPT 的 causal carry。

### CIRPT-10.3　ADMIT 缺陷

$$
\boxed{
D_{\mathsf A}(q,A)
=
\operatorname{Residual}
\bigl(K_q,\kappa_{\mathsf A}(A)\bigr).
}
$$

展开为：

$$
q(x)=q(y)
\land
\neg(A(x)\leftrightarrow A(y)).
$$

这正是 mixed admissibility fiber。

### CIRPT-10.4　ANCHOR 缺陷

定义对称 anchor defect：

$$
\boxed{
D_{\mathsf H}^{\mathrm{sym}}(q,a)
=
\operatorname{Residual}
\bigl(K_q,\kappa_{\mathsf H}(a)\bigr).
}
$$

展开为：

$$
q(x)=q(y)
\land
\neg\bigl((x=a)\leftrightarrow(y=a)\bigr).
$$

它表示同一 CUT 纤维中恰有一个端点是实际 anchor。

---

## CIRPT-11　ANCHOR shadow 与对称 residual 的精确桥

C-IRPT 定义：

$$
\operatorname{Shadow}_q(a)
=
\{x:q(x)=q(a)\land x\ne a\}.
$$

### 定理 CIRPT-IE-007　Anchor residual decomposition

$$
\boxed{
D_{\mathsf H}^{\mathrm{sym}}(q,a)
=
\bigl(\{a\}\times\operatorname{Shadow}_q(a)\bigr)
\cup
\bigl(\operatorname{Shadow}_q(a)\times\{a\}\bigr).
}
$$

两部分不交，因此在有限 $X$ 上：

$$
\boxed{
\left|D_{\mathsf H}^{\mathrm{sym}}(q,a)\right|
=
2\left|\operatorname{Shadow}_q(a)\right|.
}
$$

于是：

$$
D_{\mathsf H}^{\mathrm{sym}}(q,a)=\varnothing
\iff
\operatorname{Shadow}_q(a)=\varnothing.
$$

所以已有 one-sided anchor shadow 与统一 ordered-pair 逃逸率完全兼容。

---

## CIRPT-12　ADMIT boundary 与统一 residual 的精确桥

C-IRPT 的准入边界非空，当且仅当一个 CUT fiber 同时含有合法和非法状态。

### 定理 CIRPT-IE-008　Admit boundary residual equivalence

$$
\boxed{
D_{\mathsf A}(q,A)\ne\varnothing
\iff
\partial_qA\ne\varnothing.
}
$$

并且：

$$
D_{\mathsf A}(q,A)=\varnothing
$$

等价于存在：

$$
\overline A:B\to\mathsf{Prop}
$$

使：

$$
A(x)\leftrightarrow\overline A(q(x)).
$$

因此准入下降不需要专用评价函数，它就是相同的 kernel residual 零判据。

---

## CIRPT-13　FLOW carry 与统一 residual 的精确桥

### 定理 CIRPT-IE-009　Flow carry residual equivalence

$$
\boxed{
D_{\mathsf F}(F;q,q_Y)\ne\varnothing
}
$$

当且仅当存在：

$$
x,y:X
$$

使：

$$
q(x)=q(y),
\qquad
q_Y(Fx)\ne q_Y(Fy).
$$

它又等价于：

$$
q_Y\circ F
$$

不能沿 $q$ 下降。

因此 FLOW 是否可见闭合，与 CUT target 是否可恢复是同一个 residual 判据。

---

## CIRPT-14　四角色联合 target 与总缺陷

定义四角色 target CUT：

$$
\Theta_\Sigma(x)
=
\left(
T(x),
q_Y(Fx),
\chi_A(x),
\delta_a^b(x)
\right).
$$

其 kernel 为：

$$
K_\Theta
=
\ker T
\cap
\ker(q_Y\circ F)
\cap
\kappa_{\mathsf A}(A)
\cap
\kappa_{\mathsf H}(a).
$$

定义统一四角色缺陷：

$$
\boxed{
D_{\mathrm{CIRPT}}(\Sigma)
=
\operatorname{Residual}(K_q,K_\Theta).
}
$$

### 定理 CIRPT-IE-010　Four-role residual union

$$
\boxed{
D_{\mathrm{CIRPT}}(\Sigma)
=
D_{\mathsf C}
\cup
D_{\mathsf F}
\cup
D_{\mathsf A}
\cup
D_{\mathsf H}^{\mathrm{sym}}.
}
$$

所以 C-IRPT 的四重缺陷向量和本规范的单一信息逃逸对象并不冲突：

- 向量保留缺陷来自哪一个角色；
- 总 residual 给出不重复计数的统一逃逸集合；
- 二者由精确分解定理连接。

---

## CIRPT-15　无权重四角色逃逸率

若：

$$
2\le|X|<\infty,
$$

定义统一分母：

$$
N_X=|X|(|X|-1).
$$

定义：

$$
\boxed{
\varepsilon_{\mathrm{CIRPT}}(\Sigma)
=
\frac{|D_{\mathrm{CIRPT}}(\Sigma)|}{N_X}.
}
$$

分母对所有角色、所有 theorem 和所有 primitive bundle 完全相同。

不允许：

- 给 CUT、FLOW、ADMIT、ANCHOR 分配人为权重；
- 通过修改角色权重改变准入；
- 将重叠 defect 重复相加；
- 通过缩小 ADMIT 域改变分母；
- 用浮点近似替代精确 `Nat`／`Rat`。

该率具有概率解释：从 $X$ 中均匀抽取一个有序非对角状态对，它落入至少一个 C-IRPT 角色缺陷的概率。

---

## CIRPT-16　四位 defect signature 与精确交互分解

令角色轴类型：

$$
R=\{\mathsf C,\mathsf F,\mathsf A,\mathsf H\}.
$$

对每个有序非对角 pair $p=(x,y)$，定义 defect signature：

$$
\sigma_\Sigma(p):R\to\mathrm{Bool},
$$

其中：

$$
\sigma_\Sigma(p)(r)=1
\iff
p\in D_r.
$$

在有限模型上定义 exact histogram：

$$
H_\Sigma(s)
=
\left|
\{p\in X^2\setminus\Delta_X:\sigma_\Sigma(p)=s\}
\right|,
\qquad
s\in\mathrm{Bool}^4.
$$

### 定理 CIRPT-IE-011　Signature partition

十六个 signature classes 两两不交并覆盖全部有序非对角 pair：

$$
\sum_{s\in\mathrm{Bool}^4}H_\Sigma(s)
=N_X.
$$

统一逃逸计数为：

$$
\boxed{
|D_{\mathrm{CIRPT}}|
=
\sum_{s\ne 0000}H_\Sigma(s).
}
$$

每一角色的 defect count 为：

$$
|D_r|
=
\sum_{s:s(r)=1}H_\Sigma(s).
$$

而多角色重叠由相应多位为 $1$ 的 signature 直接给出。

因此无需人为交互权重，数学 signature 分解仍能区分：

- 单一角色缺陷；
- 两角色共同缺陷；
- 三角色共同缺陷；
- 四角色共同缺陷；
- 无缺陷 pair。

---

## CIRPT-17　后处理单调性统一 CUT 与 FLOW 翻译损失

若：

$$
g=h\circ f,
$$

则：

$$
\ker f\subseteq\ker g.
$$

### 定理 CIRPT-IE-012　Kernel data processing

对任意当前 kernel $K$：

$$
\boxed{
\operatorname{Residual}(K,\ker g)
\subseteq
\operatorname{Residual}(K,\ker f).
}
$$

含义是：粗化目标只能减少目标要求的区别；而若把 $f$ 当作现有观察并后处理成 $g$，则其绝对逃逸只能增加。

该定理统一覆盖：

- CUT 粗化；
- FLOW 输出压缩；
- 语言翻译；
- 决策接口压缩；
- 目标 readout 后处理。

---

## CIRPT-18　FLOW 动态 trace 仍然是 CUT

给定动作族：

$$
F:U\to X\to X
$$

和当前 CUT：

$$
q:X\to B,
$$

定义长度不超过 $n$ 的行为 CUT：

$$
\operatorname{Behavior}_n(F,q)(x)
=
\left(w\mapsto q(F_wx)\right)_{|w|\le n}.
$$

定义完全行为 CUT：

$$
\operatorname{Behavior}_\infty(F,q)(x)
=
\left(w\mapsto q(F_wx)\right)_{w\in U^*}.
$$

### 定理 CIRPT-IE-013　Dynamic CUT lift

每个行为 trace 都是普通 CUT，且：

$$
\ker\operatorname{Behavior}_{n+1}
\subseteq
\ker\operatorname{Behavior}_n
\subseteq
\ker q.
$$

定义动态逃逸：

$$
\boxed{
D_{\mathrm{dyn},n}(F,q)
=
\operatorname{Residual}
\left(
\ker q,
\ker\operatorname{Behavior}_n(F,q)
\right).
}
$$

它正好测量：当前同一 CUT fiber 中，哪些状态会在 $n$ 步内产生可见分叉。

完全动态逃逸：

$$
D_{\mathrm{dyn},\infty}(F,q)
=
\ker q
\setminus
\ker\operatorname{controlledBehavior}(F,q).
$$

这就是 C-IRPT 的记忆需求集合。

### 定理 CIRPT-IE-014　Finite dynamic stabilization

若 $X$ 与动作字母表有限，则上述 kernel refinement 迭代在有限步稳定。每次非固定更新都严格增加等价类数量，因此严格变化次数不超过：

$$
|X|-\left|X/\ker q\right|.
$$

这使动态信息逃逸也能在一次 Lean 编译中精确闭合，而不需要无限运行时过程。

---

## CIRPT-19　ADMIT 不作为状态删除器

统一硬门始终在完整 `Arena.State` 上计算：

$$
X^2\setminus\Delta_X.
$$

ADMIT 通过：

$$
\kappa_{\mathsf A}(A)
$$

进入联合 kernel，而不是通过：

$$
X\rightsquigarrow\{x\mid A(x)\}
$$

缩小计算域。

### 规范 CIRPT-R-001　No domain immunization

严禁用以下方式降低硬门逃逸率：

```text
先删除 residual witness
→ 再在剩余 admitted subtype 上计算
→ 宣称信息逃逸下降
```

若 theorem 的数学内容改变 ADMIT，系统应把新旧 ADMIT 作为两个 predicate primitives 比较；不得静默改变 arena 分母。

该规则直接吸收 C-IRPT 的 domain-immunization 审计结论。

---

## CIRPT-20　object ANCHOR 与 proof ANCHOR 的层级分离

C-IRPT 正确指出：一个 proof term 是 claim type 中的 ANCHOR。

但是，同层 theorem 信息计算不得把原 theorem 的 proof identity 自动加入其 object-level primitive bundle。否则每个 theorem 都可通过“我的 proof term 与其他 proof term 不同”获得伪造的唯一信息。

因此必须区分：

$$
\boxed{
\text{object anchor}
\ne
\text{certificate anchor}.
}
$$

- object anchor 是 theorem 所讨论数学状态空间 $X$ 中的实际点；
- certificate anchor 是 `Statement` 类型中的 proof term；
- certificate anchor 证明 primitive semantics 有效；
- certificate anchor 不参与同层 $X$ 上的 kernel 计算。

### 规范 CIRPT-R-002　No certificate leakage

`TheoremUnit.proof`、伴随 theorem proof、seal proof 和 declaration identity 均不得成为同一 arena 的 primitive coordinate。

若研究对象本身就是 proof theory，则应建立一个独立 meta-arena，把 proof objects 显式作为该 arena 的状态。只有在那个更高层 arena 中，proof ANCHOR 才可成为 object-level primitive。

---

## CIRPT-21　定理 primitive normal form

对每个 theorem unit $i$，不再把：

$$
c_i:X\to O_i
$$

视为任意手工指定 readout。

它必须由 theorem 的有限 primitive bundle：

$$
\Pi_i
$$

规范产生。

定义 theorem kernel：

$$
\boxed{
K_i
=
K_{\Pi_i}
=
\bigcap_{p\in\Pi_i}\kappa_p.
}
$$

任取一个 kernel-realizing CUT：

$$
c_i:X\to O_i,
\qquad
\ker c_i=K_i,
$$

即可作为本文第一部公式中的 $c_i$。

因此旧记号：

$$
\tau_i=(P_i,p_i,c_i)
$$

在 C-IRPT 正规形下展开为：

$$
\boxed{
\tau_i=(P_i,p_i,\Pi_i,K_i,c_i),
\qquad
K_i=\bigcap_{p\in\Pi_i}\kappa_p,
\quad
\ker c_i=K_i.
}
$$

其中真正规范性的语义对象是 $\Pi_i$ 与 $K_i$；$c_i$ 只是兼容现有 `Concept` API 的一个实现。

---

## CIRPT-22　theorem statement 与 primitive bundle 的绑定

primitive bundle 不是评价者添加的标签。它必须由 theorem statement 本身的标准形式产生，或由一个 kernel-checked realization theorem 连接。

原生形式：

```lean
structure PrimitiveLawArena extends Arena where
  Law : PrimitiveBundle toArena → Prop

structure NativePrimitiveTheoremUnit
    (arena : PrimitiveLawArena) where
  primitives : PrimitiveBundle arena.toArena
  proof : arena.Law primitives
```

legacy 形式：

```lean
structure LegacyPrimitiveRealization
    (arena : PrimitiveLawArena)
    (statement : Prop)
    (primitives : PrimitiveBundle arena.toArena) where
  equivalence : statement ↔ arena.Law primitives
```

禁止只有字符串式关联：

```text
this theorem is about FLOW
this theorem has high anchor value
```

必须存在 Lean 类型中的 statement-to-primitives 证明。

### CIRPT-22.1　闭定理真值塌缩

这里必须排除一个看似自然、实则把全部已证明定理压成同一坐标的错误做法。

对闭命题：

$$
P:\mathsf{Prop},
\qquad
p:P,
$$

若只把“$P$ 已被证明”为状态读出：

$$
\chi_{P,p}:X\to\mathrm{Bool},
\qquad
\chi_{P,p}(x)=\mathsf{true},
$$

则：

$$
\ker(\chi_{P,p})=X\times X.
$$

它不能切开任何状态 pair，因此对任何 catalog 都有零独有捕获。

### 定理 CIRPT-IE-021　Closed-truth universal-kernel theorem

对任意非空状态类型 $X$、任意闭命题 $P$ 与证明 $p:P$：

$$
\boxed{
\ker(\lambda x:X,\mathsf{true})=X\times X.
}
$$

从而把 theorem 仅编码为“真／假”不能产生对象层信息增益。

这说明：

$$
\boxed{
\text{theorem 的 proof ANCHOR 证明其真，theorem 的 object primitives 表达其区分内容。}
}
$$

“全部概念都可由 C-IRPT primitive 表示”的准确含义是：

- theorem 中出现的分类接口可归为 CUT；
- theorem 中出现的作用、变换与演化可归为 FLOW；
- theorem 中出现的适用条件与合法性可归为 ADMIT；
- theorem 中出现的具体构造、反例、状态或实现见证可归为 object ANCHOR；
- 这些对象角色经 kernel normalization 后进入统一计算。

它不意味着一个已经闭合的 `Prop` 的常值真值本身具有区分能力。

因此 `PrimitiveLawArena` 不是外加评价体系，而是 theorem 的对象语义被显式类型化后的载体。若没有 object-level primitive 或 realization theorem，该 declaration 只能作为 proof/certificate ANCHOR，不能伪装成一个正信息 theorem unit。

---

## CIRPT-23　完整 theorem catalog 的 primitive kernel

设当前 sealing root 为 $R$，canonical object arena 为 $A$，其唯一 maximal catalog
$C_{R,A}$ 的 occurrence index 为 $I_{R,A}$，每个 occurrence 有 kernel $K^R_{A,i}$。
本节以下省略的 $R,A$ 仅是排版简写，绝不表示跨 arena 的一个 catalog。

完整 catalog kernel：

$$
\boxed{
K^R_{A,I_{R,A}}
=
\bigcap_{i:I_{R,A}}K^R_{A,i}.
}
$$

留一 kernel：

$$
K^{R,-i}_A
=
\bigcap_{j\in I_{R,A},\ j\ne i}K^R_{A,j}.
$$

原 SPEC 的绝对 escape 为：

$$
E^R_A
=K^R_{A,I_{R,A}}\setminus\Delta_A.
$$

同一个 occurrence（`(canonical arena declaration, theoremName)`）可以出现在多个 root import
closures 或 analysis views 中而不改变其 identity；其 $K_{-i},U_i,\delta_i$ 必须针对它出现于其中的
每个 $C_{R,A}$ 重新计算。只有通过另一个具名、kernel-checked realization 登记到不同 canonical
arena 上，才产生新的 occurrence。

---

## CIRPT-24　留一增益本身就是统一 residual

固定 $(R,A,C_{R,A})$ 后，occurrence $i$ 的独有捕获集合：

$$
U_i
=K_{-i}\setminus K_I.
$$

由于：

$$
K_I=K_{-i}\cap K_i,
$$

得到：

### 定理 CIRPT-IE-015　Leave-one-out residual identity

$$
\boxed{
U_i
=
K_{-i}\setminus K_i
=
\operatorname{Residual}(K_{-i},K_i).
}
$$

这给出最精确的统一解释：

> 删除 theorem $i$ 后，其他 theorem 形成当前 CUT；theorem $i$ 的 primitive bundle 形成目标 CUT；其独有信息就是其他 theorem 无法向该目标下降的 residual。

因此当前规范没有人为 target。这里的 target $K_i$ 是 theorem occurrence 自身的
primitive kernel，由当前 maximal catalog 内生给出。

进一步：

$$
U_i\ne\varnothing
$$

等价于：

$$
K_{-i}\not\subseteq K_i,
$$

等价于 theorem $i$ 的 primitive bundle 不属于其他 theorem 的语义闭包。

### CIRPT-24.1　平坦累计 catalog 的粗成员归零

### 定理 CIRPT-IE-024　`nested_flat_catalog_coarse_member_zero`

若同一 flat catalog 中 $i\neq j$ 且：

$$
K_j\subseteq K_i,
$$

则 $K_{-i}\subseteq K_j\subseteq K_i$，故：

$$
\boxed{U_i=K_{-i}\setminus K_i=\varnothing.}
$$

所以 cumulative readouts 的严格层级不蕴含每个成员都有正 leave-one-out capture。
若 $K_{cf}\subsetneq K_{int}\subsetneq K_{obs}$ 同时作为任意 flat catalog 的 members，则
$U_{obs}=U_{int}=\varnothing$，而 finest member 的一般式是：

$$
U_{cf}=\bigl(D_A\cap(K_{int}\setminus K_{cf})\bigr)
\setminus
\bigcup_{k\in I_{R,A}\setminus\{obs,int,cf\}}\operatorname{Cap}^R_{A,k}.
$$

只有 flat catalog 恰由这三个 members 构成时，才有
$U_{cf}=D_A\cap(K_{int}\setminus K_{cf})$。

对应的 order-free Lean signatures 不要求 `Catalog.Index` 上有次序：

```lean
theorem nested_flat_catalog_coarse_member_zero
    (catalog : Catalog arena) {coarse finer : catalog.Index}
    (distinct : finer ≠ coarse)
    (refines : catalog.KernelRefines finer coarse) :
    catalog.uniqueCaptureCount coarse = 0 := by
  ...

theorem nested_flat_catalog_finest_unique_capture_iff
    (catalog : Catalog arena) (obs int cf : catalog.Index)
    (obs_ne_int : obs ≠ int) (obs_ne_cf : obs ≠ cf) (int_ne_cf : int ≠ cf)
    (cf_refines_int : catalog.KernelRefines cf int)
    (int_refines_obs : catalog.KernelRefines int obs)
    (x y : arena.State) :
    (x ≠ y ∧
      (∀ k, k ≠ cf → (catalog.theoremAt k).primitives.agrees x y) ∧
      ¬(catalog.theoremAt cf).primitives.agrees x y) ↔
    (x ≠ y ∧
      (catalog.theoremAt int).primitives.agrees x y ∧
      ¬(catalog.theoremAt cf).primitives.agrees x y ∧
      ∀ k, k ≠ obs → k ≠ int → k ≠ cf →
        (catalog.theoremAt k).primitives.agrees x y) := by
  ...

theorem nested_flat_exactly_three_finest_unique_capture_iff
    (catalog : Catalog arena) (obs int cf : catalog.Index)
    (obs_ne_int : obs ≠ int) (obs_ne_cf : obs ≠ cf) (int_ne_cf : int ≠ cf)
    (covers : ∀ k : catalog.Index, k = obs ∨ k = int ∨ k = cf)
    (cf_refines_int : catalog.KernelRefines cf int)
    (int_refines_obs : catalog.KernelRefines int obs)
    (x y : arena.State) :
    (x ≠ y ∧
      (∀ k, k ≠ cf → (catalog.theoremAt k).primitives.agrees x y) ∧
      ¬(catalog.theoremAt cf).primitives.agrees x y) ↔
    (x ≠ y ∧
      (catalog.theoremAt int).primitives.agrees x y ∧
      ¬(catalog.theoremAt cf).primitives.agrees x y) := by
  ...
```

这与 T-005 中 product member 被其坐标 peers 捕获是同一个数学现象；T-005/T-006
的既有期望保持不变。

### CIRPT-24.2　certified chain 的相邻增量

对携带 $K_\ell\subseteq\cdots\subseteq K_0$ inclusion proofs 的 `LayerChain`，定义：

$$
L_0=D_A\setminus K_0,
\qquad
L_r=D_A\cap(K_{r-1}\setminus K_r)\ (r>0),
\qquad
R_\ell=D_A\cap K_\ell.
$$

### 定理 CIRPT-IE-025　`kernelChain_increment_partition_and_telescope`

$L_0,\ldots,L_\ell,R_\ell$ 两两不交，且：

$$
D_A=L_0\;\dot\cup\cdots\dot\cup\;L_\ell\;\dot\cup\;R_\ell.
$$

因此 $L_0,\ldots,L_\ell$ 分割 $D_A\setminus K_\ell$，并有相邻 telescoping count
identity。layered count/rate 是 chain analysis，不是 theorem unit，也不生成第三个
theorem registration。

### CIRPT-24.3　严格 refinement 的精确判据

### 定理 CIRPT-IE-026　`kernelChain_increment_nonempty_iff_strict`

初层的完整判据是：

$$
L_0\neq\varnothing
\Longleftrightarrow D_A\nsubseteq K_0
\Longleftrightarrow \exists x\ne y,\ \neg K_0(x,y).
$$

对 $r>0$：

$$
L_r\neq\varnothing
\Longleftrightarrow
K_r\subsetneq K_{r-1}.
$$

chain inclusion、partition 与 strictness 必须由 Lean theorem 证明；具体有限 count 与
exact rational rate 可由同一 kernel 的 reflected equality 认证。缺少 proof 的有序
kernel 列表不是 `LayerChain`。

### CIRPT-24.4　primitive generators 的闭包 DAG

令 theorem occurrence $i$ 的 bundle kernel 为：

$$
K_i=\bigcap_{p\in\Pi_i}\kappa_p.
$$

则任意 generated node 都是 primitive kernels 的有限交：

$$
K_S
=\bigcap_{i\in S}K_i
=\bigcap_{i\in S}\ \bigcap_{p\in\Pi_i}\kappa_p.
$$

从 node $P=[S]$ 加入 theorem $i$ 的 primitive bundle，只执行同一个 C-IRPT 运算：

$$
K_Q=K_P\cap K_i.
$$

若 $K_Q\subsetneq K_P$，edge payload 正是：

$$
\operatorname{edgeCapture}(P,Q)
=K_P\setminus K_Q
=K_P\setminus K_i
=\operatorname{Residual}(K_P,K_i).
$$

equivalence kernels 的对角线不会进入该差集，所以 finite engine 与
$D_A\cap(K_P\setminus K_Q)$ 完全相同。若 residual 为空，加入动作是
`collapsed_addition`，不产生 edge。CUT、FLOW、ADMIT、ANCHOR 在这里没有权重或优先级；
它们只经 $\Pi_i$ 共同决定 $K_i$。

任一 decomposition 是从 $K_\varnothing$ 到 $K_I$ 的 generator path。path 上 increments 的
不交并与总 residual 相等，而 terminal kernel 只由最终 generator set 决定。因此多个 primitive
分解顺序可以共存，不能把某条 greedy／Shapley／名称顺序路径升级为 canonical 数学对象；这类
次序至多是 `report-only` layout。

---

## CIRPT-25　primitive representation invariance

一个 theorem 可能存在多个 C-IRPT 分解：

$$
\Pi_i,
\qquad
\Pi_i'.
$$

只要：

$$
K_{\Pi_i}=K_{\Pi_i'},
$$

则：

### 定理 CIRPT-IE-016　Bundle-kernel invariance

对任意同一 catalog 的其他 theorem：

$$
U_i(\Pi_i)=U_i(\Pi_i'),
$$

$$
\delta_i(\Pi_i)=\delta_i(\Pi_i'),
$$

并且全 catalog escape 不变。

因此：

- 把一个 CUT 写成两个可恢复坐标；
- 把 FLOW 写成等价 trace；
- 把 ADMIT 从 Prop Boolean 化；
- 把 ANCHOR 写成 pointed predicate；
- 更换 quotient 代表；

只要 joint kernel 不变，都无法改变数学判词。

这消除了“修改原语表示来修改评价结果”的空间。

### CIRPT-25.1　arena 等价输运不变性

primitive representation invariance 还必须覆盖状态载体的等价重编码。

设：

$$
e:X\simeq Y.
$$

对 $X$ 上的 kernel $K$，定义输运 kernel：

$$
(e_*K)(y_1,y_2)
\iff
K(e^{-1}y_1,e^{-1}y_2).
$$

等价 $e$ 诱导非对角有序 pair 的双射：

$$
e^{(2)}:
X^2\setminus\Delta_X
\simeq
Y^2\setminus\Delta_Y,
\qquad
(x_1,x_2)\mapsto(e x_1,e x_2).
$$

### 定理 CIRPT-IE-022　Arena-equivalence invariance

若完整 catalog 的全部 primitive kernels 沿 $e$ 输运，则对每个 theorem $i$：

$$
|E_I^X|=|E_I^Y|,
$$

$$
|U_i^X|=|U_i^Y|,
$$

$$
\varepsilon_X(I)=\varepsilon_Y(I),
$$

$$
\delta_i^X=\delta_i^Y.
$$

因此：

- 状态重命名；
- 构造上不同但等价的有限类型；
- 坐标排列；
- 经 Lean `Equiv` 证明的编码变换；

均不能改变判词。

### CIRPT-25.2　非等价 arena 不得被强行聚合

若 $X\to Y$ 不是等价，而是复制、删除或合并状态，则均匀非对角 pair 的基数和多重度可能改变。此时逃逸率变化不是“修改评分器”，而是更换了被计算的数学状态空间。

因此规范必须区分：

$$
\boxed{
\text{统一计算公式}
\neq
\text{把不同状态空间强压成一个无类型总分。}
}
$$

一次编译可以同时封印多个 arena，但输出是依赖索引族：

$$
\{\varepsilon_A,\delta_{A,i}\}_{A:\mathrm{Arena}},
$$

不是跨 arena 的加权和。

系统只允许两种跨表示关系：

1. arena definitionally 相同；
2. 有 Lean `Equiv`，并由 CIRPT-IE-022 输运。

对于不等价 arena，不存在本规范内生给出的比较或聚合标量。引入这种标量必然需要额外测度或权重，因而属于另一个数学问题，不能进入本硬门。

### 定理 CIRPT-IE-023　Uniform residual valuation uniqueness

固定有限 arena $X$，令：

$$
D_X=X^2\setminus\Delta_X.
$$

设：

$$
V:\mathcal P(D_X)\to\mathbb Q
$$

满足：

1. $V(\varnothing)=0$；
2. $V(D_X)=1$；
3. 对不交集合有限可加；
4. 对 $D_X$ 的任意置换不变。

则对每个 $R\subseteq D_X$：

$$
\boxed{
V(R)=\frac{|R|}{|D_X|}.
}
$$

所以在固定 arena 中，一旦 C-IRPT primitives 已归约出 residual set，本规范使用的逃逸率不是可调评价函数，而是满足无差别对称性的唯一归一化有限可加 valuation。

---

## CIRPT-26　theorem 内部角色 signature

对 theorem $i$ 的 unique pair：

$$
p\in U_i,
$$

定义 theorem-role signature：

$$
\rho_i(p):R\to\mathrm{Bool},
$$

其中：

$$
\rho_i(p)(r)=1
$$

当且仅当 theorem $i$ 的 primitive bundle 中至少有一个角色为 $r$ 的 primitive 切开 $p$。

### 定理 CIRPT-IE-017　Unique-capture role coverage

$$
\boxed{
p\in U_i
\Rightarrow
\rho_i(p)\ne 0000.
}
$$

并且：

$$
U_i
=
\bigcup_{r\in R}
\{p\in U_i:\rho_i(p)(r)=1\}.
$$

数学角色分解可以精确区分 theorem 的 unique information 来自：

- CUT；
- FLOW；
- ADMIT；
- ANCHOR；
- 或它们的重叠。

但最终硬门仍只有：

$$
|U_i|>0.
$$

角色分解只解释数学来源，不参与加权。

对同一个 $(R,A)$，定义 role-histogram matrix：

$$
H^R_{A,i}(s)=
|\{p\in U^R_{A,i}\mid\rho_i(p)=s\}|,
\qquad s\in\{0,1\}^4\setminus\{0000\},
$$

以及 catalog column total：

$$
H^R_A(s)=\sum_iH^R_{A,i}(s).
$$

`RoleProfileEq(i,j)` 当且仅当每个 signature column 都相等；pairwise difference 是
$H_i(s)-H_j(s)$ 的 exact integer vector，不压成 score。由
`roleHistogram_sum_eq_uniqueCaptureCount` 逐行求和：

$$
\sum_sH^R_A(s)=\sum_i|U^R_{A,i}|=h^R_A(1).
$$

该比较依赖登记的 primitive axes。只有 atom reindex、role-preserving kernel
replacement 或 role-preserving arena transport 保持它；任意同 kernel bundle 替换并
不保证 role histogram 不变。catalog totals 与 unweighted deltas 均只在同 arena 报告。

---

## CIRPT-27　统一信息逃逸计算能力

由前述定理得到一条完整归约链：

$$
\boxed{
\begin{aligned}
\text{C-IRPT primitive}\
&\longrightarrow
\text{equivalence kernel}\
&\text{CIRPT-IE-001}\\
&\longrightarrow
\text{canonical CUT normal form}\
&\text{CIRPT-IE-002}\\
&\longrightarrow
\text{finite bundle joint kernel}\
&\text{CIRPT-IE-003}\\
&\longrightarrow
\text{unified residual}\
&\text{CIRPT-IE-005}\\
&\longrightarrow
\text{exact pair count / rate}\
&\text{finite layer}\\
&\longrightarrow
\text{leave-one-out theorem gain}\
&\text{CIRPT-IE-015}.
\end{aligned}
}
$$

所以系统只需实现一个底层函数：

```text
Residual(Kcurrent, Ktarget)
```

以及一个有限族操作：

```text
JointKernel(family)
```

其他全部能力都是特化：

```text
CUT defect
FLOW carry
ADMIT mixed fiber
ANCHOR shadow
multi-target completion
dynamic memory need
theorem leave-one-out gain
four-role total defect
semantic closure
```

---

## CIRPT-28　统一性不等于唯一 primitive 分解

本规范主张：

$$
\boxed{
\text{统一的是 kernel 演算，不是每个 theorem 的唯一语法分解。}
}
$$

不同 primitive bundle 可能具有同一个 joint kernel。此时它们是信息等价表示。

反之，若两个 bundle 产生不同 kernel，则它们确实规定不同的状态同一性，因而是不同数学语义，而不是同一评价体系下的任意改分。

系统不需要选择“哲学上唯一正确”的 primitive 语法；它只要求：

1. theorem 与 bundle 的关系由 Lean 证明；
2. bundle kernel 可计算或可结构证明；
3. 同核表示具有相同判词；
4. 不同核表示被视为不同数学陈述。

---

## CIRPT-29　“平凡”的精确定义保持不变

引入 primitive normal form 后，平凡仍定义为：

$$
\boxed{
\delta_i=0
\iff
U_i=\varnothing
\iff
K_{-i}\subseteq K_i.
}
$$

这表示 theorem $i$ 的全部 CUT/FLOW/ADMIT/ANCHOR 区分能力已被其他 theorem 联合覆盖。

本规范中的“平凡”不等于：

- proof term 很短；
- theorem 在人类教材中初等；
- statement 字符数少；
- 证明使用 `simp`；
- theorem 没有文献新颖性。

一个非常简单但真正切开独有 primitive pair 的 theorem，其 $\delta_i$ 可以为正；它在本系统中不是语义冗余。

一个极长但完全处于其他 theorem 语义闭包中的形式化，其 $\delta_i=0$。
SealRow 可携带其平凡性与闭包归属证明，完整合法目录可携带冗余结论。

---

## CIRPT-30　系统自身的 primitive 表示

C-IRPT 将反射定义为 Stage 类型上的 FLOW。因此该信息系统自身仍可按相同方式处理。

在 meta-arena：

$$
X_{\mathrm{meta}}=\mathrm{Stage}
$$

上，可定义：

- Meta-CUT：stage 的 theorem/kernel catalog；
- Meta-FLOW：elaborate、normalize、seal；
- Meta-ADMIT：kernel-checked compilation acceptance；
- Meta-ANCHOR：当前已 elaborated environment。

随后使用完全相同的：

$$
\operatorname{JointKernel},
\qquad
\operatorname{Residual},
\qquad
\varepsilon,
\qquad
\delta_i.
$$

一次编译内不需要历史 baseline。meta-arena 仍然只是当前 environment 中另一个有限 arena。

---

## CIRPT-31　纯数学非主张

本部不声称：

1. 四角色在完整模型语义上彼此相同；
2. 任意 Lean theorem 的语义可在没有 interpretation proof 的情况下自动从 AST 唯一恢复；
3. primitive 数量越多，数学价值越大；
4. object proof term identity 是 object-level 信息；
5. ADMIT 可以通过删除状态来提高得分；
6. 四角色 defect count 可以无重叠地直接相加；
7. 正 escape gain 等于人类意义上的研究重要性、证明难度或文献新颖性；
8. 动态、测度或无限状态问题总能归约为有限可执行十进制数；
9. 一个闭 theorem 的常值真值可以充当对象层 primitive；
10. 不同且非等价的数学 arena 具有一个无需额外结构的全局可加总分。

本部严格主张的是：

$$
\boxed{
\text{一旦 theorem 的数学语义已由 C-IRPT primitives 在 Lean 中给出，}
}
$$

则：

$$
\boxed{
\text{其全部信息逃逸计算可统一归约为 joint kernel、kernel residual 与精确计数。}
}
$$

---

## CIRPT-32　新增纯数学定理清单

实现时至少应闭合以下 theorem：

```text
CIRPT-IE-001 primitive_kernel_equivalence
CIRPT-IE-002 quotient_cut_kernel_normal_form
CIRPT-IE-003 primitive_bundle_joint_kernel
CIRPT-IE-004 primitive_expression_kernel_normalization
CIRPT-IE-005 residual_extensional
CIRPT-IE-006 residual_joint_target_eq_iUnion
CIRPT-IE-007 anchor_residual_eq_oriented_shadow_union
CIRPT-IE-008 admit_boundary_nonempty_iff_residual_nonempty
CIRPT-IE-009 flow_carry_nonempty_iff_residual_nonempty
CIRPT-IE-010 four_role_residual_eq_union
CIRPT-IE-011 four_role_signature_partition
CIRPT-IE-012 postprocessing_residual_mono
CIRPT-IE-013 behavior_cut_kernel_antitone
CIRPT-IE-014 finite_behavior_kernel_stabilizes
CIRPT-IE-015 leave_one_out_eq_primitive_residual
CIRPT-IE-016 primitive_bundle_kernel_invariance
CIRPT-IE-017 unique_capture_has_nonempty_role_signature
CIRPT-IE-018 theorem_gain_depends_only_on_primitive_kernel
CIRPT-IE-019 certificate_anchor_erasure
CIRPT-IE-020 full_domain_admit_encoding
CIRPT-IE-021 closed_truth_readout_has_universal_kernel
CIRPT-IE-022 arena_equiv_preserves_escape_and_gain
CIRPT-IE-023 uniform_residual_valuation_unique
CIRPT-IE-024 nested_flat_catalog_coarse_member_zero
CIRPT-IE-025 kernelChain_increment_partition_and_telescope
CIRPT-IE-026 kernelChain_increment_nonempty_iff_strict
```

---

## CIRPT-33　Lean 4 primitive kernel API

以下为规范级接口草案。

```lean
universe u v w

namespace D5.S3.ConceptDynamics.CIRPT.InformationEscape

inductive PrimitiveAxis
  | cut
  | flow
  | admit
  | anchor
  deriving DecidableEq, Repr

structure DecidableKernel (X : Type u) where
  relation : X → X → Prop
  equivalence : Equivalence relation
  decidableRelation : DecidableRel relation

namespace DecidableKernel

instance (kernel : DecidableKernel X) :
    DecidableRel kernel.relation :=
  kernel.decidableRelation

end DecidableKernel
```

`DecidableKernel` 是有限编译引擎的首要接口。

它不是新的数学原语，而是：

```text
Setoid X + executable decision procedure
```

---

## CIRPT-34　四 primitive constructor

```lean
def cutKernel
    {X B : Type*} [DecidableEq B]
    (q : X → B) : DecidableKernel X :=
  ...

def flowKernel
    {X Y : Type*} [DecidableEq Y]
    (flow : X → Y) : DecidableKernel X :=
  cutKernel flow

def admitKernel
    {X : Type*}
    (admit : X → Prop)
    [DecidablePred admit] : DecidableKernel X :=
  ...

def anchorKernel
    {X : Type*} [DecidableEq X]
    (anchor : X) : DecidableKernel X :=
  ...
```

必须证明 reflection theorem：

```lean
cutKernel_relation_iff
flowKernel_relation_iff
admitKernel_relation_iff
anchorKernel_relation_iff
```

---

## CIRPT-35　PrimitiveAtom 与 PrimitiveBundle

```lean
structure PrimitiveAtom (arena : Arena) where
  axis : PrimitiveAxis
  kernel : DecidableKernel arena.State

structure PrimitiveBundle (arena : Arena) where
  Index : Type v
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  atom : Index → PrimitiveAtom arena
```

定义：

```lean
def PrimitiveBundle.agrees
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Prop :=
  ∀ index, (bundle.atom index).kernel.relation left right

def PrimitiveBundle.agreesB
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Bool := by
  letI := bundle.indexFintype
  letI := bundle.indexDecidableEq
  exact Finset.fold (fun left right => left && right) true
    (fun index =>
      decide ((bundle.atom index).kernel.relation left right)) Finset.univ
```

必须证明：

```lean
theorem agreesB_eq_true_iff :
  bundle.agreesB left right = true ↔
    bundle.agrees left right
```

反射证明必须使用 pin 中存在的 `Finset.fold_op_rel_iff_and`（或同强度、在 pin 中存在的引理）。

以及：

```lean
theorem agrees_equivalence :
  Equivalence bundle.agrees
```

---

## CIRPT-36　TheoremUnit 的规范修订

核心类型修订为：

```lean
structure TheoremUnit (arena : Arena) where
  primitives : PrimitiveBundle arena
  Statement : Prop
  proof : Statement
```

不再把自由构造的 `PackedObserver` 作为真源。

---

## CIRPT-37　Catalog 计算只消费 theorem kernel

```lean
def Catalog.indistinguishable
    (catalog : Catalog arena)
    (selected : Finset catalog.Index)
    (left right : arena.State) : Prop :=
  ∀ index, index ∈ selected →
    (catalog.theoremAt index).primitives.agrees left right
```

可执行版本：

```lean
def Catalog.indistinguishableB ... : Bool :=
  selected.toList.all fun index =>
    (catalog.theoremAt index).primitives.agreesB left right
```

独有捕获：

```lean
def Catalog.uniqueCapturePairs
    (catalog : Catalog arena)
    (index : catalog.Index) :
    Finset (arena.State × arena.State) :=
  (escapePairs catalog (without catalog index)).filter fun pair =>
    (catalog.theoremAt index).primitives.agreesB
      pair.1 pair.2 = false
```

这正是：

$$
\operatorname{Residual}(K_{-i},K_i).
$$

---

## CIRPT-38　角色 signature API

```lean
def axisOrdinal : PrimitiveAxis → Fin 4

def PrimitiveBundle.separatesOnAxis
    (bundle : PrimitiveBundle arena)
    (axis : PrimitiveAxis)
    (left right : arena.State) : Bool := by
  letI := bundle.indexFintype
  letI := bundle.indexDecidableEq
  exact Finset.fold (fun left right => left || right) false
    (fun index =>
      decide ((bundle.atom index).axis = axis) &&
        decide (¬(bundle.atom index).kernel.relation left right)) Finset.univ

theorem PrimitiveBundle.separatesOnAxis_eq_true_iff :
  bundle.separatesOnAxis axis left right = true ↔
    ∃ index,
      (bundle.atom index).axis = axis ∧
        ¬(bundle.atom index).kernel.relation left right

def PrimitiveBundle.roleSignature
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Fin 4 → Bool :=
  fun coordinate =>
    bundle.separatesOnAxis (axisOfOrdinal coordinate) left right
```

`separatesOnAxis_eq_true_iff` 的反射证明必须使用 pin 中已存在的
`Finset.fold_op_rel_iff_or`（或同强度、在 pin 中存在的引理）。

必须证明：

```lean
theorem uniqueCapture_roleSignature_nonzero :
  pair ∈ uniqueCapturePairs catalog index →
    (catalog.theoremAt index).primitives.roleSignature
      pair.1 pair.2 ≠ fun _ => false
```

### CIRPT-38.1　共享 catalog 与 layered analysis API

以下是 v4.2 新 API 的规范级 Lean signature；实现可把计算拆到多个模块，但不得改变
这些对象的 typed ownership。

```lean
namespace Catalog

def capturePairs (catalog : Catalog arena) (index : catalog.Index) :
    Finset (arena.State × arena.State)

def exclusiveCaptureVector (catalog : Catalog arena) :
    catalog.Index → Nat :=
  fun index => catalog.uniqueCaptureCount index

def pairwiseCaptureOverlapPairs (catalog : Catalog arena)
    (left right : catalog.Index) :
    Finset (arena.State × arena.State)

def pairwiseCaptureOverlapCount (catalog : Catalog arena)
    (left right : catalog.Index) : Nat

def pairwiseCaptureOverlapRate (catalog : Catalog arena)
    (left right : catalog.Index) : Rat

def KernelRefines (catalog : Catalog arena)
    (finer coarser : catalog.Index) : Prop :=
  ∀ x y,
    (catalog.theoremAt finer).primitives.agrees x y →
      (catalog.theoremAt coarser).primitives.agrees x y

def KernelEquivalent (catalog : Catalog arena)
    (left right : catalog.Index) : Prop :=
  catalog.KernelRefines left right ∧ catalog.KernelRefines right left

instance (catalog : Catalog arena) (i j : catalog.Index) :
    Decidable (catalog.KernelRefines i j) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  unfold KernelRefines
  infer_instance

inductive KernelComparison
  | equal | strictlyFiner | strictlyCoarser | incomparable
  deriving DecidableEq, Repr

def kernelComparison (catalog : Catalog arena)
    (left right : catalog.Index) : KernelComparison

def refinementWitness? (catalog : Catalog arena)
    (finer coarser : catalog.Index) :
    Option (arena.State × arena.State)

def captureMultiplicity (catalog : Catalog arena)
    (pair : arena.State × arena.State) : Nat

def captureSpectrum (catalog : Catalog arena) :
    Fin (@Fintype.card catalog.Index catalog.indexFintype + 1) → Nat

def roleHistogramTotal (catalog : Catalog arena)
    (signature : Fin 4 → Bool) : Nat

def roleProfileEq (catalog : Catalog arena)
    (left right : catalog.Index) : Prop

def roleHistogramDifference (catalog : Catalog arena)
    (left right : catalog.Index) (signature : Fin 4 → Bool) : Int

def redundantIndices (catalog : Catalog arena) : Finset catalog.Index

def CatalogRedundant (catalog : Catalog arena) : Prop :=
  ∃ index, catalog.uniqueCaptureCount index = 0

end Catalog

structure LayerChain (arena : Arena) where
  length : Nat
  kernel : Fin (length + 1) → DecidableKernel arena.State
  refines : ∀ r : Fin length,
    (kernel r.succ).relation ≤ (kernel r.castSucc).relation

namespace LayerChain

def layeredCapturePairs (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) :
    Finset (arena.State × arena.State)

def layeredCaptureCount (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Nat

def layeredCaptureSpectrum (chain : LayerChain arena) :
    Fin (chain.length + 1) → Nat :=
  fun layer => chain.layeredCaptureCount layer

def layeredCaptureRate (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Rat

def unresolvedPairs (chain : LayerChain arena) :
    Finset (arena.State × arena.State)

def unresolvedCount (chain : LayerChain arena) : Nat

def unresolvedRate (chain : LayerChain arena) : Rat

theorem layeredCapture_zero_nonempty_iff (chain : LayerChain arena) :
    (chain.layeredCapturePairs ⟨0, Nat.zero_lt_succ _⟩).Nonempty ↔
      ∃ x y, x ≠ y ∧
        ¬(chain.kernel ⟨0, Nat.zero_lt_succ _⟩).relation x y := by
  ...

theorem layeredCapture_succ_nonempty_iff_strict
    (chain : LayerChain arena) (r : Fin chain.length) :
    (chain.layeredCapturePairs r.succ).Nonempty ↔
      ∃ x y,
        (chain.kernel r.castSucc).relation x y ∧
          ¬(chain.kernel r.succ).relation x y := by
  ...

end LayerChain
```

必须提供以下 reflection/certificate theorem；artifact 中的 Bool 或 numeral 不能替代它们：

```lean
Catalog.pairwiseCaptureOverlap_comm
Catalog.pairwiseCaptureOverlap_diag
Catalog.kernelRefines_preorder
Catalog.kernelRefines_implies_zero_uniqueCapture
Catalog.captureSpectrum_sum_eq_denominator
Catalog.captureSpectrum_zero_eq_fullEscape
Catalog.captureSpectrum_one_eq_sum_unique
Catalog.captureSpectrum_incidence_doubleCount
Catalog.pairwiseOverlap_spectrum_doubleCount
LayerChain.layeredCapture_zero_nonempty_iff
LayerChain.layeredCapture_succ_nonempty_iff_strict
Catalog.catalogRoleHistogram_sum
Catalog.catalogRedundant_iff_not_irredundant
LayerChain.layeredCapture_partition
LayerChain.strictRefinement_iff_layeredCapture_nonempty
```

### CIRPT-38.2　kernel lattice、structural 与 disposition API

以下 signatures 固定 typed ownership 与定理方向；实现可以调整 universe 参数和构造器细节，
但 `GeneratedKernel` 必须按 relation equality 取商，不能让 representative subset 成为 node
identity。

```lean
namespace Catalog

/-- Extensional quotient of subsets generating the same joint relation. -/
def GeneratedKernel (catalog : Catalog arena) :=
  Quotient (generatedKernelSetoid catalog)

def generatedKernel (catalog : Catalog arena)
    (selected : Finset catalog.Index) : catalog.GeneratedKernel

namespace GeneratedKernel

def relation (node : catalog.GeneratedKernel) :
    arena.State → arena.State → Prop

def relationB (node : catalog.GeneratedKernel)
    (left right : arena.State) : Bool

theorem relationB_eq_true_iff (node : catalog.GeneratedKernel)
    (left right : arena.State) :
    node.relationB left right = true ↔ node.relation left right

instance relationDecidable (node : catalog.GeneratedKernel) :
    DecidableRel node.relation := by
  intro left right
  exact decidable_of_iff (node.relationB left right = true)
    (node.relationB_eq_true_iff left right)

def KernelRefines (finer coarser : catalog.GeneratedKernel) : Prop :=
  finer.relation ≤ coarser.relation

def escapeAt (node : catalog.GeneratedKernel) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  letI : DecidableRel node.relation := node.relationDecidable
  exact (offDiagonalPairs arena).filter fun pair =>
    node.relation pair.1 pair.2

def edgeCapture (from to : catalog.GeneratedKernel) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact from.escapeAt \ to.escapeAt

end GeneratedKernel
end Catalog
```

`Catalog.GeneratorStep`、`Catalog.StrictGeneratorStep` 与 `Catalog.CollapsedAddition` 只采用
第 20.11 节的 canonical definitions：generator step 总是向下 refinement，strict 额外否定反向
refinement，collapsed 则认证双向 refinement／relation equality；本节不复制第二组定义。

```lean
/-- A full catalog ordering; equality steps are legal and classified. -/
inductive GeneratorStepClass (catalog : Catalog arena)
    (from to : catalog.GeneratedKernel) (added : catalog.Index) where
  | strict (proof : catalog.StrictGeneratorStep from to added)
  | collapsed
      (same : from = to)
      (proof : catalog.CollapsedAddition from added)

structure GeneratorSchedule (catalog : Catalog arena) where
  length : Nat
  added : Fin length → catalog.Index
  added_bijective : Function.Bijective added
  node : Fin (length + 1) → catalog.GeneratedKernel
  starts_at_top : node 0 = catalog.generatedKernel ∅
  ends_at_bottom :
    node ⟨length, Nat.lt_succ_self length⟩ =
      catalog.generatedKernel catalog.fullIndexSet
  classification : ∀ r : Fin length,
    GeneratorStepClass catalog (node r.castSucc) (node r.succ) (added r)

/-- The stutter-free subsequence; every adjacency is a strict DAG step. -/
structure StrictKernelChain (catalog : Catalog arena) where
  length : Nat
  added : Fin length → catalog.Index
  node : Fin (length + 1) → catalog.GeneratedKernel
  step : ∀ r : Fin length,
    catalog.StrictGeneratorStep (node r.castSucc) (node r.succ) (added r)

def GeneratorSchedule.strictSubsequence
    (schedule : GeneratorSchedule catalog) : StrictKernelChain catalog :=
  ...

def GeneratorSchedule.increment
    (schedule : GeneratorSchedule catalog)
    (r : Fin schedule.length) :
    Finset (arena.State × arena.State) :=
  (schedule.node r.castSucc).edgeCapture (schedule.node r.succ)

def StrictKernelChain.increment
    (chain : StrictKernelChain catalog) (r : Fin chain.length) :
    Finset (arena.State × arena.State) :=
  (chain.node r.castSucc).edgeCapture (chain.node r.succ)

structure StructuralArena where
  State : Type u

structure StructuralTheoremUnit (arena : StructuralArena) where
  PrimitiveIndex : Type v
  primitiveIndexFintype : Fintype PrimitiveIndex
  primitiveKernel : PrimitiveIndex → StructuralKernel arena.State
  Statement : Prop
  proof : Statement

structure StructuralCatalog (arena : StructuralArena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → StructuralTheoremUnit arena

def StructuralCatalog.jointKernel (catalog : StructuralCatalog arena)
    (selected : Set catalog.Index) : StructuralKernel arena.State

def StructuralCatalog.StructurallyLowersEscape
    (catalog : StructuralCatalog arena) (index : catalog.Index) : Prop :=
  let full := (catalog.jointKernel Set.univ).relation
  let without :=
    (catalog.jointKernel {candidate | candidate ≠ index}).relation
  full ≤ without ∧ ¬(without ≤ full)

structure StructuralStrictnessCertificate
    (catalog : StructuralCatalog arena) (index : catalog.Index) where
  inclusion :
    (catalog.jointKernel Set.univ).relation ≤
      (catalog.jointKernel {candidate | candidate ≠ index}).relation
  left : arena.State
  right : arena.State
  without_agrees :
    (catalog.jointKernel {candidate | candidate ≠ index}).relation left right
  full_separates :
    ¬(catalog.jointKernel Set.univ).relation left right

def Catalog.TrivialInCatalog (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  catalog.uniqueCapturePairs index = ∅

def StructuralCatalog.TrivialInCatalog
    (catalog : StructuralCatalog arena) (index : catalog.Index) : Prop :=
  ¬catalog.StructurallyLowersEscape index
```

必须证明 `Arena.toStructuralArena` 与 `Catalog.toStructuralCatalog` 保持每个 joint kernel、
leave-one-out strictness 与 witness。`GeneratorSchedule.added_bijective` 保证它是 catalog
generators 的完整 ordering；`classification` 使每个相邻 node 自身携 strict `GeneratorStep` 或
`CollapsedAddition` certificate，collapsed steps 贡献空 increment。删去它们得到
`StrictKernelChain`；其 `step` 字段使每条 adjacency 都是 strict generator DAG edge，故后者才是
DAG path。

`escapeAt`／`edgeCapture` 的 executable bodies 还必须分别安装
`letI := arena.stateFintype; letI := arena.stateDecidableEq`；上面的 signatures 已显式保留该要求。

---

## CIRPT-40　封印契约义务

`Contract.Seal` 指定 root 与 `SealCatalog` 数组。每个 catalog 的 `arena`、`units` 与
`size` 指定同一 exact vector catalog，并携带有限枚举、非退化性与 bundle 非空证明。
`rows` 对每个索引携带降低逃逸或平凡性证明；平凡行另携剩余目录的语义闭包归属证明。
`collisions` 保留同核成员的证明；`conclusion` 携带目录冗余或不可约证明。
这些义务由 Reg 编译期 Lean 内核检查。

报告期 `CompiledSeal` 从 root 的实际 import 闭包发现全部类型化登记，按 canonical
object arena 分组，与契约中的目录身份、完整成员集合、顺序、arena 与每个单位向量元素
机械核对。RootCatalog 的 expected 与 actual 由 `CompiledSnapshots` 核对。
输入缺失、不支持、重复、解码失败或目录不一致按现役诊断具名失败。

有限计数、角色分解、重数谱和 generated-kernel hierarchy 属于库内数学定义与证明，
不构成 Seal 的报告字段。判官不构建 Environment、不生成证明、不重验契约中的数学证明。

---

## CIRPT-41　生产报告字段

生产报告由 `Inspector` 按模块输出声明、公理闭包、import、来源与登记绑定。
模块的 `information_templates` 字段来自 `ArtifactRegistration.targetJson`，含
`schema_version`、`inventory`、`registered`、`records`；登记记录由
`TemplateBinding.recordJson` 编码。其记录状态为 `declared_validated`、
`declared_unresolved` 或 `undeclared`；消费端另核对身份是否失效。状态不得由散文或
输出标签改判。

Seal 的数学证据保留在编译契约中。报告评定核对导入闭包内登记的完整成员集合、
顺序、arena 与单位向量，不生成状态划分表、角色桶或统计 JSON。
库内的有限计数、角色分解与层级分析仍是数学对象；它们不构成生产报告字段协议。

输出地址、布局、hash 与 timing 不提供数学或准入权威。报告不得作为下一轮
Lean 编译的数学输入；StrataLint 消费登记状态和绑定身份，Lean 内核承载证明。

---

## CIRPT-42　结构与独立分析诊断

生产诊断来自编译输入解码与结构评定；数学证明由 Reg 编译期内核检查。
`Contract.Discovery`／`Decoder` 对缺失编译声明、不可解码输入、未知构造器和不许可的
公理依赖具名失败。`RootStructure` 核对模块路径、结构条目数量和 root ID。
生产评定中的 IE 诊断见第 31 节。

独立下游 `LeanInformationAuditRegAnalysis/Projection` 定义 IE-C039、IE-C040、IE-C041、
IE-C042 和 IE-C043，分别检查 generated node、generator transition、投影边界、
投影证据与分析字段的准入误用。其 schema、校验器与测试属于下游分析，
不进入生产报告的 Seal 字段。

### IE-C048　RealizationIgnoredByLaw

`CompiledRegistration.validateFinite` 消费契约中的 variation 证据标记。
缺失标记给出 `reason=missing_witness`，其它非 evidence 标记给出
`reason=invalid_witness`。具体 Law-variation 证明在 Reg 编译期检查。
本诊断先于 sensitivity 检查，不在报告期枚举 realizations 证明 variation。

### IE-C049　UnusedPrimitiveInBundle

variation 已有 evidence 而 sensitivity 不完整时，`validateFinite` 枚举有限
readout／anchor 索引，输出首个缺少有效见证的槽位和已检查 support。
`support` 是契约部分证据所覆盖的索引集合，不是判官重新计算的语义支持。
完整 sensitivity 证明在 Reg 编译期检查。

### IE-C050　ClosedTruthReadout

`ReadoutProvenance` 对编译项及其原始常量依赖执行允许表走查。
受保护定义沿类型与数据 value 走查；证明体保持不透明，证明命题仍参与身份检查。
外部叶的类型参数、实例与构造器字段仍须通过允许表，不能只按名称放行。
到达目标 theorem、statement identity、相应判定实例或专用证据时拒绝；
无法完成闭包或识别形式时同样拒绝。

`reason` 的优先序为 `incomplete_closure`、`forbidden_dependency`、`unclassified_form`。
前者的 provenance 为 `null`；禁止依赖输出已走查名称的排序数组；
未分类形式输出具名分类、位置与已走查名称，缺少该证据时为 `null`。
模板 enrollment 也消费 provenance 检查，使用带 template 名的诊断。
这些有界计算不调用 Lean conversion 或类型检查器，也不赋予报告数学证明权威。

---

## CIRPT-43　数学用例与下游分析检查

### T-CIRPT-001　CUT constructor

验证 `cutKernel q` 与 `Setoid.ker q` 完全一致。

### T-CIRPT-002　FLOW constructor

验证 `flowKernel F` 与把 $F$ 直接视为 CUT 的 kernel 一致。

### T-CIRPT-003　ADMIT mixed fiber

在 Bool 状态上构造同一 CUT fiber 中一个合法、一个非法状态；`D_A` 非空且 exact count 正确。

### T-CIRPT-004　ADMIT descent

当 $A=\bar A\circ q$ 时，`D_A=∅`。

### T-CIRPT-005　ANCHOR shadow

验证 symmetric anchor residual count 等于两倍 shadow count。

### T-CIRPT-006　FLOW carry

验证 `D_F` 与 carry witness 等价。

### T-CIRPT-007　四角色 union

构造四个分量均有 witness 的有限模型，验证 unified residual 等于四者并集。

### T-CIRPT-008　overlap no double count

一个 pair 同时违反 CUT 与 ADMIT；总 escape count 只计一次，signature 为对应双位。

### T-CIRPT-009　bundle representation invariance

用单一 product CUT 和两个 coordinate CUT 表示同一 kernel，所有 rate 和 gain 完全相同。

### T-CIRPT-010　proof anchor erasure

改变 proof term，但 primitive bundle 不变；逃逸结果不变。

### T-CIRPT-011　domain immunization blocked

缩到单点 admitted subtype 会得到零 residual，但 seal 必须拒绝把该值替代 full-arena 结果。

### T-CIRPT-012　dynamic behavior

有限 FLOW 下，行为 kernel 单调缩小并在有限步稳定。

### T-CIRPT-013　leave-one-out residual identity

验证 unique capture pairs 等于 `Residual(K_without, K_unit)`。

### T-CIRPT-014　multi-role theorem

一个 theorem bundle 同时含 FLOW 与 ADMIT primitive；unique count 与 role signature partition 一致。

### T-CIRPT-015　meta-arena self application

系统 theorem 在显式 Stage arena 上使用同一 primitive kernel API，不调用第二套 evaluator。

### T-CIRPT-016　closed truth collapse

对任意已证明闭命题，把其 truth readout 设为常值 `true`；验证 kernel 为全关系且 unique capture 为零。

### T-CIRPT-017　arena equivalence transport

用两个经 `Equiv` 连接的有限状态编码输运同一 catalog；验证全部 residual、rate 与 theorem gain 完全相等。

### T-CIRPT-018　non-equivalent state duplication

复制一个状态形成非等价 arena；验证 raw pair count 可以变化，并且系统拒绝把它称为 representation-preserving comparison。

### T-CIRPT-019　cross-arena no aggregation

同一次 Seal 可含不同 arena 的 SealCatalog；每个目录携带自身数学证据，报告不生成跨 arena 统计总分。

### T-CIRPT-020　capture spectrum identities

在有限 fixtures 上逐项验证 spectrum partition、$h(0)$、$h(1)$、incidence first moment
与 overlap second moment；修改任一 reflected numeral 必须使 certificate 失败。

### T-CIRPT-021　layer-chain transport

经已证明 arena `Equiv` transport 后，每个 layered count/rate 与 unresolved count/rate
layer-chain 输运需要对应的数学证明；kernel address 相同不提供该证明。

### T-033　E1 four-node quotient

Bool-pair arena 上的 `fst`／`snd`／`id` 生成恰四个 extensional kernel classes；两个 coordinate
nodes 不可比，equal-kernel subsets collapse，两个指定 schedules（含 classified stutters）与
leave-one-out verdict 符合
第 35 节 fixture。

### T-034　unified causal strict chain

第 43.1 节 literal `CfU` 的四层 escape counts 与三段 increments 按第 35 节 T-034 验收；
chain partition/telescope 通过，flat $U_{Obs}=U_{Int}=0$。

### T-035　structural witness

在无限 State 上构造 finite-index structural catalog；不枚举 State，由显式 pair 同时证明
without-kernel agreement 与 full-kernel separation。

### T-037　generated-node extensional quotient

两个不同 subsets 生成同一 truth table 时 materialize 一个 node，并记录 collapsed addition；
强行输出两个 nodes 得 IE-C039。

### T-038　strict edge and Hasse classification

每条 edge 是一次 generator addition 且 count 正；把 stutter 写 edge 或漏写 collapsed addition
得 IE-C040。E1 的 $K_\varnothing\xrightarrow{id}K_{full}$ 是 strict shortcut 且
`is_cover: false`；diamond 有四个 distinct cover endpoint pairs、六个 labeled cover transition
rows 为 `is_cover: true`。翻转任一 classification 或让 ASCII 绘出该 shortcut 同样得 IE-C040。

### T-039　bounded boundary completeness

不 materialize 完整 $2^m$ lattice，仍包含 top、bottom、全部 leave-one-out、certified-schedule 与
requested nodes；`edges` 仍包含全部 certified-schedule strict transitions 与显式 requested
transitions，且每个 edge endpoint、leave-one-out node 与 schedule node reference 都解析到一个
materialized `node_key`。删除一个 required transition 得 IE-C040；逐类删除一个必需 node 或制造
dangling reference 得 IE-C041。

### T-040　projection certificate mutation

分别篡改 node escape、edge count、schedule increment、matrix、spectrum 与 verdict，均得 IE-C042。

### T-041　projection non-interference

改变 ASCII layout、node IDs 或 heuristic path 不改变任何 Lean proposition；尝试把这些字段接入
admission 得 IE-C043。

---

## CIRPT-44　数学性质与生产边界

### AC-CIRPT-001　Primitive completeness

每个被 seal 的 theorem unit 都有 kernel-checked C-IRPT primitive normal form。

### AC-CIRPT-002　One kernel engine

CUT、FLOW、ADMIT、ANCHOR 和 theorem gain 全部调用同一 `JointKernel`／`Residual` 内核。

### AC-CIRPT-003　No role weighting

四角色分解只产生 exact signature counts，不参与加权判词。

### AC-CIRPT-004　Representation invariance

同 joint kernel 的 primitive representations 产生 byte-for-byte 相同的数学 count fields。

### AC-CIRPT-005　Full-domain invariance

ADMIT 不改变 arena 分母；domain restriction 不得替代 canonical rate。

### AC-CIRPT-006　Certificate erasure

proof identity 与 seal identity 不进入 object-level kernel。

### AC-CIRPT-007　Dynamic closure reuse

FLOW 动态分析通过 `controlledBehavior`／`DynClosure` 的 CUT kernel 接入同一引擎。

### AC-CIRPT-008　Single compilation

数学定义与证明通过依赖驱动的 Lean 编译核验；Reg 契约携带数学证据，报告读取编译产物，不生成第二份证明源码或新定理。

### AC-CIRPT-009　Arena transport invariance

经 Lean `Equiv` 输运的 catalogs 产生完全相同的 exact counts、rates 与 pass/fail 判词。

### AC-CIRPT-010　No cross-arena scalar

不等价 arena 的结果保持依赖类型分区，不产生无来源的全局标量。

### AC-CIRPT-011　Closed truth erasure

闭 theorem 的 proof truth 不得成为对象层 primitive；只有显式 object primitive law 可进入 object kernel。

### AC-CIRPT-012　Scoped maximal catalogs

每个 root import closure 内的 canonical arena 恰有一个覆盖全部可见 members 的 maximal
catalog；occurrence identity 为 `(canonical arena declaration, theoremName)`，所有 companions
均 catalog-qualified，analysis view 不承担 positivity。

### AC-CIRPT-013　Certified shared analysis

exclusive vector、overlap/refinement matrices、multiplicity spectrum、role totals 与
positive/negative verdict 均由一般 theorem 加 reflected equalities kernel-certify。

### AC-CIRPT-014　Layered capture distinctness

`LayerChain` 的 inclusions、partition、strictness 与 exact rates 都被认证；任何输出或
测试都不把 layered increments 称为 cumulative flat unique capture。

### AC-CIRPT-015　Diagnostic address isolation

生产报告不输出 kernel address coincidence；地址摘要不提供数学对应或准入证据。

### AC-CIRPT-016　完整封印证据

`SealRow` 对 exact catalog 的每个索引提供编译证明，`SealCatalog.conclusion`
保存完整目录的结论。报告从实际 import 闭包核对 exact vector，不产出逐成员统计判词。

### AC-CIRPT-017　Generated-kernel closure

每个 maximal catalog 的 hierarchy nodes 按 exact relation equality 取商；order、internal
lattice operations、strict steps、collapsed additions 与 chain-independent invariants 全部由
IE-040--IE-055 覆盖。

### AC-CIRPT-018　Universal structural reach

任意 State 的 theorem 可进入 `StructuralArena`／`StructuralCatalog`，只要它有 finite primitive
bundle 与 faithful realization；acceptance 由 strict inclusion 和 pair witness证明。finite
`Arena` embedding 保持同一判词，finite-only `StructuralNovelty` 不冒称 universal。

### AC-CIRPT-020　层级数学与生产报告边界

库内 generated-kernel lattice、strict transitions 和 certified chains 的关系及计数
须由 Lean 证明。它们不要求生成报告的 nodes、edges、矩阵、重数谱、角色桶或
certificate-name 数组；生产报告字段只遵守第 30 节。

---

## CIRPT-45　最终统一主式

对每个 theorem $i$：

$$
\Pi_i
=
\text{其 CUT/FLOW/ADMIT/ANCHOR primitive bundle},
$$

$$
K_i
=
\bigcap_{p\in\Pi_i}\kappa_p.
$$

对完整 catalog：

$$
K_I
=
\bigcap_{i:I}K_i.
$$

对 theorem $i$：

$$
\boxed{
U_i
=
\operatorname{Residual}(K_{-i},K_i).
}
$$

信息增益：

$$
\boxed{
\delta_i
=
\frac{|U_i|}{|X|(|X|-1)}.
}
$$

伴随数学命题：

$$
\boxed{
G_i
:\Longleftrightarrow
\delta_i>0.
}
$$

增强 theorem：

$$
\boxed{
\widehat\tau_i
:
P_i\land G_i.
}
$$

因此最终闭环是：

$$
\boxed{
\text{theorem statement}
\to
\text{C-IRPT primitive normal form}
\to
\text{joint kernel}
\to
\text{leave-one-out residual}
\to
\text{exact escape gain theorem}.
}
$$

这就是统一信息逃逸计算能力：

$$
\boxed{
\text{不是为每一种数学对象发明评价体系，}
}
$$

而是：

$$
\boxed{
\text{把所有已形式化角色的区分能力归约到同一个 kernel residual 演算。}
}
$$

---

# 第三部　Lean 4 核心工程规范

## 17. 工程目标

规范入口为 `make lean-report`。Reg 的类型化登记、RootCatalog 与 Seal 通过同一次
依赖驱动的 Lean 编译检查数学义务；判官使用 `RawArtifacts.Store` 读取编译部件，
按契约类型发现输入并执行结构评定。

登记用 `Contract.Registration`，模板用 `Contract.TemplateEnrollment`，目录与封印用
`Contract.RootCatalog` 和 `Contract.Seal`。实现不进入 Reg 的依赖闭包；登记只含契约
数据与数学证明，不含也不调用判官代码。报告输出第 30 节规定的模块声明、材料和登记绑定。

实现或规则变化不重编 Reg，也不使有效报告失效。新增或改动的登记由编译依赖变化
交给当前实现评定；契约接口升级须同次交付迁移全部用法并删除旧路径，受影响闭包
自动重编、重评。提取语义或报告格式变化更新报告格式标识并全部重提取。

数学目录不使用历史 baseline、人工评分或跨 arena 标量。报告可以复用已有编译与评定
工件；复用依赖编译 trace、utility 输入和报告格式，不以判官程序字节决定。
报告不得生成第二份 Lean 证明源码，不在报告期安装声明，也不以旧判词一致代替当前实现验证。

---

## 18. 数学库与契约地址

`D5/S3/ConceptDynamics/CIRPT/` 承载 primitive 与 bundle；
`InformationEscape/` 承载有限 arena、theorem unit、目录、逃逸与留一增益；
`InformationEscapeHierarchy/` 承载 generated kernel、chain 与 structural 目录；
`InformationEscapeCounting/` 承载融合计数及对应证明。

`Arena` 包含 State、有限枚举实例与可判等实例，非退化性是单独的
`Arena.Nondegenerate` 命题。SealCatalog 的 nondegenerate 字段承载该证明；
未封印登记不因此取得额外非退化要求。
契约源码位于 `tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/`；
报告评定源码位于 `tools/lean-inspector/LeanInformationAudit/`。
Reg 的目录与 seal 位于 `Reg/Catalogs/**` 的 RootCatalog／SealedCatalog 保留叶。

---

## 24. theorem 登记语法

### 24.1 新 theorem 原生语法

新 theorem 使用普通 Lean theorem 声明与证明。登记使用独立的
`def x : Contract.Registration theoremName Readout From Residual := {…}`，
完整字段与契约参数遵守 spec A5.5／A5.6。`realization` 使用适合该对象的
`Implementation` 构造器；`correspondence`、`bundleNonempty`、`variation` 与
`sensitivity` 携带对应的类型化数学义务，`readout`、`sourceSelection`、`escapeFrom`
与 `continuation` 保留四槽输入及源选择。

`arena`、`objectArena`、`catalog`、`unitName` 与 `realizationName` 明确对象舞台、
目录与具名证据。原舞台与 canonical object arena 的对应由契约的 `correspondence`
在 Reg 编译期检查；跨舞台对应必须提供适用的 transport 证据。
登记声明只包含契约数据和数学证明，不调用判官。报告期通过编译常量的精确契约类型
发现登记。IE-C048／IE-C049 由 `CompiledRegistration`、IE-C050 由
`CompiledAssessment`、含别名归一的 IE-C024 由 `RegistrationRelations` 按触发条件消费。

### 24.2 legacy theorem 登记

登记使用 `def x : Contract.Registration … := {…}` 的带类型数据声明，完整字段与
契约参数遵守 spec A5.5／A5.6。`arena`、`objectArena`、`catalog` 指明舞台与目录，
`realization := .legacy …` 携带实现、primitive bundle 与具名等价桥。

其中等价桥必须是 Lean theorem：

```lean
existingTheoremStatement ↔
  PrimitiveLawArenaName.Law primitiveBundleExpression
```

不得是字符串说明。跨原 arena 的 legacy realization 必须给出 faithful injection/restriction
equations，并在 `equivalence` 两个方向实际消费输入 hypothesis。源重构、Law 对应与
证据绑定由 `CompiledSourceContract`、`CompiledEvidence` 及契约证明字段核对。
legacy realization 使用同一类型化发现与编译评定路径；IE-C048／IE-C049／IE-C050
及含别名归一的 IE-C024 的消费者与 §24.1 相同。

### 24.3 禁止字段

登记结构中不得出现：

```text
score
weight
importance
priority
minimum_gain
threshold
baseline
parent
previous
owner_override
novelty_class
role_weight
```

### 24.4 唯一登记

唯一性按 occurrence，而不是 theorem declaration 裸名字全局判断。键：

```text
(CanonicalArenaName, theoremName)
```

在 sealing root 的整个 import closure 中恰出现一次。每个 occurrence：

- 恰有一个 theorem unit；
- 恰属于一个 explicit catalog 与一个 canonical object arena；
- 恰有一个 kernel-checked primitive bundle；
- 恰有一个 theorem-to-bundle realization path。

同一 theorem declaration 可以通过分别命名、kernel-checked 的 realization 登记到不同
canonical arenas，并在各自 maximal catalog 中独立结算；同一 canonical arena 上的第二次
登记与 catalog/root spelling 无关，统一 IE-C002 fail-closed。不同合法 occurrences 的 unit、
realization 与 companions 必须 catalog-qualified；这些 qualified names 的碰撞由 IE-C025
fail-closed。允许一个 theorem 的 primitive bundle 内含多个角色 primitive；不允许同一
occurrence 在多个可选 bundle 之间选择。

同一 root import closure、同 canonical arena 的全部 occurrences 按一个目录 ID 分组。
`validateMaximalCatalog` 要求至少一个 canonicalMaximal 成员；缺失时发 IE-C026。
该组出现多个目录 ID 时发 IE-C024。核对范围是当前 root 的实际 import 闭包。

---

## 25. 编译契约与登记投影

### 25.1 registry entry

`InformationRegistryEntry` 是判官内部对编译契约的投影，不是 Reg 声明的接口类型。
其 `theoremName`、`unitName`、`arenaName`、`objectArenaName`、`realizationName`、
`catalogId`、`catalogKind` 与 `registrationModuleName` 来自类型化输入及编译模块归属。
Reg 只声明 `Contract.Registration`，不构造或调用该内部投影。

`rootId` 是 RootCatalog 或 Seal 所在模块的 `Name`，由编译产物的模块归属核对。
`registrationModuleName` 取登记常量的编译模块归属，只用于 import-closure provenance、
artifact 与 coverage 核对，不能过滤 seal membership。grouping key 取解析后的
`canonicalObjectArenaName`；`arenaName` 是 presentation，不能充当 object identity。

### 25.2 编译声明的可见性

判官使用 `RawArtifacts.Store` 读取编译部件，`Contract.Discovery` 按精确契约类型发现
`Registration`、`TemplateEnrollment`、`RootCatalog` 与 `Seal`。输入是构造器树或常量引用；
需要执行输入代码才能取得的值按模块、声明名与原因具名失败。

- 每个 seal 消费其 root import closure 中全部类型化登记，不过滤 imported entries；
- imported 编译模块中的登记通过同一发现路径进入 consumer/seal；
- 按 `canonicalObjectArenaName` 将全部可见 peers 合为一个 maximal catalog；
- 同一 `(canonicalObjectArenaName,theoremName)` 第二次登记触发 IE-C002；
- 同一 theorem 在不同 canonical arena 的独立 kernel-checked realization 是合法 occurrence；
- catalog-qualified companion names 不得碰撞，碰撞触发 IE-C025。

### 25.3 编译产物真源

catalog 只由编译后的类型化登记、声明与实际 import 闭包构造。RootCatalog 的 expected
字段给出预期集合；报告期将其与实际登记逐项核对。根清单由 Reg 的路径和 import 闭包
确定，辅助 root 只表示该闭包内的分析范围。Markdown、Blueprint、YAML、文件头、正则
或 Git diff 均不决定 catalog theorem 集。报告期不建 Environment、不初始化扩展，
不调用 elaborator、Meta、类型检查器或 Lean kernel。

### 25.4 registry 完整性

`CompiledRegistration.validateCore` 要求已解码的数学义务中 correspondence 为 evidence。
`sourceBound` 登记要求 theoremName、unitName、realizationName 与 arenaName 均能解析到
编译常量；源绑定的其余条件由 `CompiledSourceContract` 等源评定路径检查。
非 sourceBound 登记另核对：

- theoremName 不使用保留的 companion 名，且编译声明 kind 是 theorem；
- unitName 与 realizationName 存在；
- arenaName 与 canonicalObjectArenaName 存在；
- unitName 的编译类型头是 `TheoremUnit`。

契约证明字段在 Reg 编译期绑定目标、realization、舞台与 primitive bundle；报告不重验
这些数学证明。registrationModuleName 来自登记常量的实际编译模块，root 的实际 import
闭包确定可见登记。`validateUnique` 核对 occurrence key、unitName 与 realizationName 的
唯一性；同一 theoremName 在不同 canonical arenas 的 occurrences 可以分别存在。
目录分组使用 canonicalObjectArenaName，`validateMaximalCatalog` 要求组内目录 ID 一致
并至少有一个 canonicalMaximal 成员。Seal 另核对完整成员、顺序与单位向量，
生成的 catalog-qualified 名与已有常量或其它 occurrences 碰撞时失败。

---

## 26. 封印契约与报告评定

### 26.1 声明形式

`Reg/Catalogs/<目录>/RootCatalog.lean` 恰含一个 `Contract.RootCatalog`、不含 Seal。
同树的 `SealedCatalog.lean` 恰含一个 RootCatalog 和一个 `Contract.Seal`；其它模块
不得包含这两类结构输入。RootCatalog.data.expected 是完整预期成员集合。

Seal 的 catalogs 字段含 `SealCatalog`。各 catalog 的 arena、units 与 size 指定同一
向量目录；nondegenerate、bundleNonempty、rows、collisions 与 conclusion 承载
该目录上的类型化数学证据，enumeration 指定 arena 的有限状态枚举。
每行 `SealRow` 只含 conclusion：positive 携降低逃逸证明，zero 携平凡性与
剩余目录的语义闭包归属证明。目录结论为 redundant 或 irredundant，
由 Lean 内核在 Reg 编译期检查。

### 26.2 报告执行边界

`ArtifactAssessment` 发现 root import 闭包内的全部类型化输入，核对 occurrence key、
模板、源绑定和 realization 证据，并由 `CompiledSnapshots` 核对 expected 与 actual。
`CompiledSeal` 按 canonical arena 分组，核对编译后的目录身份、完整成员集合、
成员顺序、arena 与每个索引的单位值。数学证据不在报告期生成或重新检查，
seal 不输出统计数据。

逐成员结论保存在编译契约中；零成员本身不使合法冗余目录失败。报告按编译登记的
canonical arena 与 catalog identity 分组，不计算数学统计或层级布局。
输入缺失、不支持或不一致须具名失败，不输出伪造成功。

### 26.3 单次编译与唯一读取路径

Reg 编译直接检查契约数学义务，不生成第二份 Lean 源码或启动第二次证明编译。
报告读取编译部件并进行有界结构计算，不安装声明、不执行输入代码、不构建 Lean
Environment。生成的单位、realization 与 catalog 仅是报告数据视图。

`CompiledExpressions.sameShape` 是对编译器已检查项的有界语义比较，不是定义相等判定器。
比较两个 `Decidable.decide` 应用时，只比较命题并略过其判定实例参数：同一命题的
任意判定实例产生命题相等的布尔值，依据 Lean 的 `decide_eq_decide`。该特殊规则
只适用于 `Decidable.decide` 的实例参数，其它实例与字典参数仍按通常规则比较。
未知形式及预算耗尽保留具名诊断。

---

## 27. 报告数据视图的命名

`catalogQualifiedName` 将 root、canonical object arena、catalog 和原 theorem 绑定到
同一 occurrence 地址。报告使用该地址命名单元、primitive realization 与 catalog
数据视图，核对不同合法 occurrences 的名称不碰撞；名称碰撞由 IE-C025 具名拒绝。

数学证据由编译契约中的 `SealRow.conclusion`、`SealCatalog.collisions` 和
`SealCatalog.conclusion` 提供。报告不生成 lowering、enriched、triviality 或根级
冗余伴随证明，不把证据字段当作新 theorem unit。

现役保留名称分类由 `RegistrationData.generatedCompanionSuffixes` 与
`ReadoutProvenance` 消费，用于拒绝把判官保留名字登记成 concept；该分类不承诺
对应名称具有生产者。报告视图不安装到 Lean 环境，也不改变原声明身份。

---

## 28. 编译证明构造

### 28.1 首选反射证明

所有有限计算函数应满足：

```lean
@[implemented_by ...]
```

或普通可归约定义，并有 correctness theorem。

终局命令可以构造：

```lean
by native_decide
```

等价 proof，但规范更推荐：

1. 计算具体 `Nat`；
2. 生成 equality proof；
3. 通过通用 correctness theorem 得到目标命题。

### 28.2 不信任计算输出

一个 meta 程序打印：

```text
uniqueCaptureCount = 5
```

本身不是数学证明。

必须最终生成 Lean proof term：

```lean
0 < uniqueCaptureCount catalog index
```

并由 kernel 接受。

### 28.3 可信边界

数学信任边界是：

- Lean kernel；
- core reduction；
- theorem definitions；
- 通用 correctness proofs。

Reg 数学义务在 Lean 编译期由内核检查。报告 IO 层只负责：

- 读取编译部件与声明的常量依赖；
- 解码类型化契约构造器与常量引用；
- 对编译字段进行有界结构评定；
- 输出投影。

报告期不构建 Environment，不调用 elaborator、Meta、类型检查器或内核。

---

## 29. 单次编译数据流

```text
D5 数学定义与证明 + Interface 契约类型
                    │
                    ▼
Reg 类型化登记、RootCatalog 与 Seal
                    │ Lean 编译期检查数学义务
                    ▼
编译部件、声明类型、构造器字段与 import 闭包
                    │ RawArtifacts / Discovery / Decoder
                    ▼
ArtifactAssessment / CompiledSnapshots / CompiledSeal
                    │ 有界结构评定，不构建环境或证明
                    ▼
生产报告与只读数据视图
```

接口与实现分包；Reg 不依赖实现。判官实现或规则变化不重编 Reg，整份有效报告复用。
新增或改动的登记按编译依赖闭包使用当前实现评定。接口升级须同次迁移全部用法，
受影响的 Reg 自动重编并重评，不保留兼容读取路径。提取语义或报告格式变化须更新
报告格式标识，严格读取器拒读旧格式，全部模块重提取。
kernel-address coincidence 无回边进入分组或判词。

---

## 30. 只读报告规范

### 30.1 模块与登记绑定

报告以当前 `stratalint-raw-lean-report-v3` 格式发布。每个模块记录其声明、import、来源、
公理闭包及适用的登记绑定；格式由严格读取器检查。
`information_templates` 的容器形状为：

```json
{
  "schema_version": 1,
  "inventory": [],
  "registered": [],
  "records": []
}
```

inventory、registered 与 records 的成员来自当前编译产物；登记绑定状态与证据
由 `TemplateBinding.recordJson` 编码，不由调用者拼写。格式或提取语义改变时更新
报告格式标识并全部重提取，不双读旧格式。

### 30.2 Seal 的消费边界

Seal 的证据由 Reg 编译期内核检查；判官从当前 root 的导入闭包重建完整目录，
核对其身份、arena、成员顺序与单位向量。报告不发射独立 seal 导出包或统计表。
数学计数、角色直方图与层级对象可作为 Lean 库结果使用，不是报告期生成的协议。

### 30.3 单向数据流

报告是编译产物的只读视图，不能回写为 Lean 的数学输入。
StrataLint 消费登记绑定、声明身份、公理闭包与依赖等机器数据；可视化和文档
可以消费同一报告，但输出字段、地址、布局与 timing 不证明数学命题。

---

## 31. 契约与评定诊断

以下诊断由生产编译产物评定路径发出。解码、源绑定、模板和 join 的其它具名
诊断由各自 `Contract`／`Compiled*` 模块给出；结构检查不代替 Reg 编译期数学证明。

| code | 现行触发条件 | 实现 |
|---|---|---|
| IE-C001 | 非 source 登记的目标不是 theorem，或 Seal 的登记集合为空 | `CompiledRegistration.validateCore`、`CompiledSeal.consume` |
| IE-C002 | 同一 canonical object arena／theorem occurrence 重复 | `CompiledRegistration.validateUnique` |
| IE-C003 | arena 引用缺失、别名解析失败、不支持或预算耗尽 | `RegistrationRelations.resolveCanonicalArenaName`、`CompiledRegistration.validateCore` |
| IE-C006 | correspondence 不是 evidence，或具名 unit／realization／目标结构不匹配 | `CompiledRegistration.validateBinding`／`validateCore` |
| IE-C009 | 契约依赖含不许可公理，或目录数据视图所需常量没有值 | `Contract.Decoder`、`CompiledSeal.consume` |
| IE-C011 | 登记目标使用保留的 companion 名 | `CompiledRegistration.validateCore` |
| IE-C013 | Seal 成员的 bundleNonempty 不是 evidence | `CompiledSeal.consume` |
| IE-C024 | 同一 canonical arena 的 occurrences 分属多个 catalog IDs | `RegistrationRelations.validateMaximalCatalog` |
| IE-C025 | 不同 occurrences 的 unit／realization／qualified companion 名碰撞 | `CompiledRegistration.validateUnique`、`CompiledSeal.consume` |
| IE-C026 | 同一 arena 没有 canonicalMaximal 成员 | `RegistrationRelations.validateMaximalCatalog` |
| IE-C028 | 独立快照的成员、statement identity、贡献模块不一致，或 Seal 的目录、arena、成员数量、顺序及完整单位向量不一致 | `CompiledSnapshots`、`CompiledSeal` |
| IE-C048 | variation 缺失或不是 evidence | `CompiledRegistration.validateFinite` |
| IE-C049 | variation 有效而某有限 readout／anchor 缺少 sensitivity 见证 | `CompiledRegistration.validateFinite` |
| IE-C050 | provenance 闭包不完整、到达禁止依赖或出现允许表之外的形式 | `ReadoutProvenance`、`ArtifactRegistration`、`CompiledAssessment` |

IE-C002 的 payload 含 `object_arena`、`theorem_name`、排序后的
`registration_modules` 与完整 `count`。IE-C024 的 payload 含 root、arena 与排序后的
catalog IDs；IE-C025 含 root、catalog、generated name 与排序后的 occurrence keys；
IE-C026 含 root、arena 与排序后的 theorem names。
IE-C028 按具体检查位置报告 component 与 expected／actual；不能从同一个诊断码
推导所有消息都采用相同字段或包含数学统计。

IE-C048／IE-C049 消费编译契约证据，具体标记与优先序见 CIRPT-42。
IE-C050 的原因与走查边界也见该节。逐成员降低逃逸、平凡性、剩余目录闭包归属、
同核碰撞与目录结论保存在 `SealRow`／`SealCatalog` 的编译证明中。
报告不生成这些证明，不输出逐成员计数或 disposition 统计。

---

## 32. 反平凡化硬规则

### R-001　零边际分类

```text
uniqueCaptureCount = 0  => certified `TrivialInCatalog` classification
```

分类成功不授予 positivity、novelty 或 admission；first-freeze gate 仍独立判定。

### R-002　正值无人工阈值

```text
uniqueCaptureCount > 0 => mathematical nontriviality condition satisfied
```

系统不得写：

```text
uniqueCaptureCount >= 10
```

除非 `10` 本身由另一个数学 theorem 唯一推出；v1 不允许此扩展。

### R-003　proof 长度不参与

proof AST、tactic 数量、文件行数仅可作为性能诊断，不得进入 `LowersEscape`。

### R-004　名称不参与

Name、GID、路径仅用于寻址，不得进入增益公式。

### R-005　文献新颖性不参与数学率

外部文献是否已有该结论属于来源学问题，不是 kernel escape rate 的组成。文献审计可以作为独立投影，但不能改变 $\delta_i$。

### R-006　过完备族的非单调重新封印

若新 theorem 使旧 theorem 的边际归零，完整合法族成功重新 seal，旧 theorem 非单调地改分类为 certified `trivial_in_catalog`，并在 `SealCatalog.conclusion` 携带冗余证明；旧成员保留，待首次冻结对象的 positive admission 只由它自身的 positivity 判定，旧零 peers 不否决新正对象。

### R-007　无顺序优先

先声明或后声明不影响结果。

### R-008　无历史优先

旧 theorem 或新 theorem 不具有先验所有权。

### R-009　无 API 冒领

仅用于命名、包装、simp 或重导出的 theorem 若其 primitive joint kernel 可由其他族恢复，则自动为零。

### R-010　辅助证明不拆成 theorem unit

内部 proof support 应优先使用：

- private theorem；
- local have；
- section lemma；
- implementation detail declaration；

只有作为独立数学 concept 对完整族提供正边际时，才进入 public information theorem catalog。

---

## 33. 数学计算的性能边界

设状态数为 $n=|X|$，读出数为 $m=|I|$。下面的复杂度与计算方法适用于数学库和
独立分析，生产报告消费已编译的 Seal 证明字段，不枚举状态对或计算留一统计。

有限计算路线必须精确实现原定义，遵守既有运行资源边界并有相应 Lean 正确性证明。
对 generated-kernel lattice，存在性证明不要求枚举全部 $2^m$ subsets。
独立下游分析的 projection schema、strict-transition 验证与测试由
`LeanInformationAuditRegAnalysis/Projection` 承载；它不进入生产报告的协议或准入权威。
任何截断或布局都不能改变数学结论的量词和已证范围。

### 33.1 朴素算法

直接对每个 theorem、每个 pair、每个其他 theorem 比较：

$$
O(m^2n^2).
$$

overlap 与 refinement matrix 的 fallback 同为 $O(m^2n^2)$；实现必须复用一次生成的
per-pair theorem-separation bit signature，不能为 unique、overlap、spectrum 与 role
analysis 各自重新判一次 kernel。复杂度优化不得改变 exact set semantics。

### 33.2 推荐 kernel-class 算法

核心引擎不要求 theorem bundle 具有一个可序列化的共同输出类型。对每个 theorem $i$，直接用其 `DecidableKernel` 在有限状态集上构造 canonical class id：

$$
\lambda_i:X\to\mathrm{Fin}(k_i),
$$

其中 class id 按 arena 状态 canonical 顺序首次出现时分配，并满足：

$$
\lambda_i(x)=\lambda_i(y)
\iff
K_i(x,y).
$$

对每个状态 $x$ 计算完整 kernel signature：

$$
\sigma(x)=(\lambda_i(x))_{i\in I}.
$$

对每个 $i$ 计算留一 signature：

$$
\sigma_{-i}(x)=(\lambda_j(x))_{j\neq i}.
$$

可通过 prefix/suffix hash 或结构化 persistent vector 达到约：

$$
O(mn+mn\log n)
$$

的 grouping 成本，而不枚举所有 pair。

hash 只用于加速 grouping；任何 hash collision 必须通过 kernel relation 复核，不得改变数学结果。

### 33.3 fiber 计数公式

完整 signature 等价类大小为 $a_k$ 时：

$$
|E_I|
=
\sum_k a_k(a_k-1).
$$

对留一 signature 的 fiber $B$，其中按 theorem $i$ 的 primitive joint-kernel class 再分为 $B_v$，则：

$$
|U_i|
=
\sum_B
\left[
|B|(|B|-1)
-
\sum_v |B_v|(|B_v|-1)
\right].
$$

这与：

$$
U_i=\operatorname{Residual}(K_{-i},K_i)
$$

的有序 pair 定义完全一致。

## 34. Hash 与确定性

### 34.1 canonical ordering

仅用于 artifact 稳定性的排序键：

1. root canonical Lean `Name` encoding；
2. catalog stable `CatalogId` encoding；
3. canonical object arena `Name` encoding；
4. theorem occurrence canonical Lean `Name` encoding；
5. state canonical `Repr` 不得作为数学顺序；
6. state witness 排序必须由 arena 明确提供 `LinearOrder State`，或不输出“最小” witness。

### 34.2 hash 不参与数学

statement SHA、source SHA、artifact SHA 可以用于完整性校验，但不得进入：

$$
K_S,
E_S,
\varepsilon(S),
\delta_i.
$$

### 34.3 重编译确定性

相同 Lean environment 和相同 compiler/toolchain 应产生字节稳定 artifact。

若 artifact 不稳定但 kernel theorem 相同，数学通过状态不应改变；不过工程测试仍应报告非确定性。

生产报告不发射 primitive kernel address 或 coincidence class。数学核的相等不由地址摘要决定。

---

## 35. 数学用例与结构检查

### T-001　单一非恒等 CUT primitive

状态：`Bool`。  
primitive readout：`id`。  
期望：

$$
E_I=\varnothing,
$$

删除该 primitive theorem 后：

$$
|E^{-i}|=2,
$$

故：

$$
|U_i|=2>0.
$$

### T-002　常值 CUT primitive

状态：`Bool`。  
primitive readout：常值。  
期望：

$$
|U_i|=0.
$$

期望：完整合法 catalog 成功 seal，零成员认证为 `trivial_in_catalog`，catalog 的 `SealCatalog.conclusion` 携带冗余证明；该零对象不获 positive admission。

### T-003　两个互补坐标

状态：`Bool × Bool`。  
primitive readout：`Prod.fst`、`Prod.snd`。  
期望：两者均正增益，完整逃逸为零。

### T-004　重复坐标

状态：`Bool × Bool`。  
primitive readout：`Prod.fst` 与 `Bool.not ∘ Prod.fst`。  
两者 kernel 相同。  
数学期望：双方同时零边际；SealRow 携带平凡性与闭包归属证明，SealCatalog 的 collisions 携带同核证明，conclusion 携带冗余证明。报告核对完整目录，不输出 collision 统计。

### T-005　product 包装过完备

primitive readout：`Prod.fst`、`Prod.snd`、`id`。  
`id` 可恢复两个坐标；两个坐标也可由 `id` 恢复。  
期望：与 T-022 一致，三个成员均零边际、均认证为 `trivial_in_catalog`；完整三元素 catalog 以 redundant 结论成功 seal，零对象不获 positive admission。

### T-006　只保留 product

primitive readout：`id : Bool × Bool → Bool × Bool`。  
期望：正增益，通过。

### T-007　只保留两坐标

primitive readout：`Prod.fst`、`Prod.snd`。  
期望：二者正增益，通过。

### T-008　名称变化

重命名 theorem，concept 不变。  
期望：count 与 rate 完全不变。

### T-009　proof 改写

替换 theorem proof，statement 与 primitive bundle 不变。  
期望：count 与 rate 完全不变。

### T-010　索引重排

改变导入／声明顺序。  
期望：按 theorem 对齐后的结果相同。

### T-011　输出双射

把 Bool 输出取反。  
期望：kernel 与 rate 不变。

### T-012　多 arena

两个不同 State 类型。  
期望：分别计算，不产生跨 arena 人工加权总分。

### T-013　系统 theorem 自登记

把 `lowersEscape_iff_uniqueCaptureCount_pos` 的数学 concept 登记进其 arena。  
期望：使用相同 leave-one-out 规则，无命名空间豁免。

### T-014　certificate 回流

尝试把判官保留的报告视图名登记为 theorem unit。
期望：IE-C011。

### T-015　artifact 篡改

修改上次 JSON 后重新编译。  
期望：结果完全不受影响，因为编译不读取 JSON。

### T-016　数学的零历史输入

当前完整目录的联合核、逃逸与留一增益不取历史报告为数学参数。

### T-017　零状态／单状态 arena

有限 SealCatalog 的 nondegenerate 字段要求该 arena 非退化；零状态或单状态 arena 无法提供此数学证明。未封印登记不因此取得额外非退化要求。

### T-018　精确分数

检查：

$$
\text{withoutEscapeCount}
=
\text{fullEscapeCount}
+
\text{uniqueCaptureCount}.
$$

### T-019　结构／计数桥

检查 strict kernel inclusion 与 positive count 等价。

### T-020　全 catalog theorem

检查：

```lean
CatalogIrredundant catalog
```

只有在该目录每个索引的降低逃逸证明成立时，才能证明其全称不可约性。

### T-021　shared fst/snd analysis

`Bool × Bool` 的 maximal catalog 含 `Prod.fst`、`Prod.snd`。期望 unique counts 为
$4,4$，pairwise overlap 为 $4/12$，spectrum 为
$\{0\mapsto0,1\mapsto8,2\mapsto4\}$，catalog verdict 为 irredundant。

### T-022　overcomplete spectrum

同一 catalog 含 `Prod.fst`、`Prod.snd`、`id`。期望三个 unique counts 全为零，
spectrum 为 $\{0\mapsto0,1\mapsto0,2\mapsto8,3\mapsto4\}$；analysis view 取得
完整 redundant 数学结论；canonical Seal 的 rows 携带全部零成员的平凡性与闭包归属证明，两 identity 的同核证据可保存在 collisions 中。
补充 mixed `fst,fst,snd`：unique vector 为 `[0,0,4]`，恰两个 trivial certificates、一个 positive certificate，catalog redundant；错误 polarity/certificate 类型与旧成员集证书均拒绝。
M3 shared IC fixture 按实际完整 manifest 判定：gold 与全部同核 peers 在 level 0 均 trivial；§6.3 open schemas 下仅 strict-refinement 有 unique exclusion，occurrence 均保留 level-0 trivial class，law verdict 另列。

### T-023　nested cumulative chain

对 $K_2\subsetneq K_1\subsetneq K_0$，固定一个**恰含这三个 members、没有额外 peer** 的
analysis view；把三者作为 flat cumulative members 时期望
$U_0=U_1=\varnothing$，$U_2=D_A\cap(K_1\setminus K_2)$；同一 kernels 的 chain view
中相邻 $L_1,L_2$ 均非空。该测试防止 flat exclusive 与 ordered layered 混称。

### T-024　one theorem on multiple canonical arenas

同一 theorem declaration 通过分别命名、kernel-checked 的 realizations 登记到两个不同
canonical arenas。期望两个 `(arena,theoremName)` occurrence keys 与 catalog-qualified
companions 不碰撞，各自 count 只相对于本 arena maximal-catalog peers；若第二次登记到同一
canonical arena，则稳定发 IE-C002。

### T-025　same canonical arena split

同一 root import closure 中解析为同一 canonical arena 的 occurrences 使用不同目录 ID，
期望 IE-C024。仅改变 registration module 或 namespace 不改变这条核对的分组键。

### T-026　import-closure root scope

`LeanInformationAuditRegTests.CompiledSeal` 从实际编译产物加载共享 root，
核对 imported registrations、独立 expected rows、成员数量、顺序及完整单位向量。
重复 occurrence 与 qualified-name 碰撞按 IE-C002／IE-C025 拒绝；
辅助 root 的局部导入闭包不证明仓库全局覆盖。

### T-027　refinement matrix

fixture 同时覆盖 `equal`、`strictly_finer`、`strictly_coarser`、`incomparable`。true cells
携 inclusion proofs，false cells 携 witness pairs；transitivity 与 refinement-implies-zero
均由 kernel 检查。

### T-028　cross-arena address coincidence

kernel address 相同不提供 Equiv、semantic transport、refinement、rate aggregation
或准入证据。`RegistrationRelations.rejectKernelAddressSemanticUse` 是具名辅助检查；
生产报告不输出 coincidence class，也不自动扫描报告流调用该辅助函数。

### T-029　catalog role totals

本数学用例使用 arena `Bool × Bool` 与两个 occurrences：`fst-cut`
读取 `Prod.fst` 且 axis=`cut`，`snd-flow` 读取 `Prod.snd` 且 axis=`flow`。12 个 ordered
off-diagonal pairs 上的 expected matrix rows 固定为：

| occurrence | `1000` | `0100` | `0010` | `0001` | row total |
|---|---:|---:|---:|---:|---:|
| `fst-cut` | 4 | 0 | 0 | 0 | 4 |
| `snd-flow` | 0 | 4 | 0 | 0 | 4 |
| catalog total | 4 | 4 | 0 | 0 | 8 |

数学期望为独有捕获向量 $(4,4)$、独有捕获总量 $8$、$h(1)=8$。按列序
`1000,0100,0010,0001`，具名行差 `fst-cut - snd-flow` 是 unweighted vector
`(4,-4,0,0)`；反向差为 `(-4,4,0,0)`。重排 catalog indices 后，按 occurrence name
对齐的 rows、catalog totals 与这两个 directed deltas 逐项不变。另将 `fst-cut` 的同一
kernel 非 role-preserving 地重标为 `flow` 时，unique count 仍为 4，但 row 从
`(4,0,0,0)` 变为 `(0,4,0,0)`，因此不得冒领 histogram invariance。

### T-030　negative verdict artifact ordering

redundant analysis view 只有在完整 zero set、exact counts 与 negative verdict certificates
经数学证明检查后才形成该分析输入；canonical maximal Seal 对同样数据携带完整目录的编译证明。

### T-031　unified causal hierarchy

第 43.1 节的 `UnifiedBoolSCM := IC.Model ⊕ OI.Model` 有 48 states、2,256 ordered pairs。两个 frozen
witness 经 injection/restriction faithful transport；$K_{cf}\subsetneq K_{int}\subsetneq
K_{obs}$，三个 layered increments 均为正，而 cumulative flat catalog 的 observation 与
intervention members 为零。可选 512-state product 的数学证据与其它有限目录使用同一 SealCatalog 契约。

### T-032　有限目录数学用例

singleton 与 shared catalogs 各自使用完整、明确的成员集合，数学计数与证明绑定
各自目录。当前报告只接受第 30 节的格式；数学用例不要求保留旧格式输出或双读路径。

### T-033　E1 generated lattice

arena 为 `Bool × Bool`，catalog generators 为 `fst`、`snd`、`id`。按 exact relation equality
取商后恰有四个 classes：

| node | canonical representative | escape count |
|---|---|---:|
| $K_\varnothing$ | `[]` | 12 |
| $K_{fst}$ | `[fst]` | 4 |
| $K_{snd}$ | `[snd]` | 4 |
| $K_{full}$ | `[id]`，并 quotient `[fst,snd]` 及所有含 `id` 的同核 subsets | 0 |

$K_{fst}$ 与 $K_{snd}$ 不可比；strict edges 构成 diamond，并含直接
$K_\varnothing\xrightarrow{id}K_{full}$ generator edge。固定 schedules
`fst,snd,id` 与 `id,fst,snd` 的 increments 分别为 $(8,4,0)$ 与 $(12,0,0)$，zero steps 只进入
`collapsed_additions`。leave-one-out
$U_{fst}=U_{snd}=U_{id}=\varnothing$，catalog 发完整 redundant verdict；
$h=(0,0,8,4)$，即 $h(0)=0,h(1)=0,h(2)=8,h(3)=4$。

### T-034　causal measured hierarchy

使用第 43.1 节 literal `CfU`，readout 不因预期计数而改变。48 states、2,256 ordered pairs 上：

| layer | escape count | edge capture |
|---|---:|---:|
| $K_\varnothing$ | 2256 | - |
| $K_{obs}$ | 136 | 2120 |
| $K_{int}$ | 44 | 92 |
| $K_{cf}$ | 0 | 44 |

branch cross-check 固定为：IC branch 在 obs/int/cf 后 escape $80/20/0$，OI branch为
$56/24/0$。证明 $K_{cf}\subsetneq K_{int}\subsetneq K_{obs}$、increments 两两不交且
$2120+92+44=2256$。恰含三个 cumulative readouts 的 flat view 中
$U_{Obs}=U_{Int}=0$、$U_{CF}=44$。

### T-035　structural witness fixture

`StructuralArena.State := Nat`，catalog 与 primitive bundle index 均为 singleton，primitive
kernel 是 parity equality。without kernel 为 universal relation；`left=0,right=1` 给出
without agreement 与 full separation，故 strict inclusion 由 kernel proof接受而不枚举
`Nat`。structural 证书必须包含 inclusion、witness 与两侧义务。

### T-037　extensional quotient mutation

把 E1 的 `[id]` 与 `[fst,snd]` 强制输出为两个 nodes，期望 IE-C039；恢复 quotient 后 node
count 回到 4，且 node address 无法作为 equality proof。

### T-038　generator transition mutation

把 E1 schedule 的 zero step 写成 strict edge、把一步多 theorem addition 写成 edge、或删除
应有 collapsed row，均期望 IE-C040。E1 的 direct
$K_\varnothing\xrightarrow{id}K_{full}$ 必须作为 `is_cover: false` 的 strict shortcut 留在 JSON，
diamond 的四个 distinct cover endpoint pairs 对应六个 labeled cover transition rows，均为
`is_cover: true`；翻转 classification 或让 ASCII 绘 shortcut 也得 IE-C040。

### T-039　bounded projection fixture

构造有未 materialize interior nodes 的 catalog；projection 仍精确包含 top、bottom、全部
leave-one-out、certified-schedule 与 requested nodes，且
`complete_lattice_materialized=false`。`edges` 含全部 certified-schedule strict transitions 与
explicitly requested transitions，但不要求完整 full DAG；每个 edge endpoint 以及
leave-one-out／schedule node reference 都必须解析到 materialized `node_key`。逐种删除 required
transition 得 IE-C040；逐种删除 required node 或指向 omitted endpoint 得 IE-C041；不得因未输出
完整 $2^m$ 而失败。

### T-040　hierarchy certificate mutations

逐一改动 node escape、edge capture、schedule telescope、refinement/overlap cell、spectrum、
redundant set 与 verdict，均在发射前得 IE-C042。

### T-041　JSON／ASCII non-interference

改变 `node_key`、ASCII indentation、layout 或 report-only schedule order，Lean propositions 与
verdict 不变；让任一 admission code path 读取这些字段得 IE-C043。相同输入重跑的 JSON 与
ASCII bytes 相同，且 renderer 只消费 certified `is_cover: true` edges。

---

## 36. 与现有仓库数学内核的合并原则

### 36.1 必须复用

优先复用已有 canonical declarations：

C-IRPT 对齐文档：

```text
docs/develop/theory/CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md
```


```text
Concept
conceptJoin
conceptKernel
jointKernel
SemanticClosure
PrimitiveEscape
ProductiveSeparation
defectRelation
residual_join_law
strict_kernel_novelty_criterion
controlledBehavior
DynClosure
ObserverStructure
```

### 36.2 identity target 特化

本规范的内生逃逸：

$$
E_S
=
\operatorname{defectRelation}(C_S,\operatorname{id}_X)
$$

应作为已有 target residual 理论的特化证明，而不是复制 `defectRelation`。

### 36.3 StrictKernelNoveltyCriterion 特化

对：

$$
\Gamma=I^{-i},
\qquad
\text{candidate}=c_i,
$$

现有严格核准则直接给出：

$$
K_I\subsetneq K_{I^{-i}}
\Longleftrightarrow
c_i\notin\operatorname{SemanticClosure}(I^{-i}).
$$

新模块只需补齐：

- C-IRPT primitive 到 canonical kernel 的适配；
- identity target；
- off-diagonal finite counting；
- leave-one-out；
- exact rate；
- four-role signature partition；
- 编译期契约证据。

对任意 theorem $i$，必须额外证明：

$$
U_i
=
\operatorname{Residual}(K_{-i},K_i),
$$

其中 $K_i$ 是 theorem primitive bundle 的 joint kernel。

### 36.4 Inspector 复用边界

当前 Lean inspector 从编译部件读取声明 kind、类型、常量依赖及公理闭包；
生产读取与 assessment 使用 `RawArtifacts.Store`，不构建 Environment。

数学 rate 与计数结论由库内 Lean 定义和证明承载。
生产报告执行契约结构评定，.NET compactor 编码和校验声明材料；
两者均不替代数学证明。

### 36.5 与工程优化规范 v1 的分工

`trureturing_engineering_optimization_v1.md` §6/§8 的 fused per-pair scan 与证明复用
用于库内数学计算和 Reg 契约证据构造；生产报告只核对编译目录，本文规定数学定义与 admission semantics。
counting modules 必须落在 sibling `D5/S3/ConceptDynamics/InformationEscapeCounting/`，
不采用 nested `InformationEscape/Counting/` 布局。该布局独立于目录占用读数；
`tools/StrataLint.Engine/Coordinates/Gid.cs` 的 `ParseFormalCoordinates` 要求 ordinary formal
coordinates 至少三段，sibling placement 不由文法深度推出。计算结果须有对应的数学证明
（工程规范 §8）；工程规范 §9／§16 的 import-closure seal 义务保持有效。
数学计数不改变 production seal 的完整 registration closure、单位向量或编译期证据义务。

---

## 37. 契约、数学库与实现的交付边界

数学定义与证明归 D5 及对应 Blueprint；Reg 声明实现接口契约类型，模板 enrollment
与共享支持归 `Reg/Support`。登记与目录模块按实际 import 关系组成依赖闭包。

接口升级在同一次交付中迁移全部用法并删除旧表示，不保留旧入口、双读或回退。
实现变化不重编 Reg，不使有效报告失效。报告期只读取编译部件并评定结构；
不得生成另一份证明源码、执行登记代码或调用 Lean elaborator/Meta/内核重新证明。

`CompiledSnapshots` 核对 expected 与 actual；`CompiledSeal` 核对完整登记闭包与
目录身份、arena、成员顺序及单位向量。报告格式与提取语义升级更新格式标识，
严格读取器拒读其它格式并全部重提取。

数学优化或 generated-kernel hierarchy 的新增定理须有实际消费者与准入依据。
计数与层级数学模块放在 GID 合法的 sibling `InformationEscapeCounting/` 与
`InformationEscapeHierarchy/`；它们不为生产报告增加分析输出协议。

## 39. 数学与生产约束

以下区分库内数学性质与生产报告约束。

### AC-001　规范入口

`make lean-report` 通过 cache-writer 和 Lake 依赖编译契约，读取编译部件并发布当前报告。

### AC-002　数学与实现分工

Lean 内核检查数学证明；报告实现只读编译数据并核对结构，外部 JSON 不提供数学证明权威。

### AC-003　数学的零历史输入

本规范的联合核、留一增益与 exact rate 只取同一当前数学目录为参数。

### AC-004　全精确

所有 rate 以 `Nat`／`Rat` 表示。

### AC-005　编译期数学证据

`SealRow.conclusion` 对 exact catalog/index 携带 positive 的降低逃逸证明，或 zero 的
平凡性与剩余目录闭包归属证明。`SealCatalog` 的非退化性、bundle 非空、kernel
碰撞与目录结论由 Reg 编译期内核检查；报告不生成具名伴随证明。

### AC-006　目录结论

`SealCatalog.conclusion` 携带同一单位向量目录的冗余或不可约证明。
指定 root 的全称不可约性是其完整 maximal catalogs 的数学合取；analysis views
不替代其中任一目录，也不要求报告产生新的根级 theorem。

### AC-007　平凡成员与封印

常值、重复、可恢复或 wrapper primitive readout 可具有零独有捕获。
Seal 保留完整 peers 与每个索引的编译证明；合法冗余目录可提供 redundant 结论。
生产判官核对目录身份、舞台与完整单位向量，不另设首次冻结正性准入门。

### AC-008　次序不变

交换 module import 和 theorem 登记顺序不改变结果。

### AC-009　系统自应用

至少一个系统核心 theorem unit 通过同一 registry 和同一 leave-one-out 公式被分析。

### AC-010　artifact 单向

artifact 可删除、可重建、不可回写判词。

### AC-011　Occurrence identity

每个 `(canonical arena declaration,theoremName)` 在 sealing root 的 import closure 中恰登记
一次；同一 theorem 仅可经分别命名、kernel-checked realization 登记到不同 canonical
arena，所有 companions catalog-qualified。

### AC-012　Canonical maximal grouping

designated root import closure 中同一 canonical object `Arena` 的全部 occurrences
使用一个目录 ID，且至少有一个 canonicalMaximal 成员。该闭包不代表仓库全局覆盖。

### AC-013　库内分析证明

exclusive vector、exact gain、overlap/refinement、multiplicity spectrum、role totals 与
layer-chain identities 是库内数学对象；使用时须有对应 Lean 证明，不属于生产报告协议。

### AC-014　完整目录核对

报告从实际 import 闭包重建目录，核对完整成员、顺序、arena 与单位向量。
输入与契约不一致时具名失败，不发布成功报告。

### AC-015　分层捕获的数学边界

`LayerChain` 的 inclusions、increments、partition、strictness、unresolved 与 exact
rates 由数学库证明；flat unique capture 与 ordered layered capture 保持不同定义。

### AC-016　Import-closure membership

Seal 消费所在 root 实际 import 闭包中的全部类型化登记，按 canonical object arena
形成完整目录。RootCatalog 的 expected 与 actual 由 `CompiledSnapshots` 核对，
`CompiledSeal` 核对同一目录身份、arena、顺序与单位向量。辅助 root 的局部闭包
不证明仓库全局覆盖，也不豁免成员或数学义务。

### AC-017　Causal alignment

48-state coproduct 的两条 frozen theorem realizations faithful，三层 factorization 与两处
strict refinement 有 Lean proofs；cumulative flat coarse layers 的零 capture 被接受为
定理结果，而不被误写成全正。

### AC-018　数学计算资源边界

有限计算使用 exact counts 和已证明的公式。数值、运行资源与证明义务分别核对；
具体计算路线遵守既有预算，不把资源阻塞当作数学反例。生产报告不枚举 seal 的状态对。

### AC-019　冻结数学声明与报告格式

冻结 `InformationRoot` 的数学声明与证明不变。共享目录使用对应 root 与 catalog
identities；生产报告采用当前格式，格式升级不保留历史兼容读取。

### AC-020　依赖正确的交付

先有可编译的数学定义与接口契约，再由 Reg 实现契约类型，判官消费编译产物。
接口升级在同一交付迁移全部用法并删除旧表示；实现变化不重编 Reg、不使报告失效。
目录核对与判官定向测试保持现役检查，不以生成额外证明或旧格式读取作前置。

### AC-021　Generated-kernel lattice

库内 hierarchy 按 joint-kernel 的关系外延相等取商，证明 refinement order、内部
lattice operations、strict steps、collapsed additions 和 chain-independent invariants。
这些数学对象不要求生产报告输出 lattice 或统计字段。

### AC-022　Finite／structural universality

有限 State 的数学计数使用精确值；任意 State 的结构结论使用 strict-inclusion proof
与 pair witness。有限截断没有 transfer theorem 时不能冒称无界结论。

### AC-026　增量、确定性与诊断

相同编译输入、utility 输入与报告格式对应有效复用；判官实现字节不参与条件。
缺失输入、未知构造器、目录不一致与预算耗尽保留现役具名诊断。

### AC-027　依赖闭包与交付

Reg 的 import 闭包不含实现包。接口升级原子迁移全部用法；实现变化不重编登记。
验证使用当前实现的定向测试与完整报告；不以旧判官判词逐条相同作验收。

# 第五部　最小数学示例

## 40. Bool 单 CUT theorem

设：

$$
X=\mathrm{Bool},
$$

$$
c_0=\operatorname{id}.
$$

完整族区分 `false` 与 `true`：

$$
E_I=\varnothing.
$$

删除唯一 theorem 后，没有任何观察坐标：

$$
E_{I^{-0}}
=
\{(false,true),(true,false)\}.
$$

故：

$$
|U_0|=2,
$$

$$
\delta_0=1.
$$

增强 theorem 成立。

## 41. Bool 常值 CUT primitive

设：

$$
c_0(x)=false.
$$

完整族与空族具有同一核：

$$
K_I=K_{I^{-0}}=X^2.
$$

故：

$$
|U_0|=0,
$$

完整合法 catalog 成功 seal，零成员认证为 `trivial_in_catalog`，catalog 的 `SealCatalog.conclusion` 携带冗余证明；该零对象不获 positive admission。

## 42. Bool pair 的不可约坐标基

设：

$$
X=\mathrm{Bool}\times\mathrm{Bool},
$$

$$
c_0=\operatorname{fst},
\qquad
c_1=\operatorname{snd}.
$$

完整族联合读出等于 identity，因此：

$$
E_I=\varnothing.
$$

删除 `fst` 后，具有相同 `snd` 的不同 pair 逃逸；删除 `snd` 后同理。因此：

$$
\delta_0>0,
\qquad
\delta_1>0.
$$

该族通过。

## 43. 加入 identity 后的过完备族

再加入：

$$
c_2=\operatorname{id}.
$$

则：

- 删除 `id`，`fst` 与 `snd` 仍联合完全区分；
- 删除 `fst`，`id` 仍完全区分；
- 删除 `snd`，`id` 仍完全区分。

故：

$$
\delta_0=\delta_1=\delta_2=0.
$$

完整过完备族成功 seal，三个成员均认证为 `trivial_in_catalog`，并在 `SealCatalog.conclusion` 携带冗余证明；零对象不获 positive admission，完整 peer membership 保持。

以下是独立的不可约 analysis views，不替代完整 maximal catalog，也不删除其成员或履行 positive admission 义务：

$$
\{\operatorname{id}\}
$$

或：

$$
\{\operatorname{fst},\operatorname{snd}\}.
$$

两者都是合法不可约基，系统不引入审美规则选择其一。

## 43.1 统一 Boolean causal alignment 与三层捕获

精确使用两个 carrier：

```lean
namespace IC
abbrev Model :=
  D5.S3.ConceptDynamics.Interventions.
    InterventionCounterfactualSeparation.DeterministicBoolSCM
abbrev Int :=
  D5.S3.ConceptDynamics.Interventions.
    InterventionCounterfactualSeparation.Int
abbrev CF :=
  D5.S3.ConceptDynamics.Interventions.
    InterventionCounterfactualSeparation.CF
abbrev noEffectModel :=
  D5.S3.ConceptDynamics.Interventions.
    InterventionCounterfactualSeparation.noEffectModel
abbrev flipEffectModel :=
  D5.S3.ConceptDynamics.Interventions.
    InterventionCounterfactualSeparation.flipEffectModel
end IC

namespace OI
abbrev Model :=
  D5.S3.ConceptDynamics.Interventions.
    ObservationInterventionSeparation.DeterministicBoolSCM
abbrev Obs :=
  D5.S3.ConceptDynamics.Interventions.
    ObservationInterventionSeparation.Obs
abbrev Int :=
  D5.S3.ConceptDynamics.Interventions.
    ObservationInterventionSeparation.Int
abbrev xCausesYModel :=
  D5.S3.ConceptDynamics.Interventions.
    ObservationInterventionSeparation.xCausesYModel
abbrev yCausesXModel :=
  D5.S3.ConceptDynamics.Interventions.
    ObservationInterventionSeparation.yCausesXModel
end OI

open D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

abbrev UnifiedBoolSCM := IC.Model ⊕ OI.Model

def unifiedArena : Arena := by
  letI : Fintype IC.Model :=
    D5.S3.ConceptDynamics.InformationEscapeArenas.
      FourthFifthArenas.modelFintype
  letI : DecidableEq IC.Model :=
    D5.S3.ConceptDynamics.InformationEscapeArenas.
      FourthFifthArenas.modelDecidableEq
  exact Arena.ofFintype UnifiedBoolSCM
```

`IC` 有 16 states，`OI` 有 32 states，所以 `UnifiedBoolSCM` 有 48 states、
$48\cdot47=2256$ 个 ordered off-diagonal pairs。它低于第 33 节 direct budget。

以下 aliases 只为显示类型：

```lean
abbrev ICObsTable := Bool → Nat
abbrev ICIntTable := Bool → Bool → Nat
abbrev ICCFTable := Bool → Bool → Bool → Bool
abbrev OIObsTable := Bool → Bool × Bool
abbrev OIIntTable := Bool → Bool → Bool × Bool

abbrev ObsOut := ICObsTable ⊕ OIObsTable
abbrev IntOut := ICIntTable ⊕ (OIObsTable × OIIntTable)
abbrev CfOut := ICCFTable ⊕ OI.Model

inductive UnifiedObservationInterventionReadout
  | observation | intervention
  deriving DecidableEq, Fintype

def unifiedObservationInterventionSignature :
    PrimitiveSignature UnifiedBoolSCM where
  Index := UnifiedObservationInterventionReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .observation => Option OIObsTable
    | .intervention => Option OIIntTable
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def observationInterventionUnifiedRealization :
    PrimitiveRealization unifiedObservationInterventionSignature where
  readout
    | .observation => fun
        | .inl _ => none
        | .inr M => some (OI.Obs M)
    | .intervention => fun
        | .inl _ => none
        | .inr M => some (OI.Int M)
  anchor := fun index => Fin.elim0 index

inductive UnifiedInterventionCounterfactualReadout
  | intervention | counterfactual
  deriving DecidableEq, Fintype

def unifiedInterventionCounterfactualSignature :
    PrimitiveSignature UnifiedBoolSCM where
  Index := UnifiedInterventionCounterfactualReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .intervention => Option ICIntTable
    | .counterfactual => Option ICCFTable
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def interventionCounterfactualUnifiedRealization :
    PrimitiveRealization unifiedInterventionCounterfactualSignature where
  readout
    | .intervention => fun
        | .inl M => some (IC.Int M)
        | .inr _ => none
    | .counterfactual => fun
        | .inl M => some (IC.CF M)
        | .inr _ => none
  anchor := fun index => Fin.elim0 index
```

在 coproduct 上定义累计三层 readout：

```lean
def ObsU : UnifiedBoolSCM → ObsOut
  | .inl M => .inl (IC.Int M false)
  | .inr N => .inr (OI.Obs N)

def IntU : UnifiedBoolSCM → IntOut
  | .inl M => .inl (IC.Int M)
  | .inr N => .inr (OI.Obs N, OI.Int N)

def CfU : UnifiedBoolSCM → CfOut
  | .inl M => .inl (IC.CF M)
  | .inr N => .inr N

def obsFromInt : IntOut → ObsOut
  | .inl table => .inl (table false)
  | .inr (obs, _) => .inr obs

def intFromCf : CfOut → IntOut
  | .inl table => .inl (collapse table)
  | .inr N => .inr (OI.Obs N, OI.Int N)
```

其中 `collapse` 与下述 factorization proof 从
`D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner` open 进入作用域。OI 的
intervention layer 有意携带 observation coordinate，使 intervention 在整个 coproduct
上细化 observation；这不改变 frozen OI witness，因为相同 `OI.Obs` 与不同 `OI.Int`
仍给出不同 pair。

必须证明 factorization：

```lean
theorem obsU_factorization : ObsU = obsFromInt ∘ IntU := by
  funext model
  cases model <;> rfl

theorem intU_factorization : IntU = intFromCf ∘ CfU := by
  funext model
  cases model with
  | inl M =>
      simp [IntU, CfU, intFromCf,
        intervention_eq_collapse_counterfactual M]
  | inr N => rfl
```

故 $K_{cf}\subseteq K_{int}\subseteq K_{obs}$。严格 witness 必须直接注入 frozen
theorems：

- `.inr OI.xCausesYModel` 与 `.inr OI.yCausesXModel` 见证
  $K_{int}\subsetneq K_{obs}$；
- `.inl IC.noEffectModel` 与 `.inl IC.flipEffectModel` 见证
  $K_{cf}\subsetneq K_{int}$。

另取一个 OI branch 上与 `OI.xCausesYModel` 的 `Obs` 不同的显式 model，即可证明
$D_A\setminus K_{obs}$ 非空；该 positivity 不从另外两条 strictness theorem 冒推。

前两条规范 theorem 的完整 signature 同时携 factorization implication 与指定 injected
strictness witness：

```lean
/-- CAUSAL-IE-001. -/
theorem unified_observation_intervention_strict_refinement :
    (∀ M N : UnifiedBoolSCM, IntU M = IntU N → ObsU M = ObsU N) ∧
    (ObsU (.inr OI.xCausesYModel) = ObsU (.inr OI.yCausesXModel) ∧
      IntU (.inr OI.xCausesYModel) ≠ IntU (.inr OI.yCausesXModel)) := by
  ...

/-- CAUSAL-IE-002. -/
theorem unified_intervention_counterfactual_strict_refinement :
    (∀ M N : UnifiedBoolSCM, CfU M = CfU N → IntU M = IntU N) ∧
    (IntU (.inl IC.noEffectModel) = IntU (.inl IC.flipEffectModel) ∧
      CfU (.inl IC.noEffectModel) ≠ CfU (.inl IC.flipEffectModel)) := by
  ...
```

`CAUSAL-IE-003` 在下文显式两成员 catalog 定义之后给出。

由前两条建立 `LayerChain`：

$$
K_{cf}\subsetneq K_{int}\subsetneq K_{obs}.
$$

其 ordered increments 为：

$$
L_{obs}=D_A\setminus K_{obs},
$$

$$
L_{int}=D_A\cap(K_{obs}\setminus K_{int}),
$$

$$
L_{cf}=D_A\cap(K_{int}\setminus K_{cf}).
$$

三者两两不交，分割 $D_A\setminus K_{cf}$；加上
$E_{cf}=D_A\cap K_{cf}$ 后分割 $D_A$。三项在此 construction 上均非空，但 exact
sizes、rates、overlaps 与 histograms 由 engine reflected measurement 给出，不在 spec
预写数值。

若把 `ObsU`、`IntU`、`CfU` 三个累计 kernels 固定为恰含这三者、没有额外 peer 的 flat
analysis-view catalog，则
CIRPT-IE-024 强制：

$$
U_{obs}=U_{int}=\varnothing,
\qquad
U_{cf}=D_A\cap(K_{int}\setminus K_{cf}).
$$

这个 flat cumulative catalog 是预期 redundant 的 analysis view，不是
`CAUSAL-IE-003` 的 theorem catalog，也不因相邻 layered increments 为正而通过准入。

两条 frozen theorem 的 canonical shared catalog 使用两个 branch-local primitive law
presentations，它们的 `toArena` definitionally 是同一个 unified `Arena`：

- observation/intervention law 量化 $M,N:\texttt{OI.Model}$，只在 `.inr M/.inr N` 上比较 branch-local
  `OI.Obs` 与 `OI.Int` readouts；在 IC branch 两个 readouts 都为同一 `none`；
- intervention/counterfactual law 量化 $M,N:\texttt{IC.Model}$，只在 `.inl M/.inl N` 上比较
  branch-local `IC.Int` 与 `IC.CF` readouts；在 OI branch 两个 readouts 都为同一 `none`。

对应 API 形状为：

```lean
def observationInterventionLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := unifiedObservationInterventionSignature
  Law := fun r => ∃ M N : OI.Model,
    r.readout .observation (.inr M) = r.readout .observation (.inr N) ∧
    r.readout .intervention (.inr M) ≠ r.readout .intervention (.inr N)

def interventionCounterfactualLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := unifiedInterventionCounterfactualSignature
  Law := fun r => ∃ M N : IC.Model,
    r.readout .intervention (.inl M) = r.readout .intervention (.inl N) ∧
    r.readout .counterfactual (.inl M) ≠ r.readout .counterfactual (.inl N)

theorem observation_intervention_unified_realization :
    LegacyPrimitiveRealization observationInterventionLawArena
      (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N)
      observationInterventionUnifiedRealization := by
  ...

theorem intervention_counterfactual_unified_realization :
    LegacyPrimitiveRealization interventionCounterfactualLawArena
      (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N)
      interventionCounterfactualUnifiedRealization := by
  ...

def unifiedObservationInterventionUnit : TheoremUnit unifiedArena :=
  LegacyPrimitiveRealization.toTheoremUnit
    observation_intervention_unified_realization
    D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.
      observation_strictly_weaker_than_intervention

def unifiedInterventionCounterfactualUnit : TheoremUnit unifiedArena :=
  LegacyPrimitiveRealization.toTheoremUnit
    intervention_counterfactual_unified_realization
    D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.
      intervention_strictly_weaker_than_counterfactual

inductive UnifiedFrozenTransitionIndex
  | observationIntervention
  | interventionCounterfactual
  deriving DecidableEq, Fintype

def unifiedFrozenTransitionCatalog : Catalog unifiedArena where
  Index := UnifiedFrozenTransitionIndex
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | .observationIntervention => unifiedObservationInterventionUnit
    | .interventionCounterfactual => unifiedInterventionCounterfactualUnit

/-- CAUSAL-IE-003. -/
theorem unified_frozen_transition_catalog_irredundant :
    CatalogIrredundant unifiedFrozenTransitionCatalog := by
  ...
```

每个 `equivalence` 的 forward direction 注入 frozen witness，reverse direction 从 law
witness restriction 回取原 witness；两向都必须使用其 hypothesis 与 injection/restriction
equations。等价证明必须绑定原 statement 与该 realization 的 Law。

`unifiedFrozenTransitionCatalog` 恰有上面两个 occurrences；designated v4.2 root 以
`catalog_id = causal-unified-transitions` 分别登记它们，且不把累计 chain readouts 加入该
catalog。OI frozen witness 在 OI branch 使 IC unit 的 local readouts 同为 `none`；IC frozen witness
在 IC branch 使 OI unit 的 local readouts 同为 `none`。因此两 occurrence 各有独有 pair，
`CAUSAL-IE-003` 证明两成员 maximal theorem catalog irredundant。branch-local theorem
kernel 与累计 `ObsU/IntU/CfU` chain 是两个不同关系，artifact 必须分别命名。

可选 stronger alignment 为：

```lean
abbrev ProductUnifiedBoolSCM := OI.Model × IC.Model
```

它有 512 states、261,632 ordered pairs。有限目录的 SealCatalog 契约携带同一目录上的数学证据，报告核对完整成员与单位向量。
coproduct 与 product 都只是把两个 frozen encodings 放到一个 typed comparison arena 的
alignment device；二者都不声称 OI 与 IC 是同一个 causal ontology。

---

# 第六部　最终规范句

## 44. Positive admission 的数学条件

对当前 root $R$ 的 import closure 与 canonical object arena $A$ 形成的 maximal catalog
$\mathcal T_{R,A}$，每个 occurrence $i$ 的 positive admission 数学条件是：

$$
\boxed{
\varepsilon^R_A(\mathcal T_{R,A})
<
\varepsilon^R_A(\mathcal T_{R,A}\setminus\{i\})
}
$$

这不是历史增量，而是当前 occurrence 在当前 maximal peers 内部的留一反事实。ordered
layered capture 是 chain analysis，不替代该准入判词。

## 45. Positive admission 的数学全称式

本节的 positive admission 是下列全称正性的数学简称。
`SealCatalog.conclusion` 携带目录冗余或不可约的证明；各 `SealRow.conclusion`
分别携带 positive 或 zero 证明，均由 Reg 编译期内核检查。
生产判官核对目录身份、舞台与完整单位向量，不把下列全称正性设为额外准入门。

$$
\boxed{
\forall A\in\operatorname{Arenas}(R_\star),\ \forall i\in I_{R_\star,A},
\quad
\varepsilon^{R_\star}_A(\mathcal T_{R_\star,A})
<
\varepsilon^{R_\star}_A(\mathcal T_{R_\star,A}\setminus\{i\})
}
$$

等价地：

$$
\boxed{
\forall A,\ \forall i\in I_{R_\star,A},
\quad
c_i\notin
\operatorname{SemanticClosure}
(\mathcal T_{R_\star,A}\setminus\{i\})
}
$$

等价地：

$$
\boxed{
\forall A,\ \forall i\in I_{R_\star,A},
\quad
\exists x,y,
\left(\forall j\neq i,\ c_j(x)=c_j(y)\right)
\land
c_i(x)\neq c_i(y)
}
$$

## 46. 实现闭环

```text
D5 数学定义与证明 + Interface 契约类型
        ↓
Reg 类型化登记、RootCatalog 与 Seal
        ↓ Lean 编译期内核检查数学义务
编译部件与实际 import 闭包
        ↓ RawArtifacts / Discovery / Decoder
有界结构评定、expected/actual 与 exact vector 核对
        ↓
当前格式的模块报告、声明材料与登记绑定
```

## 47. 本体结论

该系统不是一个附着在数学之外的评价平台。

level-0 对完整合法 catalog 的每个成员给出 kernel-certified positive 或 trivial 分类；positive 成员的伴随命题为：

> 对 designated root 的每个 canonical maximal catalog 中的 positive theorem occurrence，
> 构造并证明另一个 Lean 数学命题：若从同一个 maximal peer catalog 中删除该
> occurrence，则联合概念核严格变粗，信息逃逸率严格上升。

因此获得 positive admission 的对象为：

$$
\boxed{
\widehat\tau^R_{A,i}
:
P_i
\land
\left[
\varepsilon^R_A(\mathcal T_{R,A})
<
\varepsilon^R_A(\mathcal T_{R,A}\setminus\{i\})
\right]
}
$$

数学定义、定理、逃逸率与 Seal 证明字段由 Lean 4 内核检查；报告结构评定读取这些编译数据。

没有 baseline。

没有人工评分。

没有可调评价体系。

报告实现不取得数学证明权威。

只有每个 canonical arena 内当前 maximal theorem occurrences 自身的不可区分核，以及
删除任一 occurrence 后该核是否严格增大。不同 arena 的 analysis 仍分栏，不存在跨
arena score。

---

## 48. C-IRPT 数学关系

theorem 语义、四原语和逃逸 valuation 使用同一个 kernel-residual 数学定义：

$$
\boxed{
\text{theorem readout 不再是自由字段，而是 theorem primitive bundle 的 joint kernel 实现。}
}
$$

由此得到：

1. CUT、FLOW、ADMIT、ANCHOR 使用同一 kernel engine；
2. theorem unique capture 等于 `Residual(K_without, K_unit)`；
3. 四角色总缺陷是四角色 residual 的并；
4. role overlap 通过 exact four-bit signature 统计；
5. ADMIT 不得通过删除状态改变硬门；
6. proof ANCHOR 不得泄漏进 object kernel；
7. 同 kernel 的 primitive representation 无法改变判词；
8. 等价 arena 的输运无法改变判词；
9. 不等价 arena 不被强行聚合；
10. 闭 theorem 的常值真值不会被冒充为对象信息；
11. 全流程仍在一次 Lean 编译内完成。

---

## 49. Shared-arena 数学与契约边界

occurrence identity 为 `(canonical arena declaration,theoremName)`，在 root import
闭包中唯一。同一 theorem 可经独立、kernel-checked realization 登记到不同 canonical
arenas；同一 root 中同 arena 的全部登记形成完整 maximal catalog。

flat leave-one-out exclusive capture 与 ordered layered capture 是不同量。
嵌套累计 flat catalog 的粗成员可为零，严格 chain 的相邻 increments 可同时非空。
overlap/refinement、multiplicity spectrum、role totals 与 layer-chain identities
由数学库定义与证明。Seal 保存同一 exact catalog 的数学义务；生产报告机械核对
成员、顺序、arena 和单位向量，不发布上述分析量。

kernel 地址一致不证明关系外延相等、transport、rate 或目录结论。不同 canonical
arena 的数学结果不能强行聚合为标量。有效冗余目录可提供 Seal，但不获得对象正性。
该数学正性条件不构成额外生产准入门。

## 50. Generated-kernel hierarchy 的数学边界

每个 maximal canonical catalog 的 joint kernels 按关系外延相等取商，形成 finite
closure lattice。subset、hash 与 display ID 不构成 kernel identity。
refinement order 中 finer 为 smaller，top 为全关系 kernel，bottom 为完整读出 kernel，
meet 为 intersection，join 仅在 generated closure 内取。

strict generator-transition DAG 包含全部严格单生成元步骤，可含 shortcut edges；
Hasse cover graph 是 lattice order 的传递约简。equal-kernel additions 是 stutters，
完整 generator schedule 删去 stutters 后才形成 strict chain。
Hasse diagram 为 path 当且仅当 lattice 为 chain；full strict DAG 可因 shortcuts
仍不是 tree。不可比 kernels 产生 diamond 与多条合法分解。

terminal escape、leave-one-out capture、multiplicity、overlap/refinement 与目录数学
结论不依赖所选 chain。有限 State 的计数为精确数学值；任意 State 的严格性使用
strict-inclusion proof 与 pair witness。有限截断没有 transfer theorem 时不能外推。

这些层级数学结果属于 D5 库。Reg 的 Seal 保留编译期数学证据，报告只核对完整
import 闭包与 exact catalog；不要求 materialize 全部 subsets 或输出层级统计协议。
object-level novelty 与 `proof_shape` 正交；生产准入由现行 StrataLint 规则执行。


数学对象是有限 closure lattice，操作关系是可含 shortcuts 的
full strict generator DAG；只有该 lattice 的 Hasse diagram 在 nested chain 特例才是 path／tree，
full strict DAG 仍不因此成为 tree。
