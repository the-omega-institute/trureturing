# Lean 4 单次编译内生信息逃逸定理系统

## 纯数学理论与工程实现规范

**文档状态：** 规范性草案（Normative Draft）  
**版本：** 4.2 — Single-Compilation / C-IRPT Primitive-Complete / Arena-Invariant / No-Baseline / No-Scoring / Shared-Arena / Layered-Capture / Analysis-v3
**适用对象：** `the-omega-institute/trureturing` 中由 Lean 4 定义、证明、登记和编译的数学定理族  
**核心约束：** 一次 `lake build` 完成 C-IRPT primitive 正规化、定理枚举、联合 kernel 构造、信息逃逸计算、伴随命题证明、失败判定与只读产物发射。

---

# 摘要

本规范定义一个完全位于 Lean 4 内部的数学系统。系统的输入不是论文、自然语言标签、人工评分或历史版本差分，而是同一次编译中已经 elaborated 的 Lean 定理对象及其数学概念读出。

v4.2 把“当前完整定理族”精确化为 sealing root $R$ 与 canonical object
`Arena` declaration $A$ 下的单个最大 catalog：

$$
\mathcal T_{R,A}=\{\tau_o\}_{o\in I_{R,A}}.
$$

这里的成员是登记 occurrence，而不是裸 theorem 名。所有未显式写出上标、下标的
$I,K,E,U,\delta,D_A$ 都是固定同一个 $(R,A)$ 后的简写；不同 arena 之间不存在
默认标量。v4.2 同时给出共享 arena 上的 exclusive-capture vector、overlap、kernel
refinement、multiplicity spectrum、role histogram 与 ordered layered capture。新产物使用
additive schema v3；已落地 schema v2 产物及其十一项 singleton 计数的语义不变。

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

系统最终为每个原定理构造增强定理：

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

指定系统 root $R_\star$ 的整个准入条件只有一个：

$$
\boxed{
\forall A\in\operatorname{Arenas}(R_\star),\
\forall o\in I_{R_\star,A},\quad
\delta^{R_\star}_{A,o}(\mathcal T_{R_\star,A})>0
}
$$

即指定 root 中每个 canonical maximal catalog 都必须是语义不可约的概念族：删除任意
一个 occurrence，信息逃逸率都严格上升。辅助 root 与 analysis view 可以给出局部分析，
但既不能证明系统准入，也不能豁免指定 root 中的零成员。

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

$I_{R,A}$ 中每个元素对应 $R$ 所在模块本地 elaboration 中、显式归属于 $A$ 的一个
被登记 theorem occurrence。同一个 theorem declaration 可以在不同 root 或 catalog 中
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
o=(R,A,C,i,\operatorname{theoremName},\operatorname{unit},\Pi,K,
\operatorname{realization}).
$$

其唯一键为：

$$
(\operatorname{root\_id},\operatorname{catalog\_id},
\operatorname{theoremName}).
$$

该键在一次 root elaboration 中恰出现一次。一个 theorem 若进入多个 catalogs 或 roots，
每个 occurrence 都有独立的 catalog-qualified unit、realization 与 companion names。

对每个 $(R,A)$，定义 $C_{R,A}$ 为包含 $R$ 中所有归属于 $A$ 的 occurrence 的唯一
**canonical maximal catalog**。同 arena 的 sub-catalog 只可声明为 `analysis_view`，不得
替代 $C_{R,A}$，不得用于证明 positivity。用 namespace、另一个 root、wrapper、克隆
arena 或“在别处为正”拆开本应同组的 peers，均不改变这一义务。

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

完整系统不要求当前数学必须已经完备，因此准入不强制 $E_I=\varnothing$。系统只要求每个保留定理具有严格非零边际。

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
=D_A\cap\bigl(K^R_{A,I_{R,A}\setminus\{i\}}\setminus K_{A,i}\bigr),
\qquad
\delta_i=\delta^R_{A,i}=|U^R_{A,i}|/|D_A|.
$$

这里的“完整族”只指 $R$ 所在模块本地 elaboration 的、归属于 $A$ 的所有 theorem
occurrences 所成的 canonical maximal catalog $C_{R,A}$。imported `.olean` 中的登记
不会自动进入该集合；analysis sub-catalog 也不能替代它或用于证明 positivity。

### 5.1 完整族

当前编译完成后，完整被分析定理族是：

$$
I.
$$

这里的完整意味着“本次 root module 导入并登记的全部 theorem units”，不是历史仓库状态。

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
\operatorname{Cap}^R_{A,i}=D_A\setminus K_{A,i}.
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

该矩阵对称，且 $O_{ii}=\operatorname{Cap}_i$。overlap 只描述共同捕获，单独不构成
冗余判词。

定义 kernel refinement：

$$
\operatorname{KernelRefines}_{R,A}(i,j)
:\Longleftrightarrow K_{A,i}\subseteq K_{A,j}.
$$

即 $i$ 至少与 $j$ 一样细。它是 preorder；互相 refinement 等价于 kernel equality。
有向矩阵中的每一 pair 必须 proof-backed 地分类为 `equal`、`strictly_finer`、
`strictly_coarser` 或 `incomparable`。若 peer $j\neq i$ 满足
$\operatorname{KernelRefines}(j,i)$，则 $U^R_{A,i}=\varnothing$。特别地，refinement
成立时 $O_{ij}$ 等于较粗 readout 的 capture set。

所有 rate 都以同一个 $|D_A|$ 为分母并使用 exact rational。非等价 arena 的数值只可
分栏报告，不得求和、平均或排序；经 `CIRPT-IE-022` 证明的 arena transport 才允许声明
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

以及 second-moment identity：

$$
\sum_{i<j}|O^R_{A,ij}|
=
\sum_k\binom{k}{2}h^R_A(k).
$$

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
整个 $D_A$。对 $r>0$：

$$
L_r\neq\varnothing
\Longleftrightarrow
K_r\subsetneq K_{r-1}.
$$

因此“观测 $\subsetneq$ 干预 $\subsetneq$ 反事实各自拥有多少”在本规范中指 ordered
layered counts $(|L_0|,\ldots,|L_\ell|)$，不是把累计 readouts 放进平坦共享 catalog 后的
leave-one-out counts。若平坦 catalog 同时含 $K_j\subsetneq K_i$，则较粗成员 $i$ 的
$U_i$ 为零；对 $K_{cf}\subsetneq K_{int}\subsetneq K_{obs}$，必有
$U_{obs}=U_{int}=\varnothing$，而 $U_{cf}=D_A\cap(K_{int}\setminus K_{cf})$。

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

---

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

### 8.5 系统总准入定理

固定 catalog 的数学条件是：

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

只有这个 universal conjunction 控制系统准入。辅助 root（例如 `CausalHierarchyRoot`）
是有边界的分析：它既不能证明指定 root 全正，也不能为指定 root 中的零 occurrence
提供 exemption。analysis view 可以取得完整的 negative verdict certificate，但不能
discharge positivity。

---

## 9. 平凡与冗余的纯数学定义

本节每个“平凡”“冗余”“可恢复”判词均相对于 occurrence 所在的 $(R,A,C_{R,A})$。
同一个 theorem declaration 在另一个 root 或 catalog 中是另一个 occurrence，必须重新
结算；“在某处为正”不蕴含当前 occurrence 为正。

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

因此以下形式会被自动排除：

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

系统不会替人选择哪一种不可约基；它只拒绝同一编译中同时保留一个过完备族。

更一般地，只要同一 catalog 中存在 $j\neq i$ 且 $K_{A,j}\subseteq K_{A,i}$，较细的
$j$ 已捕获 $i$ 能捕获的全部 pair，故 $U^R_{A,i}=\varnothing$。这包括但不限于同核
重述与 product 包装。

---

## 10. 重复、替代与基选择

以下结论全部是 catalog occurrence-relative；系统不把跨 root、跨 catalog 的 theorem
名称相同或不同当作替代证据。只有同一 canonical arena 内的 kernels，或经
`CIRPT-IE-022` 证明 transport 后的 kernels，才进入语义比较。

### 10.1 重复双方同时为零

若两个定理提供同一个核，留一计算会得到：

$$
\delta_i=0,
\qquad
\delta_j=0.
$$

这是正确结果，而不是系统无法决定“保留谁”。当前族确实不是不可约族。

编译必须失败并报告 collision class。开发者删除任一重复项后重新编译，剩余代表将重新获得正边际。

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

### 12.5 为什么工程硬门使用 pair counting

Shannon entropy 包含对数和实数运算，通常是 `noncomputable` 或需要额外解析证明。pair counting：

- 完全精确；
- 只使用 `Nat` 与 `Rat`；
- 可由 `decide`／`native_decide` 计算；
- 与严格正条件等价；
- 不引入浮点误差。

故工程硬门使用 $|U_i|>0$，熵值作为数学等价投影而非判官。

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

### 13.5 不修改原 API

工程实现不得破坏已有 theorem 名称及使用方式。它应生成伴随 theorem：

```lean
theorem originalName.__escape_enriched :
    OriginalStatement ∧ LowersEscape compiledCatalog originalIndex :=
  ⟨originalName, originalName.__lowers_escape⟩
```

原 theorem 继续保持：

```lean
theorem originalName : OriginalStatement := ...
```

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

编译应失败，直到当前定理族重新成为不可约基。

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
peer grouping；一个 theorem 若有多个 designated occurrences，必须在每个 occurrence
所在的 maximal catalog 中分别为正。

### 15.3 最终编译命令不是数学 theorem

`#seal_information_theory` 是 elaborator command。它执行枚举、构造证明项和发射产物，但不作为被分析 concept 加入 catalog。

其数学正确性由普通 Lean theorem 证明，而这些 soundness theorem 本身可以进入 catalog 接受自应用。

这样避免：

$$
\text{seal theorem 必须为自己生成 seal theorem}
$$

的无穷回归。

### 15.4 生成证书不是新信息 concept

`originalName.__lowers_escape` 与 `originalName.__escape_enriched` 是原 theorem 的证明证书，不被重新登记为新的 theorem primitive unit。否则每次编译会人为制造一层“证明此 theorem 有增益的 theorem”，造成无意义增长。

这不是特殊评价规则，而是输入／证书类型的数学区分：

- theorem unit 是被观察概念；
- certificate 是该 unit 性质的证明项。

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
K_{A,i}\subseteq K_{A,j}
\Longleftrightarrow
\operatorname{Cap}^R_{A,j}\subseteq\operatorname{Cap}^R_{A,i}.
$$

### IE-028　`kernelRefines_implies_zero_uniqueCapture`

若 $i\neq j$ 且 $K_{A,i}\subseteq K_{A,j}$，则：

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

### IE-034　`pairwiseOverlap_spectrum_double_count`

$$
\sum_{i<j}|O^R_{A,ij}|=
\sum_k\binom{k}{2}h^R_A(k).
$$

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

对 $1\le r\le\ell$：

$$
K_r\subsetneq K_{r-1}
\Longleftrightarrow
L_r\neq\varnothing.
$$

### IE-038　`cumulativeChain_coarser_uniqueCapture_zero`

若 flat catalog 中有 $i\neq j$ 且 $K_j\subseteq K_i$，则 $U_i=\varnothing$。因此
strict cumulative chain 不蕴含每个 flat member 的 leave-one-out capture 为正。

### IE-039　`systemWidePositive_iff_all_catalogs`

对显式指定的 system root $R_\star$：

$$
\operatorname{SystemCatalogIrredundant}(R_\star)
\Longleftrightarrow
\forall A\in\operatorname{Arenas}(R_\star),\
\operatorname{CatalogIrredundant}(C_{R_\star,A}).
$$

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

因此无需人为交互权重，系统仍能完整报告：

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
$C_{R,A}$ 的 occurrence index 为 $I_{R,A}$，每个 occurrence 有 kernel $K_{A,i}$。
本节以下省略的 $R,A$ 仅是排版简写，绝不表示跨 arena 的一个 catalog。

完整 catalog kernel：

$$
\boxed{
K^R_{A,I_{R,A}}
=
\bigcap_{i:I_{R,A}}K_{A,i}.
}
$$

留一 kernel：

$$
K^{R,-i}_A
=
\bigcap_{j\in I_{R,A},\ j\ne i}K_{A,j}.
$$

原 SPEC 的绝对 escape 为：

$$
E^R_A
=K^R_{A,I_{R,A}}\setminus\Delta_A.
$$

同一 theorem declaration 在另一个 catalog/root 的登记是另一个 occurrence；其
$K_{-i},U_i,\delta_i$ 必须按那里的 peers 重算。

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
若 $K_{cf}\subsetneq K_{int}\subsetneq K_{obs}$ 同时作为 flat members，则：

$$
U_{obs}=U_{int}=\varnothing,
\qquad
U_{cf}=D_A\cap(K_{int}\setminus K_{cf}).
$$

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

对 $r>0$：

$$
L_r\neq\varnothing
\Longleftrightarrow
K_r\subsetneq K_{r-1}.
$$

chain inclusion、partition 与 strictness 必须由 Lean theorem 证明；具体有限 count 与
exact rational rate 可由同一 kernel 的 reflected equality 认证。缺少 proof 的有序
kernel 列表不是 `LayerChain`。

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

v4.2 允许输出 `kernel_address_coincidence_classes` 作为**纯诊断 digest group**：若两个
occurrences 的 output-only `primitive_kernel_address` 字符串相同，可把它们列在同一
class，并标记 serializer version 与 `diagnostic_only: true`。这个相等只表示当前
serializer 的 ordinal-partition bytes 具有同一 SHA-256 digest；即使外部假设 SHA-256
无碰撞，它也至多是该序列化相同的证据。

kernel address coincidence 绝不证明 carrier `Equiv`、semantic kernel transport、
theorem equivalence、role equality、refinement 或跨 arena rate equality，也不得参与
grouping 与 accept/reject。任何语义比较仍须显式 `Equiv` 与 CIRPT-IE-022 proof。

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

系统可以精确输出 theorem 的 unique information 来自：

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
$H_i(s)-H_j(s)$ 的 exact integer vector，不压成 score。由已落地的
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

一个极长但完全处于其他 theorem 语义闭包中的形式化，其 $\delta_i=0$；它在本系统中失败。

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
    (left right : arena.State) : Bool :=
  Finset.univ.all fun index =>
    decide ((bundle.atom index).kernel.relation left right)
```

必须证明：

```lean
theorem agreesB_eq_true_iff :
  bundle.agreesB left right = true ↔
    bundle.agrees left right
```

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

兼容旧 API 时可以定义：

```lean
def PackedObserver.toPrimitiveAtom
    (axis : PrimitiveAxis)
    (observer : PackedObserver arena) :
    PrimitiveAtom arena :=
  ...
```

但方向只能是：

```text
existing readout → certified primitive kernel
```

不得是：

```text
arbitrary external score → primitive kernel
```

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
    (left right : arena.State) : Bool :=
  Finset.univ.any fun index =>
    decide ((bundle.atom index).axis = axis) &&
      decide (¬(bundle.atom index).kernel.relation left right)

def PrimitiveBundle.roleSignature
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Fin 4 → Bool :=
  fun coordinate =>
    bundle.separatesOnAxis (axisOfOrdinal coordinate) left right
```

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
  ∀ x y, catalog.theoremAgrees finer x y →
    catalog.theoremAgrees coarser x y

def KernelEquivalent (catalog : Catalog arena)
    (left right : catalog.Index) : Prop :=
  catalog.KernelRefines left right ∧ catalog.KernelRefines right left

instance (catalog : Catalog arena) (i j : catalog.Index) :
    Decidable (catalog.KernelRefines i j)

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
    Fin (Fintype.card catalog.Index + 1) → Nat

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
Catalog.catalogRoleHistogram_sum
Catalog.catalogRedundant_iff_not_irredundant
LayerChain.layeredCapture_partition
LayerChain.strictRefinement_iff_layeredCapture_nonempty
```

---

## CIRPT-39　建议模块布局增量

在不复制既有 `Concept`、`jointKernel`、`defectRelation` 和 `blindResidual` 的前提下新增：

```text
D5/S3/ConceptDynamics/CIRPT/InformationEscape/
  PrimitiveAxis.lean
  PrimitiveKernel.lean
  QuotientCutNormalForm.lean
  PrimitiveBundle.lean
  UnifiedResidual.lean
  FourRoleResidual.lean
  FourRoleSignature.lean
  DynamicBehaviorEscape.lean
  TheoremPrimitiveNormalForm.lean
  LeaveOneOutPrimitiveResidual.lean
  CertificateErasure.lean
  CoreTheorems.lean
```

现有：

```text
D5/S3/ConceptDynamics/InformationEscape/
```

继续承载：

- arena；
- finite pair counting；
- exact rational rate；
- catalog leave-one-out；
- theorem augmentation；
- seal command。

两层关系是：

```text
CIRPT primitive semantics
        ↓ kernel normalization
InformationEscape finite engine
```

---

## CIRPT-40　单次 seal 命令新增义务

`#seal_information_theory` 在同一次编译中必须额外检查：

1. 每个 theorem unit 具有非空、typed primitive bundle；
2. bundle 中每个 atom 由合法 primitive constructor 或等价 kernel theorem 建立；
3. 每个 ADMIT primitive 具有可执行 decidability；
4. 每个 ANCHOR primitive 所在 arena 具有 `DecidableEq`；
5. theorem proof／certificate declaration 没有泄漏进 object primitive bundle；
6. bundle kernel reflection theorem 成功；
7. catalog leave-one-out 使用 bundle joint kernel；
8. role signature histogram 总和等于 unique capture count；
9. 最终 accept/reject 仍只由 `uniqueCaptureCount > 0` 决定；
10. JSON 只投影结果，不参与任何证明。
11. 以 canonical object `Arena` declaration 分组，并为每个 $(R,A)$ 构造唯一 maximal catalog；
12. occurrence key `(root_id, catalog_id, theoremName)` 在 root 内恰出现一次；
13. 所有 generated companion names 都由 root/catalog/occurrence identity 限定；
14. overlap、refinement、spectrum、role totals、verdict 与 layer-chain inclusion/count identity 均有 Lean certificate；
15. refinement matrix 的 true cell 有 inclusion proof，false cell 有确定性 witness pair；
16. 在触发 IE-C007 前计算并验证完整 `redundantIndices`，不得 first-zero 短路；
17. canonical maximal catalog 失败时不写 artifact；显式 `analysis_view` 只有在全部 exact negative certificates staged 且 kernel-checked 后才可写 redundant projection；
18. seal 只消费命令所在模块本地 elaborated registrations；imported `.olean` registrations 不进入 root；
19. designated root 的 `SystemCatalogIrredundant` 是其全部 maximal catalogs 的 conjunction；
20. kernel-address coincidence 只进入 diagnostic projection，绝不进入证明、grouping 或 verdict；
21. 超过第 33 节 ordered-pair budget 的 catalog 必须使用 refl lane 提供的 reflected seal，否则 fail closed。

---

## CIRPT-41　新增 artifact 字段

v4.2 新共享分析 artifact 使用 additive schema
`lean-intrinsic-information-escape-v3`。已落地 v2 文件、字段与语义保持有效且不原位升级。
v3 的规范形状为：

```json
{
  "schema": "lean-intrinsic-information-escape-v3",
  "root_id": "D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot",
  "seal_scope": "module-local",
  "system_catalog_irredundant": true,
  "kernel_address_coincidence_classes": [],
  "catalogs": []
}
```

root 与 arena/catalog 字段如下：

| scope | field | normative value |
|---|---|---|
| root | `schema` | new shared artifacts 固定为 `lean-intrinsic-information-escape-v3` |
| root | `root_id` | canonical sealing-root `Name` |
| root | `seal_scope` | 固定为 `module-local` |
| root | `system_catalog_irredundant` | designated root 全部 maximal catalogs 的 universal verdict |
| root | `kernel_address_coincidence_classes` | address、occurrences、serializer 与 `diagnostic_only: true` |
| catalog | `catalog_id` | stable root-scoped identity |
| catalog | `catalog_kind` | `canonical_maximal` 或 `analysis_view`，不得由 namespace 推断 |
| catalog | `object_arena` | grouping 使用的 canonical `Arena` declaration |
| catalog | `catalog_verdict` | `irredundant` 或 `redundant` |
| catalog | `redundant_theorems` | 完整零 unique-capture occurrence names |
| catalog | `verdict_certificate` | catalog-qualified positive 或 negative Lean certificate |
| catalog | `exclusive_capture_total` | $\sum_i|U_i|$ |
| catalog | `pairwise_capture_overlap` | canonical upper triangle 的 exact count/rate rows |
| catalog | `kernel_refinement` | directed cells；proof 或 counterexample reference |
| catalog | `kernel_equivalence_classes` | mutual-refinement classes |
| catalog | `catalog_unique_capture_by_role_signature` | exact role column totals |
| catalog | `capture_multiplicity_spectrum` | decimal $k$ 到 exact count/rate 的映射 |
| catalog | `layer_chains` | ordered kernels、adjacent counts/rates、unresolved 与 certificates |
| occurrence | `catalog_membership` | `root_id` 与 `catalog_id` |
| occurrence | `certificate` | catalog-qualified companion `Name` |
| occurrence | `gain_rate` | 既有 exact per-arena normalization |

每个 theorem 记录可以新增：

```json
{
  "primitive_count": 4,
  "primitive_axes": ["cut", "flow", "admit", "anchor"],
  "unique_capture_count": 12,
  "unique_capture_by_role_signature": {
    "1000": 3,
    "0100": 2,
    "0010": 1,
    "0001": 1,
    "1100": 2,
    "1010": 1,
    "1111": 2
  }
}
```

必须满足：

$$
\sum_{s\ne0000}
\operatorname{count}(s)
=
\operatorname{uniqueCaptureCount}.
$$

不得增加：

```text
role_weight
role_score
importance
preferred_axis
manual_bonus
```

---

## CIRPT-42　新增编译错误

### IE-C013　MissingPrimitiveBundle

公开 theorem unit 没有 typed primitive bundle。

### IE-C014　PrimitiveKernelNotDecidable

有限硬门无法执行 primitive kernel 判定。

### IE-C015　PrimitiveReflectionMismatch

Boolean kernel 与结构 kernel 的 reflection theorem 失败。

### IE-C016　CertificateLeakIntoObjectKernel

proof、seal certificate、declaration name 或 statement hash 被作为 object primitive coordinate。

### IE-C017　AdmitDomainRestrictionAttempt

试图通过把 `Arena.State` 替换成 admitted subtype 来降低同一 catalog 的硬门逃逸率。

### IE-C018　RoleSignaturePartitionMismatch

角色 signature histogram 未精确分割 unique capture pairs。

### IE-C019　PrimitiveRealizationMissing

legacy theorem 与 primitive bundle 之间没有 Lean realization theorem。

### IE-C020　ShadowPrimitiveAPI

新增了与已有 `Concept`、`conceptKernel`、`jointKernel`、`defectRelation` 或 `blindResidual` 平行的第二真源。

### IE-C021　ClosedTruthAsObjectPrimitive

把一个已证明闭命题的常值 `true` readout 登记为对象层 theorem primitive。

### IE-C022　CrossArenaAggregationAttempt

试图在没有 Lean `Equiv` 或显式新测度理论的情况下，把不同 arena 的 escape rates 聚合成一个硬门标量。

### IE-C023　UnprovedArenaTransport

两个 arena 声称只是表示变化，却没有提供 Lean `Equiv` 及 primitive-kernel transport correctness theorem。

### IE-C024　SplitCanonicalArenaCatalog

同一 root 内属于同一 canonical object `Arena` 的 occurrences 被 namespace、wrapper、
cloned arena 或 sub-catalog 拆开，或试图用分析 view 替代 maximal catalog。

### IE-C025　DuplicateCatalogOccurrence

同一 `(root_id, catalog_id, theoremName)` occurrence key 出现不止一次。

### IE-C026　MissingMaximalCatalog

root 有归属于某 canonical arena 的 occurrence，却没有构造包含全部这些 occurrences 的
唯一 `canonical_maximal` catalog。

### IE-C027　UncertifiedKernelRefinement

refinement cell 没有 inclusion proof，或否定 cell 没有可复查的 witness pair。

### IE-C028　AnalysisCertificateMismatch

overlap、spectrum、role total、verdict、redundant set 或 layer count 与其 Lean/reflected
certificate 不一致或不完整。

### IE-C029　UnfaithfulCrossArenaRealization

所谓 legacy realization 没有通过 injection/restriction 方程 faithful 地消费输入 law；
尤其禁止用忽略 hypothesis 的两个既有 existential proofs 拼成空洞 `Iff`。

### IE-C030　KernelAddressUsedAsSemanticEvidence

把 `primitive_kernel_address` 或其 coincidence class 用于 arena grouping、`Equiv`、kernel
transport、refinement、rate equality 或 accept/reject。

### IE-C031　InvalidLayerChain

有序 kernels 缺少相邻 inclusion proof、顺序与证书不一致，或 layered partition/reflected
count 未通过 kernel 检查。

### IE-C032　SizeBudgetRequiresReflectedSeal

catalog 的 ordered-pair workload 超过第 33 节声明预算，却没有 refl lane 的 reflected seal。

### IE-C033　IncompleteRedundantIndexSet

negative diagnostics 在 IE-C007 前没有收集并证明全部 zero unique-capture members，或在
canonical admission failure 后仍写出 artifact。

---

## CIRPT-43　新增测试矩阵

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

同一次 seal 中存在两个不等价 arena；验证分别输出 typed results，且不存在全局加权总分字段。

### T-CIRPT-020　capture spectrum identities

在有限 fixtures 上逐项验证 spectrum partition、$h(0)$、$h(1)$、incidence first moment
与 overlap second moment；修改任一 reflected numeral 必须使 certificate 失败。

### T-CIRPT-021　layer-chain transport

经已证明 arena `Equiv` transport 后，每个 layered count/rate 与 unresolved count/rate
保持；缺少 transport proof 时得到 IE-C023，不以 address coincidence 代替。

---

## CIRPT-44　新增完成条件

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

primitive normalization、kernel computation、companion theorem construction 和 artifact emission 全部在同一次 Lean build 内完成。

### AC-CIRPT-009　Arena transport invariance

经 Lean `Equiv` 输运的 catalogs 产生完全相同的 exact counts、rates 与 pass/fail 判词。

### AC-CIRPT-010　No cross-arena scalar

不等价 arena 的结果保持依赖类型分区，不产生无来源的全局标量。

### AC-CIRPT-011　Closed truth erasure

闭 theorem 的 proof truth 不得成为对象层 primitive；只有显式 object primitive law 可进入 object kernel。

### AC-CIRPT-012　Scoped maximal catalogs

每个 root-local canonical arena 恰有一个 maximal catalog；occurrence identity 与所有
companions 都由 root/catalog 限定，analysis view 不承担 positivity。

### AC-CIRPT-013　Certified shared analysis

exclusive vector、overlap/refinement matrices、multiplicity spectrum、role totals 与
positive/negative verdict 均由一般 theorem 加 reflected equalities kernel-certify。

### AC-CIRPT-014　Layered capture distinctness

`LayerChain` 的 inclusions、partition、strictness 与 exact rates 都被认证；任何输出或
测试都不把 layered increments 称为 cumulative flat unique capture。

### AC-CIRPT-015　Diagnostic address isolation

kernel address coincidence 只以 `diagnostic_only` 输出；没有 theorem 或准入路径消费它。

### AC-CIRPT-016　Complete negative diagnostics

seal 在 IE-C007 前计算全部 zero members。canonical failure 不写 artifact；redundant
analysis view 仅在完整 negative certificates staged 后写 v3 projection。

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

实现一个 Lean-native 系统，使一次：

```bash
lake build D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot
```

完成：

1. 加载全部相关模块；
2. 从 Lean persistent environment registry 枚举 theorem units；
3. 按数学 arena 分组；
4. 构造每个 arena 的当前完整有限 catalog；
5. 对每个 theorem 执行 leave-one-out；
6. 精确计算 `escapeFull`、`escapeWithout`、`uniqueCapture`；
7. 在 Lean 内构造 `LowersEscape` 证明；
8. 为原 theorem 构造增强 conjunction theorem；
9. 若任一 theorem 增益为零，则当前 compilation 失败；
10. 若全部通过，则写出只读 JSON／CSV／DOT 报告。
11. 只枚举 root module 本地 elaborated occurrences，并按 canonical object `Arena` declaration 分组；
12. 为每个 $(R,A)$ 构造唯一 maximal `Catalog`，同时允许不承担准入的 typed analysis views；
13. 证明并投影 overlap/refinement matrices、multiplicity spectrum、role totals 与完整 catalog verdict；
14. 对显式 `LayerChain` 证明相邻 inclusions、ordered increments、partition 与 exact rates；
15. 在 designated root 中组装全部 maximal catalogs 的 `SystemCatalogIrredundant`；
16. 新共享结果写 schema v3，且不改写 frozen v4.1 schema-v2 singleton baseline。

不得：

- 生成 `.lean` 文件后再次调用 Lean；
- 读取上一版报告；
- 调用 C# 决定通过／失败；
- 调用 Python 决定通过／失败；
- 让 JSON 参与 theorem 证明；
- 依赖 Git diff；
- 依赖 PR base；
- 依赖 commit 时间。

---

## 18. 建议模块布局

```text
D5/S3/ConceptDynamics/CIRPT/InformationEscape/
  PrimitiveAxis.lean
  PrimitiveKernel.lean
  QuotientCutNormalForm.lean
  PrimitiveBundle.lean
  UnifiedResidual.lean
  FourRoleResidual.lean
  FourRoleSignature.lean
  DynamicBehaviorEscape.lean
  TheoremPrimitiveNormalForm.lean
  LeaveOneOutPrimitiveResidual.lean
  CertificateErasure.lean
  CoreTheorems.lean

D5/S3/ConceptDynamics/InformationEscape/
  Arena.lean
  TheoremUnit.lean
  JointKernel.lean
  EscapePairs.lean
  EscapeRate.lean
  LeaveOneOut.lean
  SemanticClosure.lean
  EntropyBridge.lean
  AugmentedTheorem.lean
  CoreTheorems.lean

tools/lean-inspector/LeanInformationAudit/
  Registry.lean
  Syntax.lean
  Reify.lean
  PrimitiveNormalizer.lean
  CatalogBuilder.lean
  ProofBuilder.lean
  SealCommand.lean
  Emit.lean
  Main.lean

D5/S3/ConceptDynamics/InformationEscape/SharedInformationRoot.lean
```

`D5/S3/ConceptDynamics/InformationEscape/SharedInformationRoot.lean` 是新的 designated
v4.2 root；它必须在自身模块中显式 re-register 所有 canonical occurrences，并以唯一
终局命令结束：

```lean
#seal_information_theory
```

---

## 19. 核心类型

以下接口是规范级草案。实现可调整字段名字，但不得改变数学含义。

### 19.1 Arena

```lean
universe u v w

namespace D5.S3.ConceptDynamics.InformationEscape

structure Arena where
  State : Type u
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  stateNontrivial : 2 ≤ @Fintype.card State stateFintype
```

在使用 arena 时：

```lean
letI := arena.stateFintype
letI := arena.stateDecidableEq
```

### 19.2 DecidableKernel

```lean
structure DecidableKernel (X : Type u) where
  relation : X → X → Prop
  equivalence : Equivalence relation
  decidableRelation : DecidableRel relation
```

`DecidableKernel` 是统一计算真源：

```text
Setoid X + executable relation
```

所有 CUT、FLOW、ADMIT、ANCHOR primitive 都必须通过证明完备的 constructor 产生该对象。

### 19.3 PrimitiveAxis、PrimitiveAtom 与 PrimitiveBundle

```lean
inductive PrimitiveAxis
  | cut
  | flow
  | admit
  | anchor
  deriving DecidableEq, Repr

structure PrimitiveAtom (arena : Arena) where
  axis : PrimitiveAxis
  kernel : DecidableKernel arena.State

structure PrimitiveBundle (arena : Arena) where
  Index : Type v
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  atom : Index → PrimitiveAtom arena
```

```lean
def PrimitiveBundle.agrees
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Prop :=
  ∀ index, (bundle.atom index).kernel.relation left right
```

必须有可执行 `agreesB` 及其 reflection theorem。

### 19.4 PackedObserver 兼容适配器

已有 readout 可通过 kernel constructor 接入：

```lean
structure PackedObserver (arena : Arena) where
  Output : Type v
  outputDecidableEq : DecidableEq Output
  observe : arena.State → Output

 def PackedObserver.toPrimitiveAtom
    (axis : PrimitiveAxis)
    (observer : PackedObserver arena) : PrimitiveAtom arena :=
  ...
```

`PackedObserver` 不再是核心真源，只是 `Concept`／readout 到 primitive kernel 的适配器。

### 19.5 TheoremUnit

```lean
structure TheoremUnit (arena : Arena) where
  primitives : PrimitiveBundle arena
  Statement : Prop
  proof : Statement
```

`primitives` 是 theorem unit 的数学组成，不是评分元数据。proof declaration 本身不得自动进入 object-level primitive bundle。

### 19.6 原生语义实现约束

对原生 theorem，要求 statement 直接采用 primitive law：

```lean
structure PrimitiveLawArena extends Arena where
  Law : PrimitiveBundle toArena → Prop

structure NativeTheoremUnit (arena : PrimitiveLawArena) where
  primitives : PrimitiveBundle arena.toArena
  proof : arena.Law primitives
```

对 legacy theorem：

```lean
structure LegacyPrimitiveRealization
    (arena : PrimitiveLawArena)
    (statement : Prop)
    (primitives : PrimitiveBundle arena.toArena) where
  equivalence : statement ↔ arena.Law primitives
```

这确保 primitive bundle 与 theorem 的联系仍然是 Lean 数学命题，而非字符串注释。

### 19.7 Catalog

```lean
structure Catalog (arena : Arena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → TheoremUnit arena
```

这里的 `arena` 必须是 canonical object `Arena`。`PrimitiveLawArena` 只负责陈述某个
theorem law；它的 `toArena` 必须 definitionally 等于 occurrence 声明的 object arena，
或先经 CIRPT-IE-022 的显式 transport 归一到它。相同 State carrier 不产生这种身份。

### 19.8 完整索引集

```lean
def Catalog.fullIndexSet
    (catalog : Catalog arena) : Finset catalog.Index := by
  letI := catalog.indexFintype
  exact Finset.univ
```

### 19.9 Catalog occurrence、catalog identity 与 layer chain

```lean
structure CatalogId where
  name : Name
  deriving DecidableEq, Repr

inductive CatalogKind
  | canonicalMaximal
  | analysisView
  deriving DecidableEq, Repr

structure CatalogOccurrence (arena : Arena) where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  objectArenaName : Name
  theoremName : Name
  unitName : Name
  realizationName : Name
  unit : TheoremUnit arena

def maximalCatalog
    (rootId objectArenaName : Name)
    (occurrences : Array (CatalogOccurrence arena)) : Catalog arena :=
  ...

structure LayerChain (arena : Arena) where
  length : Nat
  kernel : Fin (length + 1) → DecidableKernel arena.State
  refines : ∀ r : Fin length,
    (kernel r.succ).relation ≤ (kernel r.castSucc).relation
```

`maximalCatalog` 的输入恰为一个 root 中 `objectArenaName` 相同的全部 occurrences；不得
选择子集。occurrence key `(rootId, catalogId, theoremName)` 唯一。同一 theorem 可在多个
catalogs/roots 中出现，但每次必须有另一个 catalog-qualified unit/realization/certificate。
`LayerChain` 是同 arena 的 analysis object，不自动产生 theorem occurrence。

---

## 20. 核与逃逸 Finset API

### 20.1 对角线外 pair

```lean
def offDiagonalPairs (arena : Arena) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact Finset.univ.filter fun pair => pair.1 ≠ pair.2
```

### 20.2 子族不可区分

```lean
def indistinguishable
    (catalog : Catalog arena)
    (selected : Finset catalog.Index)
    (left right : arena.State) : Prop :=
  ∀ index, index ∈ selected →
    (catalog.theoremAt index).primitives.agrees left right
```

必须提供：

```lean
instance indistinguishableDecidable ... :
    Decidable (indistinguishable catalog selected left right)
```

该实例必须使用：

- `selected` 有限性；
- 每个 primitive kernel 的 `decidableRelation`；
- 每个 bundle 的 `agreesB_eq_true_iff`；
- 不得使用 classical oracle 伪装成可执行计算。

### 20.3 逃逸 pair

```lean
def escapePairs
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) :
    Finset (arena.State × arena.State) :=
  (offDiagonalPairs arena).filter fun pair =>
    indistinguishable catalog selected pair.1 pair.2
```

### 20.4 留一索引集

```lean
def without
    (catalog : Catalog arena)
    (index : catalog.Index) : Finset catalog.Index :=
  (catalog.fullIndexSet).erase index
```

### 20.5 独有捕获 pair

可直接定义：

```lean
def uniqueCapturePairs
    (catalog : Catalog arena)
    (index : catalog.Index) :
    Finset (arena.State × arena.State) :=
  (escapePairs catalog (without catalog index)).filter fun pair =>
    ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2
```

也必须证明它等于差集：

```lean
theorem uniqueCapturePairs_eq_sdiff :
  uniqueCapturePairs catalog index =
    escapePairs catalog (without catalog index) \
      escapePairs catalog catalog.fullIndexSet := by
  ...
```

### 20.6 Capture set 与 exclusive vector

```lean
def Catalog.capturePairs (catalog : Catalog arena)
    (index : catalog.Index) :
    Finset (arena.State × arena.State) :=
  offDiagonalPairs arena \ escapePairs catalog {index}

def Catalog.exclusiveCaptureVector (catalog : Catalog arena) :
    catalog.Index → Nat :=
  fun index => catalog.uniqueCaptureCount index
```

必须证明 `uniqueCapturePairs_eq_capture_sdiff_iUnion`、
`uniqueCapturePairs_pairwise_disjoint` 与
`sum_uniqueCaptureCount_le_capturedCount`。

### 20.7 Pairwise capture overlap

```lean
def Catalog.pairwiseCaptureOverlapPairs (catalog : Catalog arena)
    (left right : catalog.Index) :
    Finset (arena.State × arena.State) :=
  catalog.capturePairs left ∩ catalog.capturePairs right

def Catalog.pairwiseCaptureOverlapCount (catalog : Catalog arena)
    (left right : catalog.Index) : Nat :=
  (catalog.pairwiseCaptureOverlapPairs left right).card
```

必须证明 symmetry、diagonal、bounds 与 refinement 时等于较粗 capture set；artifact 只
写 canonical upper triangle，证明仍覆盖整个 symmetric matrix。

### 20.8 Kernel refinement matrix

```lean
def Catalog.KernelRefines (catalog : Catalog arena)
    (finer coarser : catalog.Index) : Prop :=
  ∀ x y, catalog.theoremAgrees finer x y →
    catalog.theoremAgrees coarser x y

def Catalog.KernelEquivalent (catalog : Catalog arena)
    (left right : catalog.Index) : Prop :=
  catalog.KernelRefines left right ∧ catalog.KernelRefines right left

def Catalog.kernelComparison (catalog : Catalog arena)
    (left right : catalog.Index) : KernelComparison

def Catalog.refinementWitness? (catalog : Catalog arena)
    (finer coarser : catalog.Index) :
    Option (arena.State × arena.State)
```

`kernelComparison` 必须 proof-backed 地穷尽 `equal`、`strictly_finer`、
`strictly_coarser`、`incomparable`。true cell 持有 inclusion proof；false cell 持有满足
$K_i(x,y)\land\neg K_j(x,y)$ 的 deterministic witness。只打印 Boolean 不合格。

### 20.9 Role-histogram matrix

```lean
def Catalog.roleHistogramTotal (catalog : Catalog arena)
    (signature : Fin 4 → Bool) : Nat :=
  ∑ index, catalog.roleHistogram index signature

def Catalog.roleProfileEq (catalog : Catalog arena)
    (left right : catalog.Index) : Prop :=
  ∀ signature, catalog.roleHistogram left signature =
    catalog.roleHistogram right signature

def Catalog.roleHistogramDifference (catalog : Catalog arena)
    (left right : catalog.Index) (signature : Fin 4 → Bool) : Int :=
  catalog.roleHistogram left signature -
    catalog.roleHistogram right signature
```

复用已落地 `roleHistogram` 与 `roleHistogram_sum_eq_uniqueCaptureCount`。必须认证每行、
catalog column total 及 unweighted difference vector；不得生成 role score 或 weight。

### 20.10 Capture-multiplicity spectrum

```lean
def Catalog.captureMultiplicity (catalog : Catalog arena)
    (pair : arena.State × arena.State) : Nat :=
  ((Finset.univ : Finset catalog.Index).filter fun index =>
    pair ∈ catalog.capturePairs index).card

def Catalog.captureSpectrum (catalog : Catalog arena) :
    Fin (Fintype.card catalog.Index + 1) → Nat :=
  ...
```

必须认证 total、$h(0)$、$h(1)$、incidence first moment 与 overlap second moment；这些
identity 是 reflected measurements 的 kernel-checked consistency laws。

---

## 21. 精确逃逸率 API

### 21.1 分母

```lean
def escapeDenominator (arena : Arena) : Nat :=
  (offDiagonalPairs arena).card
```

必须证明：

```lean
theorem escapeDenominator_pos (arena : Arena) :
    0 < escapeDenominator arena := by
  ...
```

### 21.2 分子

```lean
def escapeNumerator
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) : Nat :=
  (escapePairs catalog selected).card
```

### 21.3 精确有理率

```lean
def escapeRate
    (catalog : Catalog arena)
    (selected : Finset catalog.Index) : ℚ :=
  (escapeNumerator catalog selected : ℚ) /
    (escapeDenominator arena : ℚ)
```

不得使用：

- `Float`；
- `Double`；
- 十进制近似作为真源。

### 21.4 独有捕获数

```lean
def uniqueCaptureCount
    (catalog : Catalog arena)
    (index : catalog.Index) : Nat :=
  (uniqueCapturePairs catalog index).card
```

### 21.5 增益率

```lean
def theoremGainRate
    (catalog : Catalog arena)
    (index : catalog.Index) : ℚ :=
  (uniqueCaptureCount catalog index : ℚ) /
    (escapeDenominator arena : ℚ)
```

### 21.6 降低逃逸命题

```lean
def LowersEscape
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  escapeRate catalog catalog.fullIndexSet <
    escapeRate catalog (without catalog index)
```

### 21.7 可执行等价命题

必须证明：

```lean
theorem lowersEscape_iff_uniqueCaptureCount_pos :
    LowersEscape catalog index ↔
      0 < uniqueCaptureCount catalog index := by
  ...
```

这是编译硬门使用的核心 theorem。

### 21.8 共享分析与 layered exact rates

```lean
def Catalog.pairwiseCaptureOverlapRate (catalog : Catalog arena)
    (left right : catalog.Index) : Rat :=
  (catalog.pairwiseCaptureOverlapCount left right : Rat) /
    (escapeDenominator arena : Rat)

def Catalog.roleSignatureRate (catalog : Catalog arena)
    (index : catalog.Index) (signature : Fin 4 → Bool) : Rat :=
  (catalog.roleHistogram index signature : Rat) /
    (escapeDenominator arena : Rat)

def LayerChain.layeredCaptureRate (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Rat :=
  (chain.layeredCaptureCount layer : Rat) /
    (escapeDenominator arena : Rat)

def LayerChain.unresolvedRate (chain : LayerChain arena) : Rat :=
  (chain.unresolvedCount : Rat) / (escapeDenominator arena : Rat)
```

所有分子/分母作为 exact objects 同时输出。一个 catalog 中的 rate 共享 $|D_A|$；不同
且未证明等价的 arenas 不得合成一个 sum/average/ranking。

---

## 22. 结构 API

### 22.1 Set 级联合核

```lean
def jointKernel
    (catalog : Catalog arena)
    (selected : Set catalog.Index) :
    Set (arena.State × arena.State) :=
  {pair | ∀ index, index ∈ selected →
    (catalog.theoremAt index).primitives.agrees pair.1 pair.2}
```

### 22.2 结构降低

```lean
def StructurallyLowersEscape
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  jointKernel catalog Set.univ ⊂
    jointKernel catalog {j | j ≠ index}
```

### 22.3 结构／有限桥

```lean
theorem structurallyLowersEscape_iff_lowersEscape :
    StructurallyLowersEscape catalog index ↔
      LowersEscape catalog index := by
  ...
```

### 22.4 语义闭包

定义 bundle kernel：

```lean
def PrimitiveBundle.toKernel
    (bundle : PrimitiveBundle arena) :
    DecidableKernel arena.State :=
  ...
```

然后定义：

```lean
def semanticClosureWithout
    (catalog : Catalog arena)
    (index : catalog.Index) :
    Set (DecidableKernel arena.State) :=
  {candidate | ∀ left right,
    (∀ j, j ≠ index →
      (catalog.theoremAt j).primitives.agrees left right) →
    candidate.relation left right}
```

必须证明：

```lean
theorem lowersEscape_iff_not_mem_semanticClosureWithout :
    LowersEscape catalog index ↔
      (catalog.theoremAt index).primitives.toKernel ∉
        semanticClosureWithout catalog index := by
  ...
```

并证明它是已有 `SemanticClosure`／`strict_kernel_novelty_criterion` 的 kernel-normalized 特化。

---

## 23. 增强 theorem API

### 23.1 增强陈述

```lean
def AugmentedStatement
    (catalog : Catalog arena)
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧
    LowersEscape catalog index
```

### 23.2 增强证明构造

```lean
def augmentedProof
    (catalog : Catalog arena)
    (index : catalog.Index)
    (gain : LowersEscape catalog index) :
    AugmentedStatement catalog index :=
  ⟨(catalog.theoremAt index).proof, gain⟩
```

### 23.3 catalog 全正命题

```lean
def CatalogIrredundant
    (catalog : Catalog arena) : Prop :=
  ∀ index, LowersEscape catalog index
```

该命题只属于 occurrence 所在 catalog。canonical system admission 只接受 maximal
catalog 的该证明；analysis view 上的同名性质不向 maximal catalog 传递。

### 23.4 可判定实例

```lean
instance catalogIrredundantDecidable
    (catalog : Catalog arena) :
    Decidable (CatalogIrredundant catalog) := by
  ...
```

该实例可基于：

```lean
∀ index, 0 < uniqueCaptureCount catalog index
```

的有限决定过程构造。

### 23.5 完整正／负 verdict

```lean
def Catalog.redundantIndices (catalog : Catalog arena) :
    Finset catalog.Index :=
  Finset.univ.filter fun index => catalog.uniqueCaptureCount index = 0

def CatalogRedundant (catalog : Catalog arena) : Prop :=
  ∃ index, catalog.uniqueCaptureCount index = 0

theorem catalogIrredundant_iff_redundantIndices_eq_empty :
    CatalogIrredundant catalog ↔ catalog.redundantIndices = ∅

theorem catalogRedundant_iff_not_irredundant
    [Nonempty catalog.Index] :
    CatalogRedundant catalog ↔ ¬CatalogIrredundant catalog

structure SystemCatalogSuite where
  RootIndex : Type
  rootFintype : Fintype RootIndex
  ArenaIndex : RootIndex → Type
  arenaFintype : ∀ root, Fintype (ArenaIndex root)
  catalog : ∀ root arena, PackedCatalog

def SystemWidePositive (suite : SystemCatalogSuite) : Prop :=
  ∀ root arena, CatalogIrredundant (suite.catalog root arena).catalog
```

v4.2 的 canonical deployment 使用恰好一个 designated root，故它的 system theorem 是
该 root 内 maximal catalogs 的有限 conjunction。`SystemCatalogSuite` 只给显式 closed
suite 使用，不得把未枚举 auxiliary roots 暗中算作系统。negative verdict 必须含完整
`redundantIndices` 与证明；不能只报告第一个零成员。

---

## 24. theorem 登记语法

### 24.1 新 theorem 原生语法

建议命令：

```lean
information_theorem theoremName
  in PrimitiveLawArenaName
  object_arena CanonicalArenaName
  catalog CatalogId
  primitives primitiveBundleExpression
  : PrimitiveLawArenaName.Law primitiveBundleExpression := by
  proof
```

展开语义：

```lean
theorem theoremName :
    PrimitiveLawArenaName.Law primitiveBundleExpression := by
  proof

private def catalogQualifiedUnitName :
    TheoremUnit CanonicalArenaName :=
  {
    primitives := primitiveBundleExpression
    Statement := ArenaName.Law primitiveBundleExpression
    proof := theoremName
  }
```

并把：

```text
(rootId, CatalogId, theoremName, catalogQualifiedUnitName,
 PrimitiveLawArenaName, CanonicalArenaName, realizationName)
```

登记进 environment extension。`PrimitiveLawArenaName.toArena` 必须 definitionally 等于
`CanonicalArenaName`；否则登记语法还必须引用 CIRPT-IE-022 transport declaration。

### 24.2 legacy theorem 登记

```lean
register_information_theorem existingTheorem
  in PrimitiveLawArenaName
  object_arena CanonicalArenaName
  catalog CatalogId
  primitives primitiveBundleExpression
  realization existingTheoremPrimitiveRealization
```

其中 `realization` 必须是 Lean theorem：

```lean
existingTheoremStatement ↔
  PrimitiveLawArenaName.Law primitiveBundleExpression
```

不得是字符串说明。跨原 arena 的 legacy realization 必须给出 faithful injection/restriction
equations，并在 `equivalence` 两个方向实际消费输入 hypothesis；用两个已知 existential
proof 构造与输入无关的 `Iff` 触发 IE-C029。

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

唯一性按 occurrence，而不是 theorem declaration 全局判断。键：

```text
(root_id, catalog_id, theoremName)
```

在一个 root elaboration 中恰出现一次。每个 occurrence：

- 恰有一个 theorem unit；
- 恰属于一个 explicit catalog 与一个 canonical object arena；
- 恰有一个 kernel-checked primitive bundle；
- 恰有一个 theorem-to-bundle realization path。

同一 theorem declaration 可以在多个 catalogs/roots 中出现，但必须分别命名 unit、
realization 与 companions，并在每个 maximal catalog 中独立结算。相同 occurrence key 的
多重登记必须 IE-C025 fail-closed。允许一个 theorem 的 primitive bundle 内含多个角色
primitive；不允许同一 occurrence 在多个可选 bundle 之间选择。

同 root、同 canonical arena 的全部 occurrences 必须同时进入一个 maximal catalog。
sub-catalog 可额外声明为 `analysis_view`，但不能取代 maximal grouping 或 discharge
positivity；试图通过 namespace/root/catalog/cloned-arena 拆 peers 触发 IE-C024。

---

## 25. Persistent Environment Extension

### 25.1 registry entry

```lean
structure InformationRegistryEntry where
  catalogId : CatalogId
  catalogKind : CatalogKind
  theoremName : Name
  unitName : Name
  lawArenaName : Name
  objectArenaName : Name
  realizationName : Name
```

`rootId` 由执行 `#seal_information_theory` 的当前 module `Name` 给出，不由 entry 自报。
grouping key 只取 `objectArenaName`；`lawArenaName` 是 `PrimitiveLawArena` presentation，
不能充当 object identity。

### 25.2 持久性

registry 可继续使用 Lean environment extension 保存 elaboration state，但 v4.2 bless 的
root 语义是 **module-local registrations**：

- 每个 seal 只消费与该命令在同一 root module 中显式 elaborated 的 entries；
- import 某个已经 sealed 的 `.olean` 对当前 root 贡献零 registrations；
- 要让 frozen theorem 进入新 root，必须在新 root 用 `register_information_theorem` 显式重新登记；
- re-registration 产生新 catalog-qualified occurrence 与 realization reference；
- 无需扫描源文本；
- 无需 Git 文件列表。

不得再声称 imported `.olean` registrations 会自动进入当前 seal。未来若要引入另一种
import contract，必须另立、测试并迁移，本版本不预留双语义。

### 25.3 环境真源

最终 catalog 只由：

```lean
Environment
```

中的已 elaborated declaration 和 registry 构造。

不得从以下内容决定 theorem 集：

- Markdown；
- Blueprint；
- YAML；
- 文件头注释；
- 正则表达式；
- Git diff。

### 25.4 registry 完整性

必须检查：

- theoremName 存在；
- theoremName 的 kind 是 theorem；
- unitName 存在；
- unitName 的类型是期望的 `TheoremUnit arena`；
- unit.proof 的类型与 theoremName 的 type 定义相同或可由 kernel 证明相等；
- lawArenaName 与 objectArenaName 存在且可关闭实例；
- `lawArenaName.toArena` definitionally 等于 object arena，或有显式 transport proof；
- 没有重复 occurrence key；
- 没有重复 unitName。

还必须检查 `catalogKind`、catalog membership、maximal grouping 与所有 catalog-qualified
generated names。一个 theoremName 在不同 occurrence keys 中合法，但 unit/realization/
certificate name 仍不得碰撞。

---

## 26. 单次终局命令

### 26.1 命令形式

```lean
#seal_information_theory
```

可选只读输出路径：

```lean
#seal_information_theory
  output "build/information-theory"
```

路径只控制 artifact 写出位置，不影响任何数学判词。

命令的 root identity 是当前 module `Name`，scope 固定为 module-local。仓库 build manifest
必须 designation 恰好一个 v4.2 canonical system root；该 root 可以仍使用同一个无参数
命令。辅助 roots 也可 seal，但 artifact 明确标为 scoped analysis，不能代替 designated
root 的 `SystemCatalogIrredundant`。

### 26.2 命令执行顺序

命令必须在一次 elaboration 中执行以下步骤：

1. 读取 registry；
2. 校验 entry；
3. 只保留当前 root module 本地显式 registrations；
4. 按 canonical `objectArenaName` 确定性分组；
5. 校验 occurrence keys 与每个 arena 的唯一 maximal catalog；
6. 按 `catalogId`，再按 theorem canonical `Name` encoding 排序；
7. 为每个 maximal catalog 与 declared analysis view 构造有限 index type；
8. 验证 catalog-qualified generated names 无碰撞；
9. 构造完整 `Finset.univ`；
10. 枚举或反射 `offDiagonalPairs`；
11. 计算完整族 `escapePairs`；
12. 对每个 index 计算 `without` 与 `uniqueCapturePairs`；
13. 计算 exclusive vector、overlap/refinement matrices、spectrum 与 role totals；
14. 对每条 registered `LayerChain` 校验 inclusions 并计算 increments/unresolved；
15. 计算完整 `redundantIndices` 与 catalog verdict，不得遇首零即停止；
16. 计算 exact Nat／Rat 数值；
17. 构造所有 reflected equality、matrix/spectrum/layer identity 与 verdict proofs；
18. 为正成员从 `0 < uniqueCaptureCount` 构造 proof；
19. 经 `lowersEscape_iff_uniqueCaptureCount_pos` 得到 `LowersEscape` proof；
20. 添加 catalog-qualified private 或 namespaced companion theorem；
21. 为 designated root 组装全部 maximal catalogs 的 `SystemCatalogIrredundant`；
22. 若任一 maximal member 为零，携完整 structured diagnostics 发出 IE-C007；
23. 全部 theorem proof 加入 environment 后，写出 schema-v3 只读 artifact；
24. 命令成功结束。

原 v4.1 的步骤编号只描述 singleton baseline 实现；v4.2 以上述原子顺序为准。尤其
positive/negative certificates 必须在任何 artifact write 之前完成。

### 26.3 不得启动第二次 Lean

实现不得：

```text
write Generated.lean
lake env lean Generated.lean
```

所有 generated declaration 必须通过当前 elaborator process 的 `addDecl`／等价受支持接口加入当前 environment。

### 26.4 fail-closed

以下任一情形使命令报错并使编译失败：

- arena 无法实例化；
- state cardinal 小于 2；
- primitive bundle 缺失或为空；
- 某个 primitive kernel 无可执行 `DecidableRel`；
- primitive Bool reflection 与结构 kernel 不一致；
- theorem unit 非闭合；
- theorem-to-bundle realization 缺失；
- theorem 语义登记重复；
- proof/certificate identity 泄漏进 object primitive bundle；
- 任一 `uniqueCaptureCount = 0`；
- role-signature partition 与 unique count 不一致；
- proof builder 无法构造 kernel 可接受证明；
- artifact 在数学检查之前被写出；
- registry 与 environment 不一致。
- occurrence key 重复或同 arena maximal catalog 缺失；
- canonical arena 被 namespace/root/catalog/wrapper 拆分；
- refinement、spectrum、role、verdict 或 layer certificate 不完整；
- `redundantIndices` 不是完整零集合；
- kernel address 被用作语义或准入证据；
- 超预算 catalog 没有 refl lane reflected seal。

canonical maximal catalog 失败时不得写任何 artifact。显式 redundant `analysis_view` 只在
其完整 negative verdict certificates 已 staged 并由 kernel 接受后，才可单独输出
diagnostic projection；它不改变 designated admission。

---

## 27. 伴随 theorem 命名规范

对 theorem occurrence，先定义唯一 naming function：

```lean
def catalogQualifiedName
    (rootId : Name) (catalogId : CatalogId)
    (theoremName suffix : Name) : Name :=
  ...
```

同一函数必须生成 unit、primitive realization、catalog、irredundancy、positive、zero、
verdict、analysis 与 enriched companions。不得继续仅向裸 theoremName 附 suffix。

例如 theorem：

```text
D5.S3.Domain.SomeResult.main_theorem
```

在固定 root/catalog occurrence 中生成逻辑上等价于：

```text
catalogQualifiedName rootId catalogId main_theorem `__lowers_escape
catalogQualifiedName rootId catalogId main_theorem `__escape_enriched
```

规范类型：

```lean
theorem main_theorem.__lowers_escape :
    LowersEscape compiledArenaCatalog compiledIndex := by
  ...

 theorem main_theorem.__escape_enriched :
    OriginalStatement ∧
      LowersEscape compiledArenaCatalog compiledIndex :=
  ⟨main_theorem, main_theorem.__lowers_escape⟩
```

生成 declaration 必须：

- `includeInStatement = false` 或等价 internal 标记；
- 不进入 information registry；
- 不参与下一次同编译 catalog 枚举；
- 可由 inspector 输出为 certificate；
- 不被计算为新增数学 theorem unit。
- occurrence certificate 名在不同 catalog/root 中不碰撞；
- artifact 的 `certificate` 与 `catalog_membership` 指向同一 qualified identity。

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

Meta／IO 层只负责：

- 枚举环境；
- 组织表达式；
- 请求 elaboration；
- 输出投影。

---

## 29. 单次编译数据流

```text
Lean source theorem units
          │
          ▼
root-module elaboration + module-local registry occurrences
          │
          ▼
root identity + canonical object-Arena grouping
          │
          ▼
#seal_information_theory
          │
          ├── build every canonical maximal catalog
          ├── retain declared sub-catalogs as analysis views only
          ├── construct leave-one-out families
          ├── compute exact escape pairs
          ├── compute overlap/refinement/spectrum/role/layer analyses
          ├── stage all positive or negative certificates
          ├── add catalog-qualified companion theorems
          ├── assemble designated-root universal verdict
          └── fail canonical admission on the complete zero set
          │
          ▼
Lean kernel accepts final environment
          │
          ▼
read-only JSON / CSV / DOT artifacts
```

没有环节读取旧状态。kernel-address coincidence 在最后的 projection-only 阶段分组；它
没有回边进入 canonical arena grouping、proof construction 或 verdict。

---

## 30. 只读 artifact 规范

### 30.1 JSON 根结构

以下 v2 根结构是已经落地的 singleton baseline，保持有效且不改写：

```json
{
  "schema": "lean-intrinsic-information-escape-v2",
  "catalog_mode": "single-compilation-leave-one-out",
  "arenas": []
}
```

所有 v4.2 shared-arena 新结果另写 additive schema v3：

```json
{
  "schema": "lean-intrinsic-information-escape-v3",
  "root_id": "D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot",
  "seal_scope": "module-local",
  "system_catalog_irredundant": true,
  "kernel_address_coincidence_classes": [],
  "catalogs": []
}
```

### 30.2 arena 记录

```json
{
  "arena": "D5.S3.Example.BoolPairArena",
  "state_card": 4,
  "off_diagonal_pair_count": 12,
  "full_escape_count": 0,
  "full_escape_rate": {
    "numerator": 0,
    "denominator": 12
  },
  "theorems": []
}
```

v3 catalog record 必须另含：

```json
{
  "catalog_id": "causal-unified-transitions",
  "catalog_kind": "canonical_maximal",
  "object_arena": "D5.S3.Example.UnifiedArena",
  "catalog_verdict": "irredundant",
  "redundant_theorems": [],
  "verdict_certificate": "...",
  "exclusive_capture_total": 8,
  "pairwise_capture_overlap": [],
  "kernel_refinement": [],
  "kernel_equivalence_classes": [],
  "catalog_unique_capture_by_role_signature": {},
  "capture_multiplicity_spectrum": {},
  "layer_chains": [],
  "theorems": []
}
```

counts 与 rates 一律同时保存 exact numerator/denominator；refinement cell 一律引用 proof
或 counterexample certificate。`analysis_view` 可有 `redundant` verdict，但不能被根级
`system_catalog_irredundant` 当作 positivity evidence。

### 30.3 theorem 记录

```json
{
  "theorem": "D5.S3.Example.first_coordinate_theorem",
  "catalog_membership": {
    "root_id": "D5.S3.Example.SharedInformationRoot",
    "catalog_id": "bool-pair"
  },
  "unit": "catalog-qualified-unit-name",
  "primitive_count": 1,
  "primitive_axes": ["cut"],
  "primitive_kernel_address": "sha256:...",
  "full_escape_count": 0,
  "without_escape_count": 4,
  "unique_capture_count": 4,
  "unique_capture_by_role_signature": {
    "1000": 4
  },
  "gain_rate": {
    "numerator": 4,
    "denominator": 12
  },
  "lowers_escape": true,
  "certificate": "catalog-qualified-certificate-name"
}
```

### 30.4 禁止字段

artifact 中不得出现：

```text
baseline_commit
parent_snapshot
human_score
importance
manual_weight
approval_override
minimum_threshold
```

### 30.5 artifact 不可回写

下一次编译不得读取该 JSON 作为数学输入。

它可以用于：

- 可视化；
- 文档；
- 趋势观察；
- 人类审阅；

但不能影响准入。

`kernel_address_coincidence_classes` 是唯一允许跨 arena 并列 address strings 的位置，且
每个 class 必须写 `serializer` 与 `diagnostic_only: true`。它不提供 Equiv/transport/rate
证据。artifact 仍是 Lean certificates 的单向 projection；JSON 的完整性不能反过来
证明任何数学命题。

---

## 31. 编译错误规范

建议错误码：

### IE-C001　UnregisteredTheoremUnit

需要审计的 authored theorem 没有 theorem unit。

### IE-C002　DuplicateRegistration

同一 theorem 被登记超过一次。

### IE-C003　ArenaResolutionFailed

arena declaration 无法关闭。

### IE-C004　DegenerateArena

$$
|X|<2.
$$

### IE-C005　PrimitiveKernelUndecidable

primitive kernel 缺少可执行 relation 判定，或其输出 readout 无法产生经过证明的 `DecidableKernel`。

### IE-C006　StatementProofMismatch

theorem unit 中的 proof 与登记 theorem type 不一致。

### IE-C007　ZeroUniqueCapture

$$
|U_i|=0.
$$

错误信息必须同时报告：

- theorem 名；
- arena 名；
- full escape count；
- leave-one-out escape count；
- 同核／闭包候选（若可证明）；
- 不得建议提高人工分数。

### IE-C008　OvercompleteCollisionClass

多个 theorem primitive bundles 具有相同 joint kernel，导致成员共同零边际。

### IE-C009　ProofConstructionFailed

计算结果存在，但无法构造 kernel proof。

### IE-C010　ArtifactPrematureWrite

数学检查完成前尝试发射产物。

### IE-C011　GeneratedCertificateRegistered

伴随 certificate 被错误地重新加入 theorem unit registry。

### IE-C012　ExternalDecisionAttempt

检测到外部程序试图提供 accept/reject 判词。

IE-C013…IE-C023 的名称与含义由 CIRPT-42 保持不变。v4.2 追加：

| code | name | fail-closed condition |
|---|---|---|
| IE-C024 | `SplitCanonicalArenaCatalog` | 同 root、同 canonical arena 被拆分或 analysis view 冒充 maximal |
| IE-C025 | `DuplicateCatalogOccurrence` | occurrence key 重复 |
| IE-C026 | `MissingMaximalCatalog` | 某 arena 没有包含全部 occurrences 的 maximal catalog |
| IE-C027 | `UncertifiedKernelRefinement` | refinement cell 无 proof/counterexample |
| IE-C028 | `AnalysisCertificateMismatch` | matrix/spectrum/role/verdict/layer certificate 不完整或不一致 |
| IE-C029 | `UnfaithfulCrossArenaRealization` | realization 忽略输入 law 或缺 injection/restriction fidelity |
| IE-C030 | `KernelAddressUsedAsSemanticEvidence` | digest 被用于 grouping、transport、rate 或 verdict |
| IE-C031 | `InvalidLayerChain` | chain inclusion、order、partition 或 count certificate 失败 |
| IE-C032 | `SizeBudgetRequiresReflectedSeal` | 超 pair budget catalog 未使用 refl lane seal |
| IE-C033 | `IncompleteRedundantIndexSet` | 未收集全部零成员或 canonical failure 后写 artifact |

---

## 32. 反平凡化硬规则

### R-001　零边际一律失败

```text
uniqueCaptureCount = 0  => compilation error
```

无 owner override。

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

### R-006　过完备族整体失败

若加入一个新 theorem 使旧 theorem 变为零边际，当前完整族失败。系统不得因为旧 theorem 先存在而保留它。

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

## 33. 性能规范

设：

$$
n=|X|,
\qquad
m=|I|.
$$

每个 catalog 声明 ordered-pair workload：

$$
B(C)=|D_A|=n(n-1).
$$

v4.2 的 direct-enumeration budget 固定为：

```lean
def directOrderedPairBudget : Nat := 65536
```

$B(C)\le65536$ 时可使用普通 reduction/枚举 proof。$B(C)>65536$ 不表示数学拒绝，
但必须使用 refl lane 提供的 reflected seal，把 exact measurements 经一般 correctness
theorems送回 kernel；缺少该前置即 IE-C032。预算逐 catalog 判断，不把多个 arenas 的
pairs 相加成全局 scalar。

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

### 33.4 witness 提取

当 `uniqueCaptureCount > 0` 时，实现应确定性提取字典序最小 witness pair：

```text
(left, right)
```

用于报告和 proof term 压缩，但 witness 选择不得影响 count。

### 33.5 内存

禁止为大状态空间同时物化每个 theorem 的完整 $n^2$ pair 集。应优先存储：

- 状态签名；
- fiber sizes；
- 每 theorem 的留一 grouping；
- 至多一个 canonical witness。

---

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

`primitive_kernel_address` 的 serializer/version 也必须固定并写入 artifact。address
coincidence class 的 ordering 可确定化，但 address equality 永不进入数学或身份决定。

---

## 35. 测试矩阵

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

编译失败。

### T-003　两个互补坐标

状态：`Bool × Bool`。  
primitive readout：`Prod.fst`、`Prod.snd`。  
期望：两者均正增益，完整逃逸为零。

### T-004　重复坐标

状态：`Bool × Bool`。  
primitive readout：`Prod.fst` 与 `Bool.not ∘ Prod.fst`。  
两者 kernel 相同。  
期望：两者同时零边际，collision class，编译失败。

### T-005　product 包装过完备

primitive readout：`Prod.fst`、`Prod.snd`、`id`。  
`id` 可恢复两个坐标；两个坐标也可由 `id` 恢复。  
期望：当前三元素族过完备，多成员零边际，编译失败。

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

尝试把 `.__lowers_escape` 登记为 theorem unit。  
期望：IE-C011。

### T-015　artifact 篡改

修改上次 JSON 后重新编译。  
期望：结果完全不受影响，因为编译不读取 JSON。

### T-016　无历史文件

删除全部旧报告。  
期望：当前编译仍完整工作。

### T-017　零状态／单状态 arena

期望：IE-C004。

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

只有在所有 theorem companion proofs 构造成功时成立。

### T-021　shared fst/snd analysis

`Bool × Bool` 的 maximal catalog 含 `Prod.fst`、`Prod.snd`。期望 unique counts 为
$4,4$，pairwise overlap 为 $4/12$，spectrum 为
$\{0\mapsto0,1\mapsto8,2\mapsto4\}$，catalog verdict 为 irredundant。

### T-022　overcomplete spectrum

同一 catalog 含 `Prod.fst`、`Prod.snd`、`id`。期望三个 unique counts 全为零，
spectrum 为 $\{0\mapsto0,1\mapsto0,2\mapsto8,3\mapsto4\}$；analysis view 取得
完整 redundant verdict，canonical admission 在所有零成员收齐后发 IE-C007。

### T-023　nested cumulative chain

对 $K_2\subsetneq K_1\subsetneq K_0$，把三者作为 flat cumulative members 时期望
$U_0=U_1=\varnothing$，$U_2=D_A\cap(K_1\setminus K_2)$；同一 kernels 的 chain view
中相邻 $L_1,L_2$ 均非空。该测试防止 flat exclusive 与 ordered layered 混称。

### T-024　one theorem in multiple catalogs

同一 theorem declaration 在两个 roots/catalogs 中通过分别命名的 realizations 登记。
期望两个 occurrence keys 与 companions 不碰撞，各自 count 只相对于本 catalog peers。

### T-025　same canonical arena split

尝试用 namespace、wrapper、cloned arena 或 singleton analysis views 替代同 root 的一个
maximal same-arena catalog；期望 IE-C024。

### T-026　module-local root scope

import 一个已 sealed root 对当前 seal 贡献零 registrations；在新 root 显式调用
`register_information_theorem` 后 occurrence 才出现。undeclared auxiliary root 不改变
designated system verdict。

### T-027　refinement matrix

fixture 同时覆盖 `equal`、`strictly_finer`、`strictly_coarser`、`incomparable`。true cells
携 inclusion proofs，false cells 携 witness pairs；transitivity 与 refinement-implies-zero
均由 kernel 检查。

### T-028　cross-arena address coincidence

使用已落地 residue/commuting 的相同 kernel address 作为 diagnostic class；期望输出
`diagnostic_only: true`，且无法由此得到 `Equiv`、semantic transport、refinement、rate
aggregation 或 admission evidence。尝试消费该地址得 IE-C030。

### T-029　catalog role totals

每个 role-histogram row 的和等于对应 unique count；catalog columns 的和等于所有
theorem unique counts 与 $h(1)$。reindex 保持结果；任意非 role-preserving 同核 bundle
不冒领 histogram invariance。

### T-030　negative verdict artifact ordering

redundant analysis view 只有在完整 zero set、exact counts 与 negative verdict certificates
staged 且 kernel-checked 后才写 projection。canonical maximal admission 对同样数据发
IE-C007，写文件前失败；first-zero 短路得 IE-C033。

### T-031　unified causal hierarchy

第 43.1 节的 `UnifiedBoolSCM := IC ⊕ OI` 有 48 states、2,256 ordered pairs。两个 frozen
witness 经 injection/restriction faithful transport；$K_{cf}\subsetneq K_{int}\subsetneq
K_{obs}$，三个 layered increments 均为正，而 cumulative flat catalog 的 observation 与
intervention members 为零。可选 512-state product 必须因 261,632 pairs 使用 refl seal。

### T-032　v2 baseline preservation

已落地 `InformationRoot` 的十一项 singleton theorem counts、字段与语义在 schema-v2
compatibility fixture 中 byte-for-byte 保持；schema-v3 shared results 使用不同 root/catalog
identity，不覆盖 v2。

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
- aggregate compiler command。

对任意 theorem $i$，必须额外证明：

$$
U_i
=
\operatorname{Residual}(K_{-i},K_i),
$$

其中 $K_i$ 是 theorem primitive bundle 的 joint kernel。

### 36.4 Inspector 复用边界

当前 Lean inspector 的 environment 枚举、declaration kind、依赖及 axiom closure 代码可以复用。

但：

- 数学 rate 必须由 Lean 定义计算；
- accept/reject 必须由 Lean proof 决定；
- `.NET` compactor 不得参与；
- C# duplicate advisory 不再是研究非平凡性的真源。

---

## 37. 迁移规范

### Phase 1　纯数学核心

新增：

```text
JointKernel
IntrinsicEscape
LeaveOneOut
UniqueCapture
EscapeRate
Irredundancy
```

并证明 IE-001 至 IE-017。

### Phase 2　有限执行层

实现：

```text
offDiagonalPairs
escapePairs
uniqueCapturePairs
uniqueCaptureCount
escapeRate
```

建立 Set／Finset 桥。

### Phase 3　primitive theorem unit

实现：

```text
Arena
DecidableKernel
PrimitiveAxis
PrimitiveAtom
PrimitiveBundle
PackedObserver adapter
TheoremUnit
Catalog
```

加入 CUT／FLOW／ADMIT／ANCHOR 的 Bool 测试模型，并证明所有 constructor reflection theorems。

### Phase 4　registry

实现 persistent environment extension 与：

```lean
information_theorem
register_information_theorem
```

### Phase 5　单次 seal

实现：

```lean
#seal_information_theory
```

禁止任何 generated source second pass。

### Phase 6　伴随 theorem

为每个 theorem 生成：

```text
.__lowers_escape
.__escape_enriched
```

### Phase 7　artifact

仅在全部 proof 被 environment 接受后发射 JSON／CSV／DOT。

### Phase 8　仓库接入

先选一个有限 arena 目录试点；稳定后扩展到更多 concept families。

### Phase 9　v4.1 singleton baseline 到 v4.2 shared catalogs

已落地的
`D5.S3.ConceptDynamics.InformationEscape.InformationRoot` 保持冻结。它在一个模块中显式
登记十个 frozen legacy theorems 与 `engine_census_self_application`，每个 occurrence
独占一个 arena，因此其十一项 `unique_capture_count` 都是 singleton 语义：

$$
K_{-i}=A.\mathrm{State}^2,
\qquad
U_i=D_A\setminus K_i.
$$

这些 schema-v2 数值证明了 realization 与正 capture baseline；它们从未声称共享 peers
之间不可冗余。v4.2 不修改、重标、覆盖或拿它们冒充 peer-relative count。shared results
由一个**新** designated system root 重新登记 occurrences，并另写 schema v3。

dependency-correct landing order 固定为：

1. 本 v4.2 spec PR，仅改本文档；
2. D5 engine analysis modules（deposit）：capture/overlap/refinement/spectrum/layer laws；
3. judge registry/identity mechanics：occurrence keys、canonical arena grouping、qualified names、module-local roots、structured negative diagnostics；
4. unified causal math modules（deposit）：48-state carrier、readouts、factorizations、strict witnesses 与 faithful realizations；
5. 新 designated v4.2 system root（deposit）：显式 re-register 全部 occurrences 并登记 causal chain view；
6. judge schema-v3 analysis projection；
7. fixtures：shared、overcomplete、root-local、address-only、causal 与 v2 compatibility。

第 3 步必须先于任何 shared causal re-registration；纯 causal math 可以先 deposit，但不能
调用尚不存在的 catalog-qualified registry API。refl lane 的 reflected seal 是任何
$B(C)>65536$ catalog 的前置，不满足时该 catalog 不得在上述顺序中提前落地。

---

## 38. 明确删除旧设计

实现与文档中必须删除或弃用以下概念：

```text
AnalysisDomain.target
ResearchProblem
ResearchReceipt as semantic root
parentCatalog
baselineCatalog
CatalogSnapshot as next-run input
previousAccepted
epoch comparison
candidate commit
minimum captured weight
manual triage value
cost-adjusted priority
Shapley allocation
historical delta gate
Stage A generated source
Stage B recompilation
```

允许保留 `Catalog` 一词，但其含义必须是：

> 当前单次编译中完整 theorem unit 有限族。

不得表示历史快照。

---

## 39. 完成定义

工程实现只有同时满足以下条件才算完成。

### AC-001　单命令

一条 `lake build` 完成全部数学检查和报告。

### AC-002　零外部判官

删除 C#／Python accept/reject 路径后，结果不变。

### AC-003　零历史输入

删除旧 JSON、旧 cache、旧 snapshot、Git metadata 后，结果不变。

### AC-004　全精确

所有 rate 以 `Nat`／`Rat` 表示。

### AC-005　kernel proof

每个 accepted theorem 都有：

```lean
original.__lowers_escape
```

以及：

```lean
original.__escape_enriched
```

### AC-006　不可约总 theorem

designated root environment 中对每个 canonical arena $A$ 都存在 catalog-qualified theorem：

```lean
compiledCatalog_irredundant A : CatalogIrredundant (maximalCatalog A)
```

并存在根级：

```lean
systemCatalogIrredundant :
  ∀ A, CatalogIrredundant (maximalCatalog A)
```

它可由所有 catalog companion proofs 组装，也可由一次有限决定直接证明。analysis views
不参与此 conjunction。

### AC-007　零边际失败

插入常值、重复、可恢复或 wrapper primitive readout 时编译必失败。

### AC-008　次序不变

交换 module import 和 theorem 登记顺序不改变结果。

### AC-009　系统自应用

至少一个系统核心 theorem unit 通过同一 registry 和同一 leave-one-out 公式被分析。

### AC-010　artifact 单向

artifact 可删除、可重建、不可回写判词。

### AC-011　Occurrence identity

每个 `(root_id, catalog_id, theoremName)` 恰登记一次；跨 catalog/root 重用 theorem 仅经
分别命名、kernel-checked realization，所有 companions catalog-qualified。

### AC-012　Canonical maximal grouping

designated root 中同一 canonical object `Arena` 的全部 occurrences 进入一个 maximal
catalog；不存在 namespace/root/catalog/cloned-arena/positive-elsewhere exemption。

### AC-013　Certified analysis v3

每个 shared catalog 的 exclusive vector、exact gain vector、overlap/refinement matrices、
multiplicity spectrum、role totals、kernel-equivalence classes 与 verdict 均有 kernel
certificate，并按 schema v3 单向投影。

### AC-014　Complete negative verdict

IE-C007 之前完成全部 zero members 的收集与认证。canonical failure 零 artifact；显式
redundant analysis view 仅在 negative certificate 完整后可写 diagnostic projection。

### AC-015　Layered capture

每条 `LayerChain` 的 inclusions、increments、partition、strictness、unresolved 与 exact
rates 均被认证，且 flat unique capture 与 ordered layered capture 在 API/artifact/test
中保持不同名字。

### AC-016　Module-local designated root

seal 只消费自身模块的 registrations；恰有一个 designated v4.2 system root。辅助 roots
既不证明也不豁免 system-wide positivity。

### AC-017　Causal alignment

48-state coproduct 的两条 frozen theorem realizations faithful，三层 factorization 与两处
strict refinement 有 Lean proofs；cumulative flat coarse layers 的零 capture 被接受为
定理结果，而不被误写成全正。

### AC-018　Size budget reflection

每个 catalog 写出 $B(C)=|D_A|$；超过 65,536 的 catalog 只有在 refl lane reflected seal
存在时才可执行。512-state optional product 因 261,632 ordered pairs 必须走该路径。

### AC-019　v2 immutability

frozen `InformationRoot`、其十一项 singleton counts 与 schema-v2 语义不变；v4.2 结果
使用新 root、catalog identities 与 schema v3。

---

# 第四部　最小 Lean 参考骨架

以下代码是实现骨架，需按仓库实际 universe、namespace 与已存在定义调整。

```lean
universe u v w

namespace D5.S3.ConceptDynamics.InformationEscape

structure Arena where
  State : Type u
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  stateNontrivial : 2 ≤ @Fintype.card State stateFintype

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

structure PrimitiveAtom (arena : Arena) where
  axis : PrimitiveAxis
  kernel : DecidableKernel arena.State

structure PrimitiveBundle (arena : Arena) where
  Index : Type v
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  atom : Index → PrimitiveAtom arena

namespace PrimitiveBundle

variable {arena : Arena}

def agrees (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Prop :=
  ∀ index, (bundle.atom index).kernel.relation left right

def agreesB (bundle : PrimitiveBundle arena)
    (left right : arena.State) : Bool := by
  letI := bundle.indexFintype
  exact Finset.univ.all fun index =>
    @decide ((bundle.atom index).kernel.relation left right)
      ((bundle.atom index).kernel.decidableRelation left right)

theorem agreesB_eq_true_iff
    (bundle : PrimitiveBundle arena)
    (left right : arena.State) :
    bundle.agreesB left right = true ↔
      bundle.agrees left right := by
  -- finite all/reflection proof
  sorry

end PrimitiveBundle

structure TheoremUnit (arena : Arena) where
  primitives : PrimitiveBundle arena
  Statement : Prop
  proof : Statement

structure Catalog (arena : Arena) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index → TheoremUnit arena

namespace Catalog

variable {arena : Arena} (catalog : Catalog arena)

def fullIndexSet : Finset catalog.Index := by
  letI := catalog.indexFintype
  exact Finset.univ

def without (index : catalog.Index) : Finset catalog.Index := by
  letI := catalog.indexDecidableEq
  exact (fullIndexSet catalog).erase index

def offDiagonalPairs : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact Finset.univ.filter fun pair => pair.1 ≠ pair.2

def indistinguishableB
    (selected : Finset catalog.Index)
    (left right : arena.State) : Bool :=
  selected.toList.all fun index =>
    (catalog.theoremAt index).primitives.agreesB left right

def indistinguishable
    (selected : Finset catalog.Index)
    (left right : arena.State) : Prop :=
  ∀ index, index ∈ selected →
    (catalog.theoremAt index).primitives.agrees left right

theorem indistinguishableB_eq_true_iff
    (selected : Finset catalog.Index)
    (left right : arena.State) :
    indistinguishableB catalog selected left right = true ↔
      indistinguishable catalog selected left right := by
  sorry

def escapePairs
    (selected : Finset catalog.Index) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (offDiagonalPairs catalog).filter fun pair =>
    indistinguishableB catalog selected pair.1 pair.2 = true

def uniqueCapturePairs
    (index : catalog.Index) :
    Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (escapePairs catalog (without catalog index)).filter fun pair =>
    (catalog.theoremAt index).primitives.agreesB pair.1 pair.2 = false

def escapeDenominator : Nat :=
  (offDiagonalPairs catalog).card

def escapeNumerator
    (selected : Finset catalog.Index) : Nat :=
  (escapePairs catalog selected).card

def uniqueCaptureCount
    (index : catalog.Index) : Nat :=
  (uniqueCapturePairs catalog index).card

def escapeRate
    (selected : Finset catalog.Index) : ℚ :=
  (escapeNumerator catalog selected : ℚ) /
    (escapeDenominator catalog : ℚ)

def theoremGainRate
    (index : catalog.Index) : ℚ :=
  (uniqueCaptureCount catalog index : ℚ) /
    (escapeDenominator catalog : ℚ)

def LowersEscape
    (index : catalog.Index) : Prop :=
  escapeRate catalog (fullIndexSet catalog) <
    escapeRate catalog (without catalog index)

def AugmentedStatement
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧
    LowersEscape catalog index

def CatalogIrredundant : Prop :=
  ∀ index, LowersEscape catalog index

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
```

生产实现必须证明每个 primitive constructor 的 kernel correctness、`PrimitiveBundle.agreesB` 与结构联合 kernel 的 reflection correctness，以及 `Catalog.indistinguishableB` 与量化版 catalog kernel 的 reflection correctness；Bool 计算结果只有经这些 theorem 传回 Prop 后才能用于最终 kernel certificate。

---

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

编译失败。

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

系统拒绝整个过完备族。

开发者必须选择：

$$
\{\operatorname{id}\}
$$

或：

$$
\{\operatorname{fst},\operatorname{snd}\}.
$$

两者都是合法不可约基，系统不引入审美规则选择其一。

## 43.1 统一 Boolean causal alignment 与三层捕获

精确使用两个已落地 carrier：

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
abbrev CfOut := ICCFTable ⊕ OI
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

规范 theorem 名为：

```text
CAUSAL-IE-001 unified_observation_intervention_strict_refinement
CAUSAL-IE-002 unified_intervention_counterfactual_strict_refinement
CAUSAL-IE-003 unified_frozen_transition_catalog_irredundant
```

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

若把 `ObsU`、`IntU`、`CfU` 三个累计 kernels 当作 flat catalog members，则
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

- observation/intervention law 量化 $M,N:OI$，只在 `.inr M/.inr N` 上比较 branch-local
  `OI.Obs` 与 `OI.Int` readouts；在 IC branch 两个 readouts 都为同一 `none`；
- intervention/counterfactual law 量化 $M,N:IC$，只在 `.inl M/.inl N` 上比较
  branch-local `IC.Int` 与 `IC.CF` readouts；在 OI branch 两个 readouts 都为同一 `none`。

对应 API 形状为：

```lean
def observationInterventionLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := observationInterventionSignature
  Law := fun r => ∃ M N : OI,
    r.readout .observation (.inr M) = r.readout .observation (.inr N) ∧
    r.readout .intervention (.inr M) ≠ r.readout .intervention (.inr N)

def interventionCounterfactualLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := interventionCounterfactualSignature
  Law := fun r => ∃ M N : IC,
    r.readout .intervention (.inl M) = r.readout .intervention (.inl N) ∧
    r.readout .counterfactual (.inl M) ≠ r.readout .counterfactual (.inl N)

theorem observation_intervention_unified_realization :
    LegacyPrimitiveRealization observationInterventionLawArena
      (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N)
      observationInterventionUnifiedRealization

theorem intervention_counterfactual_unified_realization :
    LegacyPrimitiveRealization interventionCounterfactualLawArena
      (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N)
      interventionCounterfactualUnifiedRealization
```

每个 `equivalence` 的 forward direction 注入 frozen witness，reverse direction 从 law
witness restriction 回取原 witness；两向都必须使用其 hypothesis 与 injection/restriction
equations。空洞地引用两条已证明 existential Props 而忽略输入触发 IE-C029。

OI frozen witness 在 OI branch 使 IC unit 的 local readouts 同为 `none`；IC frozen witness
在 IC branch 使 OI unit 的 local readouts 同为 `none`。因此两 occurrence 各有独有 pair，
`CAUSAL-IE-003` 证明两成员 maximal theorem catalog irredundant。branch-local theorem
kernel 与累计 `ObsU/IntU/CfU` chain 是两个不同关系，artifact 必须分别命名。

可选 stronger alignment 为：

```lean
abbrev ProductUnifiedBoolSCM := OI.Model × IC.Model
```

它有 512 states、261,632 ordered pairs，只有第 33 节 refl lane seal 就绪后才 admissible。
coproduct 与 product 都只是把两个 frozen encodings 放到一个 typed comparison arena 的
alignment device；二者都不声称 OI 与 IC 是同一个 causal ontology。

---

# 第六部　最终规范句

## 44. 唯一数学判词

对当前 module-local root $R$ 与 canonical object arena $A$ 形成的 maximal catalog
$\mathcal T_{R,A}$，每个 occurrence $i$ 的数学判词是：

$$
\boxed{
\varepsilon^R_A(\mathcal T_{R,A})
<
\varepsilon^R_A(\mathcal T_{R,A}\setminus\{i\})
}
$$

这不是历史增量，而是当前 occurrence 在当前 maximal peers 内部的留一反事实。ordered
layered capture 是 chain analysis，不替代该准入判词。

## 45. 唯一准入条件

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

## 46. 唯一实现闭环

```text
current root-local Lean theorem occurrences and proofs
        ↓
C-IRPT primitive normalization
        ↓
canonical object-Arena grouping + maximal catalogs
        ↓
leave-one-out primitive kernels
        ↓
exact shared analyses + optional certified LayerChains
        ↓
Lean proofs of strict decrease and analysis identities
        ↓
catalog-qualified companion theorems
        ↓
designated-root universal verdict succeeds or fails
        ↓
read-only schema-v3 artifacts
```

## 47. 本体结论

该系统不是一个附着在数学之外的评价平台。

它只做一件事：

> 对 designated root 的每个 canonical maximal catalog 中的每一个 theorem occurrence，
> 构造并证明另一个 Lean 数学命题：若从同一个 maximal peer catalog 中删除该
> occurrence，则联合概念核严格变粗，信息逃逸率严格上升。

因此接纳对象为：

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

整个系统、系统定理、被分析定理、逃逸率、严格下降证明与最终封印都位于 Lean 4 中。

没有 baseline。

没有人工评分。

没有可调评价体系。

没有外部判官。

只有每个 canonical arena 内当前 maximal theorem occurrences 自身的不可区分核，以及
删除任一 occurrence 后该核是否严格增大。不同 arena 的 analysis 仍分栏，不存在跨
arena score。

---

## 48. v4.1 C-IRPT 合并裁决

本版本相对 v3.0 的决定性变化，是把 theorem 语义、四原语和无任意性的逃逸 valuation 合并为同一个 kernel-residual 闭环：

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

## 49. v4.2 shared-arena 与 analysis 合并裁决

v4.2 不推翻第 48 节；它在 v4.1 kernel-residual 内核上作 additive 扩展，并裁定：

1. 分析成员的身份是 root/catalog-qualified occurrence；同一 occurrence key 恰出现一次；
2. 分组键是 canonical object `Arena` declaration，不是 carrier coincidence、namespace 或 `PrimitiveLawArena`；
3. 同 root、同 arena 的全部 occurrences 构成唯一 maximal catalog，sub-catalog 只作 analysis view；
4. module-local root semantics 是现役真相；imported sealed roots 不自动贡献 registrations；
5. 恰有一个 designated v4.2 system root，其 positivity 是全部 maximal catalogs 的 conjunction；
6. namespace、root、catalog、cloned arena 与 positive-elsewhere 均不构成 exemption；
7. flat leave-one-out exclusive capture 与 ordered layered capture 是两个不同量；
8. nested cumulative flat catalog 的粗成员必为零，严格 chain 的相邻 increments 可同时非空；
9. overlap/refinement matrices、multiplicity spectrum、role totals、verdict 与 layer chain 都由 Lean theorem 加 reflected equality 认证；
10. kernel-address coincidence 仅是 diagnostic digest group，不是 `Equiv`、transport、rate 或 verdict 证据；
11. 48-state `IC ⊕ OI` 是 causal alignment device，保留两个 frozen theorems 的 faithful realizations并证明三层 strict chain；
12. 512-state `OI × IC` 也是 alignment device，仅在 refl lane 满足第 33 节预算后可采用；
13. 两种 carrier 都不声称两个 frozen SCM encodings 是同一个 causal ontology；
14. schema v3 只承载新 shared analysis；v2 artifact 与 frozen `InformationRoot` 的十一项 singleton counts 保持原义。

最终边界是：只有 designated maximal catalog 的 `CatalogIrredundant` 控制 admission；
overlap、rate magnitude、role comparison、spectrum、layered counts 与 address coincidence 都
是无权重 analysis，不增加第二个 threshold，也不产生跨 arena scalar。
