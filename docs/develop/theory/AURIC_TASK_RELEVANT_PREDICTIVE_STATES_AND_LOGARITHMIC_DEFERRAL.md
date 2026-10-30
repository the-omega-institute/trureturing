<a id="auric-predictive-states-deferral"></a>

# AURIC 任务相关预测状态与对数暂缓

> **保存说明（编者）。** 下文完整保留作者提供的九节研究稿、混合编号、证明、公式、三张表及来源链接，仅作 Markdown 数学与标题层级的格式规范化，并在相关位置加入四处明确标示的编者澄清。原稿中的项目更新、来源阅读、历史核对与新颖性表述均归属于作者；纸面推导、条件性复杂度结论与已经构造的算法须按各自前提理解。本次保存不构成新的 Lean 编译、定理认证或全 SAT 预测器构造。

**结合这次项目更新，我认为可以把你的直觉推进到一个更明确的研究命题：观察者不必准确预测每一步，更不必事先知道最优路径；只要它能够以统一多项式成本取得一种结构，使某条正确完成路径上的“尚须分支探索的位置”降到对数个，就已经足以推出 $P=NP$。**

而项目最新进展同时揭示：必须区分**预测状态的存在、预测状态的取得，以及预测状态对当前任务是否足够**。这三个问题可以分别给出定义、定理和反例。

本次核对固定在仓库提交 [`388e1086d5de6323c9dd6913d26e72fd91ddfdb6`](https://github.com/the-omega-institute/trureturing/commit/388e1086d5de6323c9dd6913d26e72fd91ddfdb6)，提交时间为**新加坡时间 2026 年 10 月 30 日 00:06**，相对上次的 `827c052…` 分析新增内容。下面给出纸面数学证明；涉及项目形式化时，我会明确区分源码中的证明与本轮重新编译验证。

<a id="sec-1"></a>

## 一、这次项目更新，真正推进了哪些问题

与我们的主线直接有关的变化主要有四组。

| 新进展 | 对当前研究的意义 |
|---|---|
| [Selection Calculus §27–28](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md) | §27 已接入上次讨论的条件计数、前缀增长和概率预测；§28 新证明：裸五模式加常量与相等关系，不能自动构造 NOR/NAND。 |
| [取得残余理论 §9 的更正](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ADAPTIVE_RESIDUAL.md) | 预测全部实际读出轨迹，并不等于知道隐藏后继状态落在哪个等价类。此前一条双向刻画被六状态反例纠正。 |
| [最小预测核心与取得接口](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md) | 将未来行为的预测商、实际取得，以及允许安全增长的读出条件分别建模。 |
| [存在量词与量子记录 V14](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)、[黄金门 V15](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md) | 固定门、实际记录、相干演化、编码近似普适性和有限精确实现，已经有更细致的数学边界。 |

其中最有价值的进展，是项目开始能够指出：**一个看似自然的“观察者可以这样做”，究竟在哪一步需要补充关系、读出或算法。**

这使我们可以从类比转向可检验的结构理论。

<a id="sec-2"></a>

## 二、先找到一个具体边界：裸五模式已经容易，新增关系使它获得 SAT 表达能力

这里统一使用项目的**代数坐标** $(x,y,z)$。图形印刷中的三个位置是 $(x,z,y)$，两者不能混用。

定义五模式关系

$$
\Sigma
=
\{(x,y,z)\in\{0,1\}^{3}:xz=yz=0\}.
$$

等价地，

$$
\Sigma(x,y,z)
\iff
(\neg x\lor\neg z)\land(\neg y\lor\neg z).
$$

它表达的约束是：中间变量 $z$ 不能和两侧变量同时占据。

<a id="theorem-1"></a>

### 定理 1：裸五模式的封闭性与廉价预测

考虑只由以下成分构成的显式有限网络：

- $\Sigma$ 约束；
- 变量相等关系；
- $0/1$ 钉值；
- 共享变量和有限辅助变量。

则：

1. 所有通过合取与存在量化定义的关系，都对逐坐标 AND 封闭。
2. 网络的可满足性及一个完整满足赋值，可以在统一多项式时间内求出。
3. 在全部完整满足赋值的均匀分布下，下一位的条件概率存在一个统一多项式时间的估计器，误差至多 $1/4$。

第一项对应项目新增的 §28；第三项是本次在其基础上进一步得到的推论。

<a id="theorem-1-proof-1"></a>

#### 证明第一项：辅助变量不能破坏已有封闭性

若 $u,v\in\Sigma$，那么 $u\land v$ 不会新增同时占据的禁用位置，因此

$$
u\land v\in\Sigma.
$$

相等关系、常量 $0$、常量 $1$ 也都保持这一性质。

现在假设某个新关系由

$$
R(x)\iff \exists a\;\bigwedge_j R_j(x,a)
$$

定义。若 $x,x'$ 分别有辅助见证 $a,a'$，那么逐坐标取 AND：

$$
(x,a)\land(x',a')
$$

仍满足每一个原子约束。因此 $a\land a'$ 是 $x\land x'$ 的见证。

所以无论加入多少这种辅助变量，都无法越过该封闭性。证毕。

<a id="theorem-1-proof-2"></a>

#### 证明第二项：直接构造一个解

先合并相等变量。

剩余约束全部是：

$$
\neg u\lor\neg v,
$$

以及常量钉值。

若一个相等分量同时被钉为 $0$ 和 $1$，或者某个禁止同时为一的变量对都被钉为一，就无解。否则，把所有没有被钉为一的分量置零，便得到一个合法完整赋值。

解析、合并、检查和输出都只需要多项式成本。证毕。

<a id="theorem-1-proof-3"></a>

#### 证明第三项：不计数也能预测到足够精度

令 $p$ 是一个仍可延拓的前缀，并记

$$
Z(p)=\#\{\text{与 }p\text{ 相容的完整满足赋值}\}.
$$

下一变量为 $x$，定义

$$
q_0(p)=\frac{Z(p0)}{Z(p)}.
$$

先将相等关系合并。设 $x$ 所属的整个相等分量为 $C$。

若 $C$ 已被赋值为零或一，则 $q_0$ 分别为一或零。

否则，对任意一个 $C=1$ 的完整解，把**整个分量 $C$** 改成零，其他变量保持原值。因为剩余约束只禁止某些变量同时为一，这个修改仍然合法。

而且该映射是单射。因此

$$
Z(p1)\le Z(p0),
$$

从而

$$
\frac12\le q_0(p)\le1.
$$

于是取

$$
\widehat q_0(p)=
\begin{cases}
1,&C\text{ 已定为 }0,\\
0,&C\text{ 已定为 }1,\\
3/4,&C\text{ 尚未赋值},
\end{cases}
$$

就有

$$
\boxed{
|\widehat q_0(p)-q_0(p)|\le\frac14.
}
$$

这个程序没有计算 $Z(p0)$ 或 $Z(p1)$。对不可延拓前缀，它可以任意输出，但仍在同一多项式时间界内停止。证毕。

<a id="sec-2-significance"></a>

#### 这个结果为什么重要

我们上次得到的目标是：对一般 SAT，如果能以统一多项式成本预测下一位的条件概率，并保证固定误差小于 $1/2$，就能推出 $P=NP$。

现在有了一个具体正例：

> **在裸五模式这一子类中，足以支持合法增长的粗概率预测，确实可以通过结构取得，无须完整计数。**

但它只覆盖这类网络。下一步要分析的，正是哪些新增关系会破坏这种性质。

<a id="theorem-2"></a>

### 定理 2：删除空模式后，关系成为 NOR

定义

$$
N=\Sigma\setminus\{000\}.
$$

则

$$
N(x,y,z)
\iff
xz=yz=0
\quad\text{且}\quad
x\lor y\lor z=1.
$$

这恰好等价于

$$
\boxed{z=\neg(x\lor y).}
$$

<a id="theorem-2-proof"></a>

#### 证明

若 $z=1$，前两个约束迫使 $x=y=0$。

若 $z=0$，非空条件迫使 $x\lor y=1$。

这正是 NOR 的真值关系。证毕。

由 NOR 可构造

$$
\neg x=\operatorname{NOR}(x,x),
$$

$$
x\lor y
=
\operatorname{NOR}
\bigl(\operatorname{NOR}(x,y),\operatorname{NOR}(x,y)\bigr),
$$

以及 AND，因此任意布尔验证电路都可用多项式规模的 NOR 电路表示。

把输入留作未知变量、输出钉为一，就得到：

$$
\exists x\; C(x)=1.
$$

这一问题属于 NP，并可编码一般 SAT，所以是 NP 完全的。

这里有一个非常具体的“删东西后的边界”：

$$
\boxed{
\text{裸五模式}
\quad\longrightarrow\quad
\text{加入非空要求}
\quad\longrightarrow\quad
\text{NOR 电路的存在性求解}.
}
$$

其中变化的是**关系的表达能力和封闭性**。这还没有证明 $P\ne NP$，但准确指出了此前廉价预测证明失效的位置。

还要保留一个重要操作条件：项目 §28 证明，非空关系不能由裸 $\Sigma$、钉值和相等关系通过上述合取与存在量化免费构造出来。它是一个新增供应。[来源：Selection Calculus §28](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md)

这对辅助线研究给出了一个更精确的问题：

> 哪些辅助结构保留了容易处理的封闭性？哪些辅助结构破坏它？破坏之后，能否取得新的表示，使任务重新出现可利用的封闭性？

<a id="sec-3"></a>

## 三、观察者必须预测什么：实际未来记录，而非默认知道隐藏后继

项目新增的六状态反例非常值得重视。

其核心可以这样表述：

- 从 $s$ 出发，先输出 $0$，再以各 $1/2$ 的概率进入 $u,v$；
- 从 $t$ 出发，先输出 $0$，然后确定进入 $w$；
- $u$ 下一次确定输出 $0$；
- $v$ 下一次确定输出 $1$；
- $w$ 下一次以各 $1/2$ 的概率输出 $0,1$；
- 此后全部进入永远输出 $0$ 的状态。

因此，从 $s,t$ 出发都以各 $1/2$ 的概率产生

$$
0000\cdots,\qquad0100\cdots.
$$

**全部实际输出轨迹的概率律一致。**

但是隐藏后继的结构不同：

$$
s\to \tfrac12 u+\tfrac12 v,
\qquad
t\to w.
$$

观察者看见第一个 $0$，无法据此判断实际进入了 $u,v,w$ 中的哪一个。甚至知道全部未来输出概率，也不能唯一恢复隐藏混合的分解。

项目因此撤回了“实际轨迹同律就等于递归隐藏后继类相同”的一般断言。这个反例有对应的 [Lean 源文件](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.lean)，包含 `counterkernel_facts` 与 `result : ¬ claim` 的证明体；本次读取了相关声明，没有重建该工程。

所以，“内生观察者用自身结构预测自身增长”可以采用如下严格版本：

> 观察者保存一个由实际历史确定的预测状态。这个状态给出允许实验的未来结果分布，并在新结果实际出现后更新自己。

这种状态表示已有成熟的 PSR——预测状态表示——与可观察算子模型背景。我们可以利用它们，修复项目刚刚发现的问题，而不必预设一个对所有世界、任务和读口都通用的观察者表示。[proceedings.neurips.cc](https://proceedings.neurips.cc/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf?utm_source=chatgpt.com)

<a id="definition-1"></a>

### 定义 1：任务与操作菜单相对的预测空间

设有限模型有 $d$ 个隐藏状态，允许动作 $a$，实际读出 $y$。用非负矩阵表示一步过程：

$$
M_{a,y}\in\mathbb R_{\ge0}^{d\times d},
\qquad
\sum_yM_{a,y}\mathbf1=\mathbf1.
$$

失败、拒绝等结果也计入实际读出。

对有限动作—读出序列

$$
w=(a_1,y_1)\cdots(a_k,y_k)
$$

定义

$$
M_w=M_{a_1,y_1}\cdots M_{a_k,y_k}.
$$

若当前状态分布为行向量 $\mu$，该实验序列的概率是

$$
P_\mu(w)=\mu M_w\mathbf1.
$$

定义未来测试空间

$$
V=\operatorname{span}\{M_w\mathbf1:w\text{ 有限}\}.
$$

取一组由测试向量组成的基

$$
B=[\,\mathbf1,v_2,\ldots,v_r\,],
\qquad r=\dim V\le d,
$$

并令观察者的预测状态为

$$
z=\mu B.
$$

<a id="theorem-3"></a>

### 定理 3：预测状态可以用自身递归更新

对每个动作与读出 $(a,y)$，存在唯一矩阵 $C_{a,y}$，满足

$$
M_{a,y}B=BC_{a,y}.
$$

当实际结果的概率为正时，

$$
\boxed{
P(y\mid a,z)=zC_{a,y}e_1,
}
$$

$$
\boxed{
z'
=
\frac{zC_{a,y}}
     {zC_{a,y}e_1}.
}
$$

并且

$$
\boxed{
\mu B=\nu B
\iff
P_\mu(w)=P_\nu(w)
\quad\text{对全部有限测试 }w.
}
$$

<a id="theorem-3-proof"></a>

#### 证明

给一个测试前面增加动作与读出 $(a,y)$，仍然得到一个允许的测试。因此

$$
M_{a,y}V\subseteq V.
$$

这给出坐标矩阵 $C_{a,y}$。

实际读出发生后的状态分布满足

$$
\mu'
=
\frac{\mu M_{a,y}}
     {\mu M_{a,y}\mathbf1}.
$$

右乘 $B$，利用 $M_{a,y}B=BC_{a,y}$，得到更新公式。

若 $\mu B=\nu B$，每个测试向量又都是 $B$ 的线性组合，因此全部测试概率相同。反过来，基的每一列本身就是测试向量，所以全部测试概率相同必然意味着 $\mu B=\nu B$。

对于自适应实验，一条具体读出路径确定了该路径实际选择的动作串；上述等式逐条保持路径概率，因此也保持完整自适应档案的分布。证毕。

这里更新的是**实际历史条件下的未来预测**。它不要求知道真实隐藏后继属于哪个类，因此避开了六状态反例中的错误。

这也给“时间是观察者结构的增长”一个精确表达：

$$
z_t
\xrightarrow[\text{实际读出 }y_t]{\text{由当前结构选择动作 }a_t}
z_{t+1}.
$$

同一个 $z_t$ 既参与预测下一次读出，也参与构造读出之后的 $z_{t+1}$。但随机结果的分布可预测，不意味着结果值必然可以事前确定。

<a id="sec-4"></a>

## 四、一个关键反例：预测状态只有二维，仍可能把 SAT 藏在初始化中

定理 3 给出了闭合更新，但还没有解决“如何取得这个状态”。

先给一个任务充分性的精确判据。

<a id="proposition-3-1"></a>

### 命题 3.1：预测充分性与任务充分性

令目标为

$$
\mu g,\qquad g\in\mathbb R^d.
$$

要求对**所有概率初态 $\mu$**，这个目标期望都能由预测状态 $z=\mu B$ 唯一恢复。

则其充要条件为

$$
\boxed{g\in V.}
$$

<a id="proposition-3-1-proof"></a>

#### 证明

若 $g=Bc$，则

$$
\mu g=zc,
$$

所以可以恢复。

反之，若 $g\notin V$，可取

$$
v\in V^\perp,\qquad vg\ne0.
$$

因为 $\mathbf1\in V$，所以 $v\mathbf1=0$。取足够小的 $\varepsilon>0$，使

$$
\mu_\pm=\frac1d\mathbf1^{\mathsf T}\pm\varepsilon v
$$

均为概率分布。

这两个分布满足

$$
\mu_+B=\mu_-B,
$$

但

$$
\mu_+g-\mu_-g=2\varepsilon vg\ne0.
$$

所以相同预测状态不能唯一恢复该目标。证毕。

这意味着：**一个观察者可以完整预测自己既有读口的未来，同时仍缺少任务需要的关系。**

更进一步，即使目标确实属于预测空间，取得对应坐标仍可能承载原问题。

<a id="counterexample-3-2"></a>

### 反例 3.2：二维预测核心承载任意 SAT 的计数

给定 $n$ 变量公式 $F$。

取隐藏状态

$$
w\in\{0,1\}^n,
$$

初始分布均匀。允许的实验只是读取 $F(w)$，并保持 $w$ 不变。

于是

$$
M_1=\operatorname{diag}(F(w)),
\qquad
M_0=I-M_1.
$$

由于同一状态被重复读取时结果不变，全部未来测试向量都落在

$$
V\subseteq\operatorname{span}\{\mathbf1,F\}.
$$

因此

$$
\boxed{\dim V\le2.}
$$

但是，初始预测状态中的非平凡坐标是

$$
\boxed{
p_F=\mathbb E[F(w)]
=\frac{\#SAT(F)}{2^n}.
}
$$

精确取得 $p_F$，就取得了 $\#SAT(F)$；判断 $p_F>0$，就决定了 SAT。

这不是 SAT 困难性的下界证明。它证明的是：

> **低维表示与简单递归公式，并未消除复杂性；复杂性可以完整地保留在初始预测坐标的取得中。**

在显式给出全部 $d\times d$ 有理矩阵的情况下，预测基确实可以通过线性闭包与高斯消元，在显式输入规模的多项式时间内构造。但这里 $d=2^n$，这并不等于对紧凑公式长度的多项式成本。

对你的“动态规划极限查表”图景，这个反例尤为直接：**表可以压缩成一个标量，而计算这个标量恰好就是原问题。**

<a id="sec-5"></a>

## 五、真正更接近 $P/NP$ 的观察者：它只需保留一条完成路径

项目新的最小预测核心理论，已经开始把“预测全部未来”与“足以安全行动”分开。

例如，在有限配置模型中，设配置为 $C\subseteq E$，可执行动作是合法新增一个事件，记

$$
\operatorname{En}(C)
=
\{e\notin C:C\cup\{e\}\text{ 合法}\}.
$$

若当前读出为 $r(C)$，项目给出一种取得判据：每个包含多个配置的读出纤维，都必须有共同启用事件，

$$
\bigcap_{C\in r^{-1}(q)}
\operatorname{En}(C)\ne\varnothing.
$$

这样观察者就能在不知道准确配置时，选择一个对所有当前可能配置都合法的动作，并用有限增长最终取得配置。这个判据仍将读出本身的安装、计算与访问成本留作独立问题。[来源：最小预测核心桥 §9–10](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md)

对于 SAT，可以进一步放宽：**我们只需要找到某条正确完成路径，不需要恢复全部世界。**

<a id="definition-2"></a>

### 定义 2：带暂缓输出的选择性预测器

设公式 $F$ 的编码长度为 $L$，变量数为 $n\le L$，满足赋值集为

$$
S_F=\{w\in\{0,1\}^n:F(w)=1\}.
$$

定义一个统一确定性程序

$$
A(F,p)\in\{0,1,?\}.
$$

含义是：

- $0$：下一位采用零；
- $1$：下一位采用一；
- $?$：当前结构不能确定，应保留两个分支。

要求同一个程序在全部输入上多项式时间停止。模型构造、初态取得、参数位数和更新成本都计入该界。

<a id="theorem-4"></a>

### 定理 4：对数个已定位的未决选择，足以推出 $P=NP$

假设存在一个已知可计算预算 $B(L)$，使每个可满足公式 $F$ 都至少有一个满足赋值 $w$，满足：

1. 沿着 $w$ 的每个前缀，预测器若输出 $0/1$，该输出与 $w$ 的下一位一致；
2. 沿着这条路径，输出 $?$ 的次数不超过 $B(L)$。

那么 SAT 可以在

$$
\boxed{
2^{B(L)}\operatorname{poly}(L)
}
$$

时间、 多项式空间内决定，并在有解时输出一个解。

特别地，若

$$
B(L)=O(\log L),
$$

则

$$
\boxed{P=NP.}
$$

> **编者澄清 1（定理 4 的预算取得与资源核算）。** 分支次数采用非负整数预算，并可先截断为 $b(L)=\min\{n,B(L)\}$；长度为 $n$ 的路径不需要更大预算。原文一般时间界的使用还须计入取得这个截断预算的成本。若预算取得需要时间 $T_b(L)$、空间 $S_b(L)$，总界应写为 $T_b(L)+2^{b(L)}\operatorname{poly}(L)$ 时间和 $S_b(L)+\operatorname{poly}(L)$ 空间；只有取得成本也受相应界控制时，才可省略它。也可使用能够高效取得的安全整数上包络 $U(L)\ge b(L)$，并以 $\min\{n,U(L)\}$ 作为实际搜索预算，此时时间指数按实际预算计算。
>
> 在 $B(L)=O(\log L)$ 的情形，可固定足够大的整数常数 $c,c_0$，使用可高效计算的 $U(L)=c\lceil\log_2\max\{2,L\}\rceil+c_0$，其中 $c_0$ 覆盖有限个小长度例外。这给出统一的多项式搜索，无须高效计算精确的 $B(L)$。因此条件性的 $P=NP$ 推论保持；本文没有构造满足条件的全 SAT 预测器。

<a id="theorem-4-proof"></a>

#### 证明

进行带预算的深度优先搜索。

预测器输出 $0/1$ 时，只沿该分支前进；输出 $?$ 时，若尚有预算，就探索两个分支并扣除一次预算；预算用尽后再次遇到 $?$，则剪去该分支。

到达长度 $n$ 时，用原公式直接验证完整赋值。

每条探索路径最多有 $B(L)$ 个二叉分支点，所以至多有 $2^{B(L)}$ 个叶子。路径长度不超过 $n$，总节点数为

$$
O\!\left(n2^{B(L)}\right).
$$

对 YES 输入，假设中的 $w$ 不会被单值预测排除，也不会被预算剪枝，因此一定被找到。

对 NO 输入，没有任何候选能通过最终验证。搜索仍受相同预算限制，必定停止。

每次预测与验证都为多项式成本，深度优先搜索只保存多项式大小的栈。证毕。

反过来，若 $P=NP$，利用 SAT 判定对前缀自归约，即可构造从不暂缓的预测器。因此：

$$
\boxed{
P=NP
\iff
\text{存在满足上述全输入条件、且 }B(L)=O(\log L)
\text{ 的统一预测器}.
}
$$

<a id="sec-5-static-deletion"></a>

#### 这如何回答“从极限静态图往下删”

可以把完整查表结构看成：每个相关前缀都附有一个正确选路标记。

删去部分标记之后，观察者在这些位置输出 $?$。

于是得到一个可证明的保留条件：

> 若保留下来的信息能够以统一多项式成本读取或重算，并且每个有解实例仍保留一条最多含 $O(\log L)$ 个空白位置的正确路径，求解仍然是多项式的。

这是一条明确的充分边界。它没有断言超过对数个空白就必然困难；额外代数结构、共享计算或新的表示仍可能继续加速。

**辅助结构的作用，由此可以量化为：它把需要真正分支的位置减少了多少，以及它能否可靠地指出这些位置。**

<a id="sec-6"></a>

## 六、“预测错得少”与“知道哪里需要探索”，复杂度不同

这正是机器学习与辅助线之间很值得研究的连接。

<a id="definition-3"></a>

### 定义 3：预测创新编码

给定任意确定性自回归预测器

$$
a(F,p)\in\{0,1\},
$$

对完整候选 $w$ 定义

$$
e_i(w)=w_i\oplus a(F,w_{<i}).
$$

$e_i=1$ 表示该位置偏离预测。

<a id="theorem-5"></a>

### 定理 5：创新编码是双射

对固定 $F$，映射

$$
w\longmapsto e(w)
$$

是 $\{0,1\}^n$ 上的双射，而且在预测器为多项式时间时，正反向均可多项式计算。

<a id="theorem-5-proof"></a>

#### 证明

由 $w$ 计算 $e$ 显然可行。

反过来，给定 $e$，递归定义

$$
w_i=e_i\oplus a(F,w_{<i}).
$$

此前前缀已经确定，因此每一步唯一得到下一位。这两个过程互为逆映射。证毕。

于是，至多有 $k$ 次预测错误的完整候选数，恰好为

$$
\sum_{j=0}^{k}\binom nj.
$$

因此：

| 已证明的预测保证 | 直接得到的搜索上界 |
|---|---:|
| 某个有效解至多有常数个未定位错误 | 多项式 |
| 某个有效解至多有 $O(\log L)$ 个未定位错误 | $2^{O((\log L)^2)}$，即拟多项式上界 |
| 某条有效轨迹至多有 $O(\log L)$ 个明确标出的暂缓位置 | 多项式 |

这里给出的是这些保证直接支持的算法上界，没有证明其他算法无法更快。

它指出一个具体研究方向：

> 一个好的辅助结构，既可以提高预测正确率，也可以帮助观察者识别“这一步的依据还不够”。

而且，因为创新编码是双射，对固定 $F$ 下任意随机变量 $W$，都有

$$
\boxed{H(e(W))=H(W).}
$$

预测没有凭空消灭全部信息，而是把信息重新表达为“相对预测的偏离”。

但求解存在性问题，只需要选择一个有效解。它可以利用某条创新编码很短、或者未决位置很少的轨迹，而无须恢复所有解的完整分布。

<a id="sec-7"></a>

## 七、概率与熵：应衡量整条轨迹落入解集的质量

现在可以把“P/NP 好像是一个概率问题”的直觉写得更准确。

设一个统一多项式时间随机生成器产生分布 $Q_F$。每次生成完整候选后，都用原公式验证。

令

$$
s_F=Q_F(S_F)
$$

表示一次生成成功的概率。

<a id="theorem-6"></a>

### 定理 6：有效解质量的 KL 变分刻画

对任意支持于 $S_F$ 的概率分布 $P$，若 $s_F>0$，有

$$
D_{\mathrm{KL}}(P\|Q_F)
=
D_{\mathrm{KL}}
\bigl(P\|Q_F(\cdot\mid S_F)\bigr)
-\log s_F.
$$

因此

$$
\boxed{
-\log s_F
=
\inf_{\operatorname{supp}P\subseteq S_F}
D_{\mathrm{KL}}(P\|Q_F).
}
$$

并且

$$
\boxed{
s_F\ge
\exp[-D_{\mathrm{KL}}(P\|Q_F)].
}
$$

这里采用自然对数。

<a id="theorem-6-proof"></a>

#### 证明

在 $w\in S_F$ 上，

$$
Q_F(w)=s_FQ_F(w\mid S_F).
$$

代入 KL 定义：

$$
\begin{aligned}
D(P\|Q_F)
&=
\sum_{w\in S_F}P(w)
\log
\frac{P(w)}
{s_FQ_F(w\mid S_F)}\\
&=
D(P\|Q_F(\cdot\mid S_F))
-\log s_F.
\end{aligned}
$$

KL 非负；取 $P=Q_F(\cdot\mid S_F)$ 时达到下确界。证毕。

> **编者澄清 2（KL 的方向、支撑与扩展值）。** 本节方向始终为 $D(P\|Q_F)$。采用 $0\log(0/q)=0$，且当 $P(w)>0$ 而 $Q_F(w)=0$ 时相应项为 $+\infty$ 的约定；定理 6 在 $s_F>0$ 时也按扩展值成立，$\exp(-\infty)=0$。下面的通常条件分布链式展开可在 $P\ll Q_F$ 下直接使用：每个 $P$ 正质量前缀都有 $Q_F$ 正质量，因而 $Q_i(\cdot\mid p)$ 有定义。若不假设绝对连续性，不能在 $P$ 正质量而 $Q_F$ 零质量的前缀上任意指定条件分布后照搬该式；须采用在首次失去支撑处计入 $+\infty$ 的链式约定。后文有限总损失界 $D(P\|Q_F)\le C\log L$ 本身即保证 $P\ll Q_F$。后面的 $Q_F=\delta_{00}$ 例中，无穷大具体指 $D(P_{\mathrm{unif}}\|\delta_{00})$，其中 $P_{\mathrm{unif}}$ 在 $\{00,11\}$ 上均匀；反方向为 $\log 2$。

若 $P$ 是满足赋值上的均匀分布，其下一位条件概率就是

$$
P_i(b\mid p)=\frac{Z_F(pb)}{Z_F(p)}.
$$

链式法则给出

$$
D(P\|Q_F)
=
\sum_{i=1}^{n}
\mathbb E_{p\sim P_{<i}}
D\!\left(
P_i(\cdot\mid p)\,\middle\|\,Q_i(\cdot\mid p)
\right).
$$

因此，如果对**每一个可满足输入**都能证明总条件预测损失满足

$$
D(P\|Q_F)\le C\log L,
$$

就有

$$
s_F\ge L^{-C}.
$$

独立重复多项式次、逐次验证，便能以常数以上成功率找到解；NO 输入始终不会错误接受。于是得到

$$
\boxed{NP=RP.}
$$

这是随机计算结论。确定性的 $P=NP$ 仍需要定理 4 那类确定搜索保证，或额外的去随机化结构。

<a id="sec-7-corollaries"></a>

#### 两个推论

第一，逐步平均准确率很高，仍可能使整条轨迹的成功质量很小。例如，唯一有效轨迹有 $n$ 步，每步独立以 $0.99$ 概率选对，则该生成器的成功率为

$$
0.99^n.
$$

这个例子说明的是该生成器的表现，并不证明对应问题难解。

第二，寻找一个解不要求学会均匀解分布。若

$$
S_F=\{00,11\},\qquad Q_F=\delta_{00},
$$

生成器每次都成功；但它与均匀解分布之间的 KL 为无穷大。

因此，任务相关的核心量是

$$
\boxed{Q_F(S_F),}
$$

而“逼近全部解的均匀分布”只是保证这个量足够大的一种途径。

这使机器学习方向更明确：需要研究的是**取得与验证成本受控的生成器，能否在全部目标实例上维持足够的有效解质量**。训练集上的低损失或某个分布上的平均表现，还没有提供这个全输入保证。

<a id="sec-8"></a>

## 八、量子版本：预测状态仍可闭合，但相位、取得和精度都留在模型中

以上预测表示可以直接推广到量子仪器。

给定完全正分支映射

$$
\mathcal E_{a,y},
$$

其对同一动作的分支和保迹。定义未来效果空间

$$
V_Q=
\operatorname{span}_{\mathbb R}
\{\mathcal E_w^*(I):w\text{ 有限}\}
\subseteq\operatorname{Herm}(d).
$$

选基

$$
E_1=I,E_2,\ldots,E_r,
\qquad
z_j=\operatorname{tr}(\rho E_j).
$$

若

$$
\mathcal E_{a,y}^*(E_j)
=
\sum_i(C_{a,y})_{ij}E_i,
$$

> **编者澄清 3（量子归一化更新的定义域）。** 下式中读出概率的表达式适用于全部分支；归一化预测状态 $z'$ 仅在实际结果具有正概率 $zC_{a,y}e_1>0$ 时定义。零概率结果不触发这一条件态更新，不能以除以零的式子指定其后继。

那么仍然有

$$
\boxed{
P(y\mid a,z)=zC_{a,y}e_1,
\qquad
z'=\frac{zC_{a,y}}{zC_{a,y}e_1}.
}
$$

证明直接来自对偶恒等式

$$
\operatorname{tr}(\mathcal E(\rho)E)
=
\operatorname{tr}(\rho\mathcal E^*(E)).
$$

这里的相位与干涉保留在密度矩阵、通道和效果空间里。它符合项目 V14 对实际记录、相干复合和支撑语义的区分。[来源：V14 §6–7](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)

一般只有

$$
r\le d^2.
$$

对 $n$ 个量子比特，$d=2^n$，所以通用上界是 $4^n$。这不是下界，但显然没有提供全局多项式表示保证。

<a id="golden-protocol-boundary"></a>

### 黄金门的新结果说明：极限闭包与有限实现必须分别分析

V15 已经把固定黄金门写成

$$
K=\zeta[I+(\zeta-1)\mathcal P],
\qquad
\zeta=e^{3\pi i/5},
\qquad
\mathcal P^2=\mathcal P.
$$

因而

$$
K^{10}=I.
$$

单个地址反复使用只有十种幂；更丰富的能力来自不同地址上的非交换作用。V15 在明确的编码桥和外部 Fibonacci 编织密度定理下，给出编码近似普适性。[来源：V15 §3–6](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)

同一稿件还给出一个很有启发性的精确障碍。

<a id="theorem-7"></a>

#### 定理 7：有限完整黄金协议不能产生非平凡有理概率

限定为：

- 计算基初始化；
- 有限次黄金门调用；
- 计算基投影测量；
- 有限深反馈；
- 保留全部失败与终止结果；
- 不额外提供随机币或对成功分支重新归一化。

则任意最终事件概率 $p$ 满足

$$
\boxed{
p\in\mathbb Q
\Longrightarrow
p\in\{0,1\}.
}
$$

<a id="theorem-7-proof"></a>

#### 证明

令

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad
\beta=\varphi^{-1/2}.
$$

因为

$$
\beta^4+\beta^2-1=0,
$$

所以 $\beta$ 是代数整数；$\zeta$ 也是代数整数。项目给出的 $K$ 的矩阵元都属于

$$
\mathbb Z[\zeta,\beta].
$$

有限矩阵乘积、计算基投影和有限求和保持代数整数性。因此每条未归一分支的矩阵元，以及事件概率中的有限和

$$
\sum_{h,y}|(M_h)_{yx}|^2
$$

都是代数整数。

有理代数整数只能是整数；再由 $0\le p\le1$，得到结论。证毕。[来源：V15 §8](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)

所以，在这个操作合同内，有限协议无法精确产生概率 $1/2$，尽管相关编码可以有任意好的近似。

而若另行允许每轮新的独立制备，并不断重复至成功，则可以用两次偏币读出接受 $01,10$，得到精确公平结果。项目中一轮成功率为

$$
s=2\varphi^{-3},
$$

于是

$$
\mathbb ET=\frac1s,
$$

但任意固定轮数 $M$ 后仍有

$$
\Pr(\mathrm{abort})=(1-s)^M>0.
$$

这提供了一个严格实例：

$$
\boxed{
\text{有限深协议、条件化、几乎必然终止的无限重复}
}
$$

对应不同的操作资源。它们在极限图中都可以有清楚的数学位置，但不能在成本分析中自动互换。[来源：V15 §11](https://github.com/the-omega-institute/trureturing/blob/388e1086d5de6323c9dd6913d26e72fd91ddfdb6/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)

<a id="sec-9"></a>

## 九、ETH 之后，研究目标已经可以分成清楚的几个层级

本次核对的 OpenAI 官方仓库仍是上次版本。官方说明其结果已在 Lean 中验证，研究者的公开声明则将工作表述为对该主张组织开放独立检查。这里继续把公开算法与复杂度界作为明确供应，而不把本次源码阅读视为重新完成了独立认证。[OpenAI](https://openai.com/index/building-scientific-understanding-with-academic-communities/?utm_source=chatgpt.com)

公开 Lean 范围给出的固定宽度计数时间为

$$
\operatorname{poly}(L)\,
2^{O\!\left(
n(\log\log n)^2/\sqrt{\log n}
\right)}.
$$

项目现在已在 Selection §27、预测谱 §14 中将其接入有限关系计数、前缀完成及数量目标。这个界提供亚指数路线，尚未提供多项式界。[GitHub](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/378.md?utm_source=chatgpt.com)

由此，可以把不同目标放在同一张表里：

| 观察者取得的保证 | 严格后果 |
|---|---|
| 裸 $\Sigma$ 网络的结构性粗预测 | 该子类可多项式求解，无须精确计数 |
| 一般 SAT 的亚指数精确计数供应 | 亚指数时间的可靠前缀增长与完成 |
| 一般 SAT 的统一多项式预测器，某条有效轨迹至多 $O(\log L)$ 次暂缓 | $P=NP$ |
| 统一多项式随机生成器，对每个 YES 输入有逆多项式有效解质量 | $NP=RP$ |
| 相应的统一多项式量子生成与验证保证 | $NP\subseteq BQP$ |

> **编者澄清 4（固定宽度计数供应与表中“一般 SAT”行）。** 上引钉版 Lean 范围明确限定为固定 $k\ge2$、规范编码的 $k$-CNF：其输入变量数为 $n$、编码位长为 $L$，界中的常数及多项式次数可依赖固定的 $k$。表中“一般 SAT 的亚指数精确计数供应”一行保留作者原文，但应用于一般紧凑公式时，必须另外给出保计数的归约，并按归约后的变量数 $N$ 与编码位长 $L'$ 使用 $\operatorname{poly}(L')2^{O_k(N(\log\log N)^2/\sqrt{\log N})}$，前缀限制也须纳入该输入核算。
>
> 例如，对长度为 $L$ 的显式布尔公式或有界扇入电路，逐门加入辅助变量、用固定宽度子句精确约束各门并钉住输出，可使每个原输入赋值的内部延拓唯一；可满足输入赋值与所得完整满足赋值一一对应，从而保计数。常规显式编码下可取 $N=n+O(L)$、$L'=\operatorname{poly}(L)$。这给出按该归约后规模计算的界；它不自动成为按原变量数 $n$ 计算的亚指数界，也不成为一般 SAT 的多项式算法。若要保留原 $n$ 的所示指数，须另证归约变量增长的相应控制，不能只用“多项式归约”替代。

这次研究因此有了一个更具体的落点：

$$
\boxed{
\begin{gathered}
\text{从输入与既有结构取得任务相关的预测状态}\\
\Downarrow\\
\text{将无法确定的位置明确标出}\\
\Downarrow\\
\text{保留至少一条正确完成轨迹}\\
\Downarrow\\
\text{把这条轨迹的未决分支预算压到 }O(\log L)\\
\Downarrow\\
\text{以原任务验证终端输出}.
\end{gathered}
}
$$

对你一直强调的“辅助线”，这给出了一个可证明、也可寻找反例的定义方向：**辅助结构是观察者能够实际取得的一组关系，它使某些原本必须探索的分歧变成可直接推进的步骤，或准确指出剩余分歧的位置。**

裸五模式的 $1/4$ 预测器证明了，这种结构性推进确实存在；二维预测核心的 SAT 反例证明了，简洁表示本身还不够；对数暂缓定理则给出，什么程度的结构性推进已经足以跨到 $P=NP$。

目前尚未构造出覆盖全部 SAT 输入、满足这一预算的观察者。**下一步最有实质内容的研究，是找出哪些关系不变量能让“暂缓位置”被低成本定位，并证明它们在组合、换序、量子读出和观察者增长之后仍然维持足够小的总预算。**
