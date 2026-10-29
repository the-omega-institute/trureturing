<a id="auric-v16"></a>

# 预测、递归、最优化与变分

**AURIC 静态相容理论的等价、障碍与黄金谱**

**定义、定理与完整纸面证明**

**v16.0 · 2026 年 10 月 30 日 · Asia/Singapore**

<a id="sec-abstract"></a>

## 摘要

本文把“预测 = 递归 = 最优化 = 变分”发展为带前件的数学理论。在同一相容对象、边界、评分与资源条件下，有限 DAG 的 Bellman 递归等价于全局路径最优、单位流最小化与潜势对偶；正参考律下的 Gibbs 变分等价于带温度递归及完整切面的配分不变性；有限线性相干网络的全部递归约束等价于一个严格凸残差泛函的唯一零能最小元。黄金均值语言进一步把 Fibonacci 递归、Perron 根与最大熵率联系起来。对 AURIC 五模式，我们复核最大熵完成与 minimax 预测的严格区别，并给出耗散流的能量耗散变分身份。对黄金门，我们建立静态历史态、变分消元及有限阶门的无严格降势结论，并从代数分级推出有限门长的显式误差下界。核心结论是解集与表述的条件等价，而非所有物理更新都在下降同一个能量。复 Hilbert 结构、Born 读出、参考概率及实际资源均保留为各自使用处的前提。

**证明身份。** 本文包含经典理论的自足证明、对项目已有结论的复述核对以及本轮进一步推论；不宣称首次发现 Bellman、Gibbs、Parry、Onsager 或历史态构造。本文不是 Lean 内核认证稿，也未以数值程序、CAS、模拟或门序列枚举代替证明。

> **转换说明（编者）。** 本文完整转换用户提供的 v16.0 XeLaTeX 稿件。陈述沿用源稿各节共享编号；自动编号公式沿用全局 (1)–(9)，其余显示公式不编号。源稿对项目快照、历史审计、前稿与本轮推论的报告均归属于作者；转换不构成这些报告或数学结论的独立认证。排版宏已展开，分页、页眉及字体设置由 Markdown 排版替代。

> **格式说明（编者）。** 源稿 `align` 按原行拆为显示公式；第 6 节每行的成对等式共用一个标签，第 12 节仅末行标 (9)。引用和目录改为显式锚点链接。正文、公式、证明与资源边界按原稿保留；未作实质数学修订，未运行 Lean、数值实验、CAS、门枚举或硬件认证。

## 目录

1. [最新项目快照与本轮问题](#sec-1)
2. [把“等号”写成什么](#sec-2)
3. [五模式：相容确定纤维，评分选出预测](#sec-3)
4. [递归何时真的是下降](#sec-4)
5. [静态 DAG 上的四重等价与最优证书](#sec-5)
6. [概率、递归与 Gibbs 变分的精确桥梁](#sec-6)
7. [黄金谱：Fibonacci 递归等于熵率变分](#sec-7)
8. [内生预测：条件期望递归与信息增长](#sec-8)
9. [量子相干 DAG：预测就是零残差全局完成](#sec-9)
10. [黄金门的静态历史、切面与消元](#sec-10)
11. [黄金门的周期性排除逐步严格降势](#sec-11)
12. [五模式耗散的真正变分身份](#sec-12)
13. [量子实时间是驻作用，虚时间才是此能量下降](#sec-13)
14. [黄金门优化：下确界为零却没有有限最小元](#sec-14)
15. [可以保留的统一命题与研究边界](#sec-15)

[文献与项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 最新项目快照与本轮问题

本轮只读核验的研究分支为 `dev`，不可变提交是
`f22ccafb22873bb5445053498b0f64f9ea111ede`。
提交时间为 2026-10-30 01:00:09（Asia/Singapore），标题为 *Ingest sink-incidence, six-phase energy and graph-deficit theory updates (#23767)*。相对上一稿 `52ce13dc…`，理论目录有 18 个变更路径，其中 4 个新增、14 个修改；当前理论目录含 1005 个文件。本轮针对性核验 17 份当前源码的 Git blob，并核对 4 份旧版本及差异。这是定向研究核验，不能解释为对全部项目证明的认证。

与本轮最直接相关的证据如下。

1. [《金字塔基础公式》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)已有隐藏纤维、最大熵完成与最坏误差预测；两种最优通常不同。
2. [《信息逃逸与热力学作用》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_FIB_PYRAMID_INFORMATION_ESCAPE_DYNAMICS_THERMODYNAMIC_ACTION.md)已有质量作用流、对数平均 mobility 及指数耗散不等于同端点最小二次作用的精确比较。
3. [《KL 作用原卷》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)定理 21.6 及其后续论述已有同一实际相邻律的 Markov 最大熵补全、条件互信息余项及逐边 Bellman 证书。
4. [《真实切面恢复》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md)本轮新增的 §§14–17 使用条件期望递归构造共同探测列表，但保留 $4^d$ 目录工作；多项式实际 Read 数不等于多项式总计算工作。
5. [《相干重构续卷》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)本轮新增的 §§64–67 给出共同有限码、三源循环比较及实际联合记录；假设 64.2 仍供应初始化、寻址、相位校准与 Born 合同，§67.3 明确量子起源尚未闭合。

前稿 v14 与 v15 现已作为用户稿件转换收入项目。它们构成研究连续性，不能充当独立验证。本文引用 v15 的位置均指出具体数学前提；本轮新算术界另给自足证明。

<a id="sec-2"></a>

## 2. 把“等号”写成什么

<a id="statement-2-1"></a>

#### 定义 2.1（相容完成问题）

给定候选空间 $\mathcal X$、观察映射 $O$、已得记录 $r$ 和约束 $\mathcal C$，定义

$$
\mathcal M(r)=\{x\in\mathcal X: O(x)=r,\ \mathcal C(x)=0\}.
$$

若记录带误差，应以已声明的集合约束 $O(x)\in R$ 取代等式。一个目标读数是 $f:\mathcal X\to\mathcal Y$。预测可以是可行集合 $f(\mathcal M(r))$、某个评分下的最优点预测，或已标定联合律下的条件分布。三者类型不同。

<a id="statement-2-2"></a>

#### 定义 2.2（四个层次）

递归是局部合成或更新方程 $x=T(x)$、$x_{k+1}=T(x_k)$；最优化是给定可行域与目标的 $\operatorname*{arg\,min} \mathcal E$；变分驻值是 $\delta\mathcal S=0$；递归求解器则是寻找上述解的具体迭代。**解集相同、迭代收敛、物理过程下降、资源最优** 分别是四个命题。

我们所追求的精确表述是：在同一对象和约束上，证明

$$
\{\text{相容预测}\}=\{\text{递归方程的解}\}
=\operatorname*{arg\,min}\mathcal E,
$$

并在有充分条件时再证明它等于驻点集。不能仅因某种最小化形式存在，就宣布目标、度量或物理规律被唯一决定。

内生观察者可以一并作为变量 $\theta$，例如 $O_\theta(x)=r$。这会产生真实的辨识问题：观测 $y=rx$ 对 $(x,r)\mapsto(ax,r/a)$ 不变。误差 $|rx-y|^2$ 的最小值为零，却不唯一确定对象与尺子。应预测可辨识的关系，或增加实际标定记录；“写成变分”没有消除这种自由度。

<a id="sec-3"></a>

## 3. 五模式：相容确定纤维，评分选出预测

采用位置标签 $(0,1,2,3,13)$，对应项目的 $(0,2,3,5,25)$ 与合法三位词 $(000,100,010,001,101)$。此处标签表示五种合法配置，不预设它们已是三维空间中的点或正交坐标。

令 $p=(p_0,p_1,p_2,p_3,p_{13})$，定义

$$
X=p_1+p_{13},\quad Y=p_3+p_{13},\quad Z=p_2,\quad R=1-Z.
$$

固定这三个读数后，隐藏关系 $\kappa=p_{13}$ 满足

<a id="equation-1"></a>

$$
p(\kappa)=(R-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\tag{1}
$$

<a id="equation-2"></a>

$$
\kappa_-=\max(0,X+Y-R)\le\kappa\le\min(X,Y)=\kappa_+.
\tag{2}
$$

<a id="statement-3-1"></a>

#### 定理 3.1（同纤维上的两种最优）

设 $R>0$ 且 $0<X,Y<R$。最大 Shannon 熵的唯一完成为

$$
\kappa_*=\frac{XY}{R}.
$$

若只知 $\kappa\in[\kappa_-,\kappa_+]$，以最坏绝对误差评价点预测，则唯一 minimax 预测为

$$
\widehat\kappa_{\rm mm}=\frac{\kappa_-+\kappa_+}{2},\qquad
\inf_a\sup_\kappa|a-\kappa|=\frac{\kappa_+-\kappa_-}{2}.
$$

**证明。**

使用自然对数，令 $H(p)=-\sum_i p_i\log p_i$。纤维内部

$$
H'(\kappa)=\log\frac{(X-\kappa)(Y-\kappa)}{\kappa(R-X-Y+\kappa)},\qquad
H''(\kappa)=-\left(\frac{1}{p_0}+\frac{1}{p_1}+\frac{1}{p_3}+\frac{1}{p_{13}}\right)<0.
$$

令一阶导数为零得 $R\kappa=XY$。所列严格边际条件保证它位于纤维内部，严格凹性给唯一性。另一方面，最坏绝对误差等于 $\max(|a-\kappa_-|,|a-\kappa_+|)$，唯一在区间中点取两端平衡并达到半宽。端点退化时直接按单点处理；$R=0$ 时只有顶点态，不使用 $XY/R$。

∎

特别取 $X=Y=1/5,Z=0$，可行纤维为 $[0,1/5]$，但

$$
\kappa_*=\frac{1}{25}\ne \frac{1}{10}=\widehat\kappa_{\rm mm}.
$$

这个项目已有的反例准确说明：**关系相容本身不足以选择唯一概率或唯一“最佳预测”。** 最大熵描述一个补全规则；它不是未知真实来源必然采用该规则的证明。

<a id="statement-3-2"></a>

#### 命题 3.2（隐藏关系的 KL 储备）

在上述固定纤维上，记 $p_*=p(\kappa_*)$，有

$$
D(p\Vert p_*)=H(p_*)-H(p)
=R I(x_1:x_3\mid x_2=0).
$$

**证明。**

条件于中位为零，底面四格总质量为 $R$，两端边际固定为 $X/R,Y/R$；$p_*$ 正是它们的乘积分布。将条件互信息定义展开即得最右表达式。$\sum p_i\log(p_*)_i$ 只依赖所固定的边际，故等于 $\sum(p_*)_i\log(p_*)_i$，得到熵差。零质量按 $0\log0=0$ 处理。

∎

<a id="sec-4"></a>

## 4. 递归何时真的是下降

<a id="statement-4-1"></a>

#### 定理 4.1（收缩递归的残差变分证书）

设 $T$ 将非空完备度量子空间 $X$ 映到自身，且在所用范数下为 $q<1$ 的收缩。则存在唯一固定点 $x_*$，并且

$$
E_{\rm res}(x)=\frac{1}{2}\left\lVert x-Tx\right\rVert^2,
\quad E_{\rm res}(Tx)\le q^2E_{\rm res}(x),
\quad \left\lVert x-x_*\right\rVert\le \frac{\left\lVert x-Tx\right\rVert}{1-q}.
$$

因此固定点、零残差及全局最小元相同，迭代还给可核查的精度证书。

**证明。**

相邻迭代差至多为 $q^k\left\lVert x_1-x_0\right\rVert$，几何级数使迭代为 Cauchy 列；完备性给极限，连续性给固定点，收缩性给唯一性。残差不等式是 $\left\lVert Tx-T^2x\right\rVert\le q\left\lVert x-Tx\right\rVert$。由
$\left\lVert x-x_*\right\rVert\le\left\lVert x-Tx\right\rVert+q\left\lVert x-x_*\right\rVert$ 得最后一式。

∎

无收缩前件时结论会失败。$T(x)=-x$ 的固定点只有零，但非零迭代永远两周期。即使 $T(x)=-x/2$ 收敛，符号读出也会永远交替；“到有限分辨率后必定定格”还要求极限远离量化边界，或采用已声明的容差等价。

<a id="statement-4-2"></a>

#### 定理 4.2（自然递归场的势函数判据）

在开凸域 $U\subset\mathbb{R}^d$ 上，设 $T\in C^1$，$F(x)=x-T(x)$。存在 $E\in C^2$ 使 $\nabla E=F$，当且仅当 $DT(x)=DT(x)^{\mathsf T}$。若进一步 $I-DT(x)\succeq mI$、$m>0$，则该势严格凸，任何存在的驻点都是唯一全局最小元。

**证明。**

必要性由 Hessian 对称。充分性取 $x_0\in U$，定义

$$
E(x)=\int_0^1 F(x_0+t(x-x_0))\cdot(x-x_0)\,dt.
$$

微分、使用 $DF$ 对称并对 $t$ 作分部积分，得到 $\nabla E=F$。正定 Hessian 给强凸不等式，因而存在的驻点唯一且全局最小；这里没有由开放域自动推断最小元存在。

∎

例如 $T(x,y)=(y,-x)$ 的 $DF=\left(\begin{smallmatrix}1&-1\\1&1\end{smallmatrix}\right)$ 不对称。互相预测与递归相容不自动产生欧氏梯度势。这不排除更换度量、加入变量或另造残差泛函，恰说明这些操作是额外的表述选择。

<a id="statement-4-3"></a>

#### 命题 4.3（通用残差编码的局限）

若 $F$ 有零点，$\min\frac12\left\lVert F(x)\right\rVert^2=0$，且零能最小元恰是零点；但正残差局部最小仍可存在。

**证明。**

非负平方给第一部分。取 $F(x)=x^3-3x+3$，它因连续且两端异号而有实根；在 $x=1$，$F=1,F'=0,F''=6$，所以 $E'=0,E''=6>0,E=1/2$。这是严格局部最小，却不相容。进一步，$\mathcal L(x,\lambda)=\lambda\cdot F(x)$ 总可编码为联合驻值问题，但在 $F(x)\ne0$ 处沿 $\lambda=-tF(x)$ 趋于负无穷，不能称为最小化。

∎

<a id="sec-5"></a>

## 5. 静态 DAG 上的四重等价与最优证书

<a id="statement-5-1"></a>

#### 定义 5.1（完整有限预测图）

取有限 DAG $G=(V,E)$、起点 $s$、终点 $t$，每个相关顶点可达 $t$，每条边有实代价 $c_e$。多个终止点与终止损失可接到同一个新终点，接边代价取对应损失。完整路径 $h:s\leadsto t$ 的代价为 $C(h)=\sum_{e\in h}c_e$。状态必须保留决定后继、成本和停止的实际信息。

<a id="statement-5-2"></a>

#### 定理 5.2（路径、递归、流与势的等价）

以下四个数相等，且各自达到：

<a id="equation-3"></a>

$$
\min_{h:s\leadsto t} C(h),
\tag{3}
$$

<a id="equation-4"></a>

$$
V(s),\quad V(t)=0,\quad V(v)=\min_{v\to w}\{c_{vw}+V(w)\},
\tag{4}
$$

<a id="equation-5"></a>

$$
\min\Big\{\sum_e c_e f_e:f_e\ge0,\ \operatorname{div}f=\delta_s-\delta_t\Big\},
\tag{5}
$$

<a id="equation-6"></a>

$$
\max\{u(s):u(t)=0,\ u(v)\le c_{vw}+u(w)\ \text{对全部边}\}.
\tag{6}
$$

Bellman 解 $V$ 唯一。任意可行势 $u$ 和任意完整路径满足

$$
C(h)-u(s)=\sum_{v\to w\in h}[c_{vw}+u(w)-u(v)]\ge0.
$$

若某路径全部缩减代价为零，它已经附带全局最优证书。

**证明。**

按逆拓扑序定义 $V$；终点固定，每步依赖已定义后继，因此唯一。按第一条边分解路径集合，归纳得 $V(v)$ 是从 $v$ 出发的最小路径成本，并有取等路径。

可行单位流在 DAG 上可分解为完整路径的凸组合：沿正流边从 $s$ 走到 $t$，减去沿途最小流量，重复；每次至少去掉一条正边，且 DAG 无可藏循环流，有限步完成。流成本是路径成本的凸组合，不能低于最优路径；最佳路径本身给可行流。

对可行势逐边求和，内部势望远镜抵消，得到最后公式；故 $u(s)$ 是共同下界。$V$ 自身可行且有全紧路径，故对偶最大值也达到同一数。

∎

这把“在没有最优之前或许它就是最优”推进为可证明的认证方式：不必先逐个比较所有候选；合法下界势与一条达到它的路径足以认证。但找到证书的计算成本另计。

<a id="statement-5-3"></a>

#### 说明 5.3（终止条件不可删）

若允许零成本自环及成本一的退出，所有完整终止路径的最小成本为一，但 Bellman 方程 $V=\min(V,1)$ 有全部 $V\le1$ 作为解。无限继续和实际停止不能被同一个未加条件的局部等式混淆。

<a id="sec-6"></a>

## 6. 概率、递归与 Gibbs 变分的精确桥梁

<a id="statement-6-1"></a>

#### 定义 6.1（路径参考律与变分预测）

在上一节有限 DAG 上，每个非终点给严格正的出边参考概率 $q(w\mid v)$，行和为一。它诱导完整路径律 $Q(h)=\prod_{v\to w\in h}q(w\mid v)$。有限 DAG 与完整终止条件保证 $\sum_hQ(h)=1$。固定 $\tau>0$，定义

$$
\mathcal F_\tau(P)=\mathbb{E}_P C+\tau D(P\Vert Q).
$$

<a id="statement-6-2"></a>

#### 定理 6.2（Gibbs、软 Bellman 与条件转移）

令

$$
Z(v)=\sum_{h:v\leadsto t}Q(h\mid v)e^{-C(h)/\tau},\qquad Z(t)=1.
$$

则唯一最优路径律、最优值及递归分别为

<a id="equation-7"></a>

$$
\begin{aligned}
P_*(h)&=\frac{Q(h)e^{-C(h)/\tau}}{Z(s)},&
\min_P\mathcal F_\tau(P)&=-\tau\log Z(s),
\end{aligned}
\tag{7}
$$

<a id="equation-8"></a>

$$
\begin{aligned}
Z(v)&=\sum_{v\to w}q(w\mid v)e^{-c_{vw}/\tau}Z(w),&
V_\tau(v)&=-\tau\log Z(v).
\end{aligned}
\tag{8}
$$

特别

$$
V_\tau(v)=-\tau\log\sum_{v\to w}q(w\mid v)
e^{-[c_{vw}+V_\tau(w)]/\tau},
$$

而 $P_*$ 的实际条件转移为

$$
q_*(w\mid v)=\frac{q(w\mid v)e^{-c_{vw}/\tau}Z(w)}{Z(v)}.
$$

对任何 $P$ 还有精确误差身份

$$
\mathcal F_\tau(P)=-\tau\log Z(s)+\tau D(P\Vert P_*).
$$

**证明。**

把 $\log P_* =\log Q-C/\tau-\log Z(s)$ 代入相对熵，即得最后身份。有限 KL 非负且仅在两律相同取零，给唯一性。按首边分解后缀路径得 $Z$ 递归；条件转移公式随之归一化。沿完整路径相乘时所有中间 $Z$ 抵消，恢复 $P_*$。

∎

<a id="statement-6-3"></a>

#### 命题 6.3（完整切面的不变性与零温极限）

若切面 $\Sigma$ 是每条完整路径恰好穿过一次的顶点集合，令 $a(v)$ 为从 $s$ 到 $v$ 的全部前缀参考权重乘 $e^{-\text{前缀成本}/\tau}$ 的总和，则

$$
Z(s)=\sum_{v\in\Sigma}a(v)Z(v),\qquad
P_*(\text{穿过 }v)=\frac{a(v)Z(v)}{Z(s)}.
$$

若 $m=\min_hC(h)$，$h_*$ 为任一最优路径，则

$$
m\le-\tau\log Z(s)\le m-\tau\log Q(h_*),
$$

因而 $\tau\downarrow0$ 时最优值趋于 Bellman 最优值。

**证明。**

完整路径按唯一切面交点分割，再分别求前后缀之和即得第一式。由 $Q$ 归一化，$Q(h_*)e^{-m/\tau}\le Z(s)\le e^{-m/\tau}$，取负对数即得界。

∎

这是一种真正不依赖外部时钟的统一：全局变分与局部递归描述同一完整对象，切面只是分解方式。其前件仍包括参考律、可加成本、足够的状态与正温度；没有从“存在可能性”独自推出这些选择。KL 控制和指数线性化的先行工作见 Todorov （[2](#ref-todorov)）。

<a id="sec-7"></a>

## 7. 黄金谱：Fibonacci 递归等于熵率变分

<a id="statement-7-1"></a>

#### 定义 7.1（带权黄金均值语言）

合法二进制串禁止相邻 $11$。每个 $1$ 赋权 $\lambda>0$，长度 $n$ 的配分函数记为 $Z_n$。设

$$
A_\lambda=\begin{pmatrix}1&\lambda\\1&0\end{pmatrix},\quad
\rho=\frac{1+\sqrt{1+4\lambda}}{2},\quad s=1-\rho.
$$

<a id="statement-7-2"></a>

#### 定理 7.2（递归与谱增长）

$$
Z_0=1,\quad Z_1=1+\lambda,\quad Z_n=Z_{n-1}+\lambda Z_{n-2},
$$

$$
Z_n=\frac{\rho^{n+2}-s^{n+2}}{\rho-s},\qquad
\lim_{n\to\infty}\frac{\log Z_n}{n}=\log\rho.
$$

当 $\lambda=1$，$\rho=\varphi=(1+\sqrt5)/2$。

**证明。**

以首位为零或以 $10$ 开头分解合法串，得到递归；初值单独计数。两根满足 $z^2=z+\lambda$，所列显式式满足同一递归和初值。因 $\rho>1$ 且 $|s|=\rho-1<\rho$，对数增长率成立。

∎

<a id="statement-7-3"></a>

#### 定理 7.3（黄金谱的最大熵变分身份）

令 $h=(\rho,1)^{\mathsf T}$，定义

$$
P_{ij}=\frac{A_{ij}h_j}{\rho h_i},\qquad
P=\begin{pmatrix}\rho^{-1}&\lambda\rho^{-2}\\1&0\end{pmatrix},
\quad \pi=\frac{1}{2\rho-1}(\rho,\rho-1).
$$

对任意平稳合法 Markov 律 $(\nu,Q)$，熵率 $h(Q)=-\sum_{ij}\nu_iQ_{ij}\log Q_{ij}$ 满足

$$
\boxed{h(Q)+(\log\lambda)\nu_1
=\log\rho-\sum_i\nu_iD(Q_i\Vert P_i).}
$$

等号 $h(Q)+(\log\lambda)\nu_1=\log\rho$ 唯一选出 $(\pi,P)$。该最优性也覆盖全部平稳合法过程；达到最优的过程必为上述一阶 Markov 过程。

**证明。**

$A_\lambda h=\rho h$ 保证 $P$ 行和为一，直接代入验证 $\pi P=\pi$。合法边上

$$
\log P_{ij}=\log A_{ij}+\log h_j-\log h_i-\log\rho.
$$

按 $\nu_iQ_{ij}$ 求和，平稳性抵消两项 $\log h$；只有 $0\to1$ 有 $\log A_{ij}=\log\lambda$，其平稳频率为 $\nu_1$。将行 KL 展开即得身份。等号强迫所有有质量行等于 $P$；该链不可约，平稳质量不能只停在某个真子集，故全部行及平稳律唯一。

对任意平稳过程，熵率不超过 $H(X_1\mid X_0)$；这是条件熵随增加过去信息而不增及链式法则的结果。取相同一位、相邻位边缘的 $Q$，前述上界继续成立。若取等，所有有限过去上的额外条件互信息都为零，因而具有一阶 Markov 条件；再用行 KL 的等号条件得到唯一过程。

∎

特别在 $\lambda=1$，

$$
P_{00}=\varphi^{-1},\quad P_{01}=\varphi^{-2},\quad P_{10}=1,
\qquad \sup h=\log\varphi.
$$

这里黄金比例同时是**合法完成数量的递归增长率、转移算子的 Perron 根和最大熵率的指数** 。这是标准 Parry 理论在本合法语言上的具体化 （[3](#ref-parry)），不是量子公理的无前提推导。

<a id="statement-7-4"></a>

#### 推论 7.4（同一无限平稳谱的五模式切片）

按 $(000,100,010,001,101)$ 顺序，三位边缘为

$$
p^{(\lambda)}=\frac{\big(1,\rho-1,\lambda,\rho-1,(\rho-1)^2\big)}{\rho(2\rho-1)}.
$$

因此 $p_0p_{13}=p_1p_3$，对应给定中位零后的两端条件独立。$\lambda=1$ 时

$$
p^{(1)}=\frac{\big(1,\varphi^{-1},1,\varphi^{-1},\varphi^{-2}\big)}{\varphi\sqrt5}.
$$

**证明。**

每个合法三位词的概率为 $\pi_iP_{ij}P_{jk}$，逐项代入并使用 $\lambda=\rho(\rho-1)$ 即得。

∎

有限三位串在等权计数下是五点均匀律；无限平稳最大熵率律的三位切片则是上式。边界、完成深度和优化目标不同，结果自然不同。它也不自动等于黄金量子门的 Born 输出：前者是正权重完成，后者还含相位、干涉与具体测量。

<a id="sec-8"></a>

## 8. 内生预测：条件期望递归与信息增长

<a id="statement-8-1"></a>

#### 定理 8.1（评分下的最优预测与塔式相容）

给定同一实际联合律、实值 $Y\in L^2$ 和记录 $\sigma$ 代数 $\mathcal F$，令 $m_\mathcal F=\mathbb{E}[Y\mid\mathcal F]$。任意 $\mathcal F$ 可测平方可积预测 $g$ 满足

$$
\mathbb{E}[(Y-g)^2]=\mathbb{E}[(Y-m_\mathcal F)^2]+
\mathbb{E}[(g-m_\mathcal F)^2].
$$

若 $\mathcal F\subset\mathcal G$，则

$$
\mathbb{E}[m_\mathcal G\mid\mathcal F]=m_\mathcal F,
\quad
\mathbb{E}[(Y-m_\mathcal F)^2]-\mathbb{E}[(Y-m_\mathcal G)^2]
=\mathbb{E}[(m_\mathcal G-m_\mathcal F)^2].
$$

**证明。**

展开平方，交叉项因 $\mathbb{E}[Y-m_\mathcal F\mid\mathcal F]=0$ 消失。塔式恒等式由条件期望对每个 $\mathcal F$ 事件的积分定义及唯一性得出。把较精细的预测代入相应正交分解即得风险差。

∎

这给“预测行为成为自身增长”的一个精确定义：新记录扩张可用信息，最佳平方评分风险下降多少，恰等于预测修正的平方量。该结论不保证真实轨迹的每次点误差都下降，也不在没有共同联合律时生效。对有限离散目标 $Y$，给定实际条件概率 $p(\cdot\mid R)$ 和预测概率 $q(\cdot\mid R)$，正概率事件上的 $q=0$ 按无穷损失处理，对数评分另有

$$
\mathbb{E}[-\log q(Y\mid R)]=H(Y\mid R)+
\mathbb{E}_R D(p(\cdot\mid R)\Vert q(\cdot\mid R)),
$$

由展开定义直接得到；预测何为最优取决于评分 （[4](#ref-gneiting)）。

<a id="statement-8-2"></a>

#### 命题 8.2（条件期望递归可以构造确定见证）

有限随机选择树上，令终端坏事件计数 $B$ 为非负整数。若 $\mathbb{E} B<1$，并能在每个已达前缀计算实际各子分支的条件期望，则可逐层选择条件期望不增的正概率子分支，最终得到 $B=0$ 的确定叶。

**证明。**

父节点条件期望是各正概率子节点条件期望的凸组合，因此至少一子节点不超过父值。有限层后条件期望等于该叶实际整数 $B<1$，故为零。

∎

这与项目最新真实切面构造的条件期望路线一致。关键资源是那些条件期望能否在实际信息与工作预算内得到；“存在一个好子节点”不提供免费的求值器。完整控制记录、状态恢复与规范化成本应保留在递归状态中。

<a id="sec-9"></a>

## 9. 量子相干 DAG：预测就是零残差全局完成

<a id="statement-9-1"></a>

#### 定义 9.1（线性相干递归网络）

有限 DAG 每个内部顶点 $v$ 配有限维复 Hilbert 空间 $\mathcal H_v$，边 $u\to v$ 配线性算子 $A_{vu}$，边界供应 $b_v$。令

$$
x_v=b_v+\sum_{u\to v}A_{vu}x_u,
\qquad \mathcal H=\bigoplus_v\mathcal H_v.
$$

在任意拓扑排序下，块矩阵 $A$ 严格三角，因此 $A^m=0$ 对某个有限 $m$ 成立。这里多父节点的贡献是振幅求和；不能替换成每条来边单独要求相等。

<a id="statement-9-2"></a>

#### 定理 9.2（相容预测、递归、最小元与驻点）

任意 $W=W^\dagger\succ0$ 下，记 $B=I-A$。下列四项等价：

1. $x$ 满足全部局部递归；
2. $x=x_*=(I+A+\cdots+A^{m-1})b$；
3. $x$ 是 $E_W(x)=\frac12\langle Bx-b,W(Bx-b)\rangle$ 的全局最小元；
4. 对所有实变分方向（包括复向量的实、虚分量）都有 $\delta E_W=0$。

解唯一，最小值为零，Hessian 为正定的 $B^\dagger WB$。若 $W\succeq w_0I$，则

$$
E_W(x)\ge \frac{w_0}{2\left\lVert B^{-1}\right\rVert^2}\left\lVert x-x_*\right\rVert^2.
$$

**证明。**

有限几何级数给 $B^{-1}=I+A+\cdots+A^{m-1}$，故前两项等价。正性使 $E_W=0$ 当且仅当 $Bx=b$。变分为
$\operatorname{Re}\langle B\eta,W(Bx-b)\rangle$，对全部 $\eta$ 为零当且仅当 $B^\dagger W(Bx-b)=0$；两矩阵可逆，故等价零残差。最后用 $x-x_*=B^{-1}(Bx-b)$。

∎

$A^k$ 的每个块是相应长度路径上有序算子乘积的和。因此该定理把整个路径谱的相干预测写为一个静态相容最小值。正的 $W$ 有很多选择，却给同一解；没有由这个等价唯一推出物理能量。

甚至在这个严格凸情形，平行递归 $x\mapsto Ax+b$ 也未必逐步降低 $E_I$。取 $A=\left(\begin{smallmatrix}0&M\\0&0\end{smallmatrix}\right)$、$b=0$、$M>1$、$x=(M,1)$，则 $E_I(x)=1/2$，$E_I(Ax)=M^2/2$，但 $A^2x=0$。**有限步相容求解与逐步下降仍是不同命题。**

已给定量子仪器时，也可把完整测量记录树上的未归一化分支算子置于 Hilbert–Schmidt 空间，使用同样线性残差结构。这里 CP、仪器及 Born 合同是输入；平方残差本身没有推导它们。

<a id="sec-10"></a>

## 10. 黄金门的静态历史、切面与消元

固定黄金门满足

$$
K=\zeta[I+(\zeta-1)P],\quad P=P^\dagger=P^2,
\quad \zeta=e^{3\pi i/5},\quad K^{10}=I.
$$

其谱分解为 $K=\zeta(I-P)+\zeta^2P$。对有限电路 $U_1,\ldots,U_L$，每个 $U_j$ 可以是某地址的 $K$。令 $W_0=I,W_j=U_j\cdots U_1$。

<a id="statement-10-1"></a>

#### 定理 10.1（有限黄金电路的静态零能历史）

在 $\mathbb{C}^{L+1}\otimes\mathcal H$ 上，定义

$$
D_j=\langle j|\otimes I-\langle j-1|\otimes U_j,
\qquad H_{\rm prop}=\frac{1}{2}\sum_{j=1}^L D_j^\dagger D_j.
$$

对 $\Psi=\sum_j|j\rangle\psi_j$，有

$$
\langle\Psi,H_{\rm prop}\Psi\rangle
=\frac{1}{2}\sum_j\left\lVert \psi_j-U_j\psi_{j-1}\right\rVert^2.
$$

其归一化零能态恰是

$$
|\Psi_\eta\rangle=\frac{1}{\sqrt{L+1}}
\sum_{j=0}^L |j\rangle W_j|\eta\rangle,\quad\left\lVert \eta\right\rVert=1.
$$

对单位输入 $b$ 再加 $H_{\rm in}=|0\rangle\langle0|\otimes(I-|b\rangle\langle b|)$，归一化零能态在整体相位之外唯一，为 $\Psi_b$。

**证明。**

逐项平方给期望式；非负和为零当且仅当全部传播约束成立。它们唯一确定 $\psi_j=W_j\psi_0$，酉性给总范数 $(L+1)\left\lVert \psi_0\right\rVert^2$。正算子和的核是各核之交，输入项把 $\psi_0$ 限制为 $b$ 的倍数。

∎

这是标准历史态构造 （[5](#ref-aharonov)） 在黄金门菜单上的应用。标签 $j$ 可解释为逻辑切面地址，不必是外部绝对时钟；但新增地址寄存器、输入罚项、历史态制备与读出均有资源要求。数学上存在零能态不等于原始固定门菜单可免费精确制备它。

<a id="statement-10-2"></a>

#### 定理 10.2（递归合成等于变分消元）

对酉 $U,V$、$w_1,w_2>0$，

$$
\min_z\{w_1\left\lVert z-Ux\right\rVert^2+w_2\left\lVert y-Vz\right\rVert^2\}
=\frac{w_1w_2}{w_1+w_2}\left\lVert y-VUx\right\rVert^2.
$$

故任意链都有

$$
\min_{\psi_1,\ldots,\psi_{L-1}}
\sum_{j=1}^Lw_j\left\lVert \psi_j-U_j\psi_{j-1}\right\rVert^2
=\left(\sum_{j=1}^Lw_j^{-1}\right)^{-1}
\left\lVert y-U_L\cdots U_1x\right\rVert^2,
$$

其中 $\psi_0=x,\psi_L=y$。

**证明。**

置 $z'=Vz$、$a=VUx$，酉性把左边变成 $w_1\left\lVert z'-a\right\rVert^2+w_2\left\lVert y-z'\right\rVert^2$。配方得到唯一最小 $z'=(w_1a+w_2y)/(w_1+w_2)$ 及所列余项；对链反复应用，等效倒权重相加。

∎

特别十个等权 $K$ 的内部消元给

$$
\min_{\rm internal}\sum_{j=1}^{10}\left\lVert \psi_j-K\psi_{j-1}\right\rVert^2
=\frac{1}{10}\left\lVert y-x\right\rVert^2.
$$

门的合成关系变成恒等，但相容性代价的系数仍保留十层长度。忽略这个因子就丢失了变分度量信息。

<a id="statement-10-3"></a>

#### 命题 10.3（一般 Schur 消元）

若 $Q=\left(\begin{smallmatrix}A&B\\B^\dagger&C\end{smallmatrix}\right)\succeq0$ 且 $C\succ0$，则

$$
\min_z(b,z)^\dagger Q(b,z)
=b^\dagger(A-BC^{-1}B^\dagger)b.
$$

只要内部块可逆，逐块消元次序不影响最终边界二次型。

**证明。**

配方为 $(z+C^{-1}B^\dagger b)^\dagger C(z+C^{-1}B^\dagger b)$ 加右侧。次序无关由 $\min_x\min_y E=\min_{x,y}E$ 及唯一最小元得到。高斯积分另有行列式归一化因子，不能把本最小化公式直接冒充积分公式。

∎

<a id="statement-10-4"></a>

#### 命题 10.4（无外部时钟不等于任意换序）

有限偏序中的每个事件配酉算子。所有线性扩张给出相同算子，当且仅当每对不可比较事件的算子交换。

**证明。**

任意两个线性扩张可用相邻不可比较事件的交换连接，故充分。对任意不可比较的两事件，先排列两者所有严格前驱的并，再相邻排列它们，可得到仅交换两者的两个线性扩张。约去可逆的共同前后缀，得必要性。

∎

进一步，取连通平行传输图，各边传输 $U_{vu}$ 酉，反向边定义为其伴随，闭走允许使用反向边。对边关系 $x_v=U_{vu}x_u$，固定根向量 $b$ 后，零残差完成存在当且仅当每个根闭走的有序乘积固定 $b$。必要性沿闭走代入；充分性以任一路径定义 $x_v$，闭走条件保证路径无关。局部酉变换 $x_v\mapsto G_vx_v$、$U_{vu}\mapsto G_vU_{vu}G_u^\dagger$ 保持全部残差范数。这给观察者坐标自由度一个精确模型；它与前一节多路径振幅求和是两种不同的合成语义。

<a id="sec-11"></a>

## 11. 黄金门的周期性排除逐步严格降势

<a id="statement-11-1"></a>

#### 定理 11.1（有限阶更新的无严格 Lyapunov 定理）

若 $K^{10}=I$，实函数 $E$ 对全部状态满足 $E(K\psi)\le E(\psi)$，则实际上对全部状态有 $E(K\psi)=E(\psi)$。结论也适用于密度算子的 $\rho\mapsto K\rho K^\dagger$。

**证明。**

$$
E(\psi)=E(K^{10}\psi)\le E(K^9\psi)\le\cdots
\le E(K\psi)\le E(\psi).
$$

首尾相等迫使每项相等。证明不需连续性或可微性。

∎

一般酉门还满足 $\left\lVert U\psi-U\phi\right\rVert=\left\lVert \psi-\phi\right\rVert$，因此不是含不同状态空间上的严格压缩。量子递归可以有干涉、周期和可逆转动。测量、遗忘、耗散或另一个优化求解器可以引入下降，但那已经增加了映射与资源。

因此本轮核心等价应理解为：**整段递归历史可以是静态相容泛函的最小元，而不是每个门作用都把同一个状态能量降得更低。**

<a id="sec-12"></a>

## 12. 五模式耗散的真正变分身份

沿第 3 节固定内部纤维，令 $D(\kappa)=D(p(\kappa)\Vert p_*)$，

$$
a=\kappa(R-X-Y+\kappa),\quad b=(X-\kappa)(Y-\kappa),
\quad D'(\kappa)=\log(a/b).
$$

定义对数平均

$$
\Lambda(a,b)=\begin{cases}(a-b)/(\log a-\log b),&a\ne b,\\a,&a=b,
\end{cases}\quad M(\kappa)=\gamma\Lambda(a,b)>0,
$$

其中 $\gamma>0$。项目质量作用流就是

$$
\dot\kappa=\gamma(b-a)=-M(\kappa)D'(\kappa)
=-\gamma R(\kappa-\kappa_*).
$$

<a id="statement-12-1"></a>

#### 定理 12.1（局部变分与完整能量耗散身份）

对固定内部 $\kappa$，速度 $\dot\kappa$ 是

$$
\min_v\left\{\frac{v^2}{2M(\kappa)}+D'(\kappa)v\right\}
$$

的唯一解。对内部绝对连续路径、下式各项可积时，有

$$
D(\kappa_T)-D(\kappa_0)
+\frac{1}{2}\int_0^T\left[\frac{\dot\kappa^2}{M}
+M(D')^2\right]du
$$

<a id="equation-9"></a>

$$
=\frac{1}{2}\int_0^T\frac{(\dot\kappa+MD')^2}{M}\,du\ge0.
\tag{9}
$$

等号当且仅当该路径几乎处处满足质量作用流。

**证明。**

局部二次式的导数为 $v/M+D'$，二阶导 $1/M>0$。全局式展开右侧平方，交叉项积分为 $\int\dot\kappa D' du=D(\kappa_T)-D(\kappa_0)$；非负平方和为零等价于流方程。

∎

这使“递归耗散 = 变分”有了明确含义：目标与 mobility 一起指定，零缺陷轨迹由耗散身份刻画。该结构属于 Onsager／广义梯度系统传统 （[6](#ref-mielke)）。它不证明每个确定性反应模型自动是原生量子仪器或物理热浴。

<a id="statement-12-2"></a>

#### 命题 12.2（同端点二次动作给出不同答案）

固定合法端点和 $T>0$，对绝对连续路径

$$
\mathcal A[\kappa]=\frac{1}{2}\int_0^T\dot\kappa^2du
\ge\frac{(\kappa_T-\kappa_0)^2}{2T},
$$

唯一等号路径为仿射插值。若 $\alpha=\gamma R>0$ 且 $\kappa_0\ne\kappa_*$，指数流与同端点仿射路径满足

$$
\frac{\mathcal A_{\exp}}{\mathcal A_{\rm affine}}
=\frac{\alpha T}{2}\coth\frac{\alpha T}{2}>1.
$$

**证明。**

由端点差等于导数积分，Cauchy–Schwarz 得下界，等号要求导数几乎处处为常数。指数流导数为 $-\alpha(\kappa_0-\kappa_*)e^{-\alpha u}$，积分得
$\mathcal A_{\exp}=(\kappa_0-\kappa_*)^2\alpha(1-e^{-2\alpha T})/4$；除以对应端点差的仿射作用得到比值。对 $x>0$，$x\cosh x-\sinh x>0$，因为导数为 $x\sinh x>0$，故 $x\coth x>1$。平衡或零速率时两作用均零，比例不定义。

∎

<a id="sec-13"></a>

## 13. 量子实时间是驻作用，虚时间才是此能量下降

<a id="statement-13-1"></a>

#### 定理 13.1（Schrödinger 驻作用）

有限维 Hermitian $H$ 下，在全部复向量路径上考虑固定端点的实作用

$$
\mathcal S[\psi]=\int_0^T\left[
\frac{i\hbar}{2}(\langle\psi,\dot\psi\rangle-
\langle\dot\psi,\psi\rangle)-\langle\psi,H\psi\rangle\right]du
$$

对所有内部变分驻定，当且仅当 $i\hbar\dot\psi=H\psi$。

**证明。**

对共轭分量与原分量变分并分部积分，端点项为零，得到
$\delta\mathcal S=2\operatorname{Re}\int\langle\delta\psi,(i\hbar\partial_u-H)\psi\rangle du$。任意紧支撑变分的基本引理给方程，反向直接代入。

∎

驻定一般不是极小。取 $H=0$、单位正交 $b,v$、端点为零的实光滑 $f$，令

$$
\psi_\epsilon(u)=\sqrt{1-\epsilon^2f(u)^2}\,b
+\epsilon f(u)e^{i\omega u}v.
$$

这里驻值定理先使用不限制逐点范数的内部变分；若逐点限制归一化，方程可多出可吸收到整体相位的实乘子。对足够小 $\epsilon$，上述反例路径归一且端点仍为 $b$，但直接代入给

$$
\mathcal S[\psi_\epsilon]-\mathcal S[b]
=-\hbar\epsilon^2\omega\int_0^Tf^2du.
$$

取正、负 $\omega$ 得两种符号，故常值 Schrödinger 解是鞍型驻点。

<a id="statement-13-2"></a>

#### 命题 13.2（归一化虚时间的能量下降）

令 $E=\langle\psi,H\psi\rangle$，$\left\lVert \psi\right\rVert=1$，定义

$$
\partial_\tau\psi=-(H-E)\psi.
$$

则范数保持且 $\partial_\tau E=-2\operatorname{Var}_\psi(H)\le0$。

**证明。**

范数导数为 $-2\langle H-E\rangle=0$；能量导数为
$2\operatorname{Re}\langle\partial_\tau\psi,H\psi\rangle =-2(\langle H^2\rangle-E^2)$。谱分解表明只有初态含非零基态分量时才收敛到初态基态投影的归一化；否则趋于初态在其支持中最低能级上的投影归一化。

∎

项目[《统一预测几何》](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md) §1.3 已有实时间与虚时间的区别；量子变分模拟的不同原理也须区分 （[7](#ref-yuan)）。复结构可以在给定 Hilbert 几何中把梯度方向转成 Hamilton 方向，但“有变分”本身没有唯一强迫复数域和 Born 平方律。

<a id="sec-14"></a>

## 14. 黄金门优化：下确界为零却没有有限最小元

采用前稿 v15 的单逻辑位码

$$
J|q\rangle=|1\,0\,q\,0\,1\,0\rangle.
$$

两个固定地址上的 $K_P,K_Q$ 精确保码，码内投影分别为

$$
P=|1\rangle\langle1|,\qquad
Q=\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\
\varphi^{-3/2}&\varphi^{-2}\end{pmatrix}.
$$

v15 给出其射影群稠密性：两个五次幂反射之积的迹为 $4-2\sqrt5$，共轭 $4+2\sqrt5>2$ 排除有限阶；所得实转动圆及 $K_P$ 共轭后的不同轴生成 $SU(2)$。这一单比特码结论不依赖多体编织稠密性外部定理。完整证明见[前稿 v15 第 4–5 节](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)；本轮并未把收录行为视为重新认证。

设 $\mathcal W_L$ 为上述两地址门的长度至多 $L$ 的正字，$X$ 为逻辑取反，定义

$$
e_L=\min_{C\in\mathcal W_L}\min_{\theta\in\mathbb{R}/(2\pi\mathbb Z)}
\left\lVert CJ-e^{i\theta}JX\right\rVert_{\rm op}.
$$

<a id="statement-14-1"></a>

#### 定理 14.1（有限预算最优与无穷下确界）

$$
e_L>0,\qquad e_{L+1}\le e_L,\qquad \lim_{L\to\infty}e_L=0.
$$

因此全部有限字上误差的下确界是零，但没有达到它的有限字。这里不声称每层严格下降，也不声称最优编译有效率。

**证明。**

下一定理给每个有限 $L$ 的严格正下界。有限字集合和紧相位圆保证每层最小值存在。集合嵌套给单调性。前述射影稠密性给任意精度的群字，而 $K^{-1}=K^9$ 把逆门换成有限正字，因此误差趋零。

∎

下面的定量推论是本轮从固定门代数结构进一步得到的纸面结果。

<a id="statement-14-2"></a>

<a id="thm-paritybound"></a>

#### 定理 14.2（奇偶残留与门长下界）

令 $\Gamma=\varphi^3+\sqrt{\varphi^6-1}<9$。任意由 $\ell$ 个固定 $K$ 门组成的纯酉字，从一个物理计算基输入出发，输出中*与输入相同 Hamming 奇偶性*的总概率 $q$ 满足

$$
q\ge \frac{2}{1+\Gamma^\ell}\ge \frac{2}{1+9^\ell}.
$$

因而上述固定码、固定菜单的逻辑 $X$ 优化满足

$$
\boxed{e_L\ge\sqrt{\frac{2}{1+\Gamma^L}}.}
$$

若要求 $e_L\le\epsilon<1$，必要条件为

$$
L\ge \frac{\log(2\epsilon^{-2}-1)}{\log\Gamma}.
$$

此界针对纯单位门字、固定基输入与该码；不覆盖归一化后选择、外供非基态或更换编码。

**证明。**

置 $\beta=\varphi^{-1/2}$、$t=\beta^2=\varphi^{-1}$、$F_0=\mathbb Q(\zeta)$、$R_0=\mathbb Z[\zeta]$。因

$$
t=-(\zeta+\zeta^{-1})\in R_0,\qquad \beta^4+\beta^2-1=0,
$$

$\beta$ 是代数整数。固定三位门的唯一非对角转移为 $000\leftrightarrow010$，其投影块为

$$
\begin{pmatrix}t&\beta^3\\\beta^3&t^2\end{pmatrix}.
$$

邻居均为一时投影为恒等，混合邻居时为零。故门的保奇偶矩阵元在 $R_0$，翻奇偶矩阵元在 $\beta R_0$。因为 $\beta^2\in R_0$，矩阵乘法保留此二分级。

固定基输入 $x$，将相反奇偶输出振幅写为 $C_{yx}=\beta c_y$、$c_y\in R_0$。相反奇偶总概率

$$
p=t\sum_y c_y\overline{c_y}
$$

属于 $F_0$ 的实子域 $\mathbb Q(\sqrt5)$，且为代数整数。取自同构 $\sigma(\zeta)=\zeta^3$；它在 $F_0$ 与复共轭交换，且 $\sigma(t)=-\varphi$。因此非平凡实共轭为

$$
p'=\sigma(p)=-\varphi\sum_y|\sigma(c_y)|^2\le0.
$$

若 $p=1$ 则其共轭也为一，矛盾。物理酉性给 $0\le p<1$，所以 $q=1-p>0$，而 $q'=1-p'\ge1$。实二次数域范数 $qq'$ 是正整数，故 $qq'\ge1$；即使 $q$ 为有理数，此范数论证仍成立。

把 $\sigma$ 延拓为 $F_0(\beta)$ 的复嵌入 $\widetilde\sigma$，必有
$\widetilde\sigma(\beta)=\pm i\sqrt\varphi$。变换后的活动投影块的 Frobenius 范数为

$$
\sqrt{\varphi^2+2\varphi^3+\varphi^4}=\varphi^3.
$$

为精确估计单门，记 $u=\sigma(\zeta)$、$P'=\widetilde\sigma(P_{\rm active})$、
$A'=u[I+(u-1)P']$。由 $\operatorname{Tr} P'=1$、
$u+\bar u=\varphi$、$|u-1|^2=\varphi^{-2}$，

$$
\left\lVert A'\right\rVert_F^2
=2+(u+\bar u-2)\operatorname{Tr} P'+|u-1|^2\left\lVert P'\right\rVert_F^2
=\varphi+\varphi^4=2\varphi^3.
$$

$P'$ 仍是迹一的幂等矩阵，故 $\det A'=u^3$、$|\det A'|=1$。
两个奇异值平方的和为 $2\varphi^3$、积为一，因此最大值为 $\Gamma$。
其余物理块都是模一标量，所以 $\left\lVert \widetilde\sigma(K)\right\rVert^2=\Gamma$；
并且 $\Gamma<2\varphi^3=4\varphi+2<9$。

扩张不必与整个扩域的复共轭交换；这里只对 $R_0$ 中的系数使用交换性。
同奇偶振幅在 $R_0$，故其变换后的模平方和为 $q'$；
相反奇偶振幅的变换模平方和为 $-p'=q'-1$。因此有更强的精确身份

$$
\left\lVert \widetilde\sigma(C)|x\rangle\right\rVert^2=2q'-1\le\Gamma^\ell.
$$

于是 $q'\le(1+\Gamma^\ell)/2$，结合 $qq'\ge1$ 得所列概率下界。

码字 $|10b010\rangle$ 的物理 Hamming 重量为 $2+b$，$b\in\{0,1\}$。
逻辑 $X$ 把每个码基态送到相反奇偶，任何整体相位都不改变这一事实。
将向量误差投影到原奇偶子空间，理想项为零而实际项范数为 $\sqrt q$；
故算子误差至少为 $\sqrt q$。这保留完整物理输出，已包括同奇偶泄漏。
对全部 $\ell\le L$ 取最小即得 $e_L$ 的界，再移项取对数。

∎

该定理不是“物理奇偶守恒”：单个 $K$ 确实混合奇偶。它说有限精确字不能把某一基输入的同奇偶残留全部消掉。代数共轭中的负号是证明工具，不能解释为负物理概率。稠密闭包仍可出现零残留极限，故与普适近似相容。

<a id="sec-15"></a>

## 15. 可以保留的统一命题与研究边界

现在可以把最初的等号分成一组可检验的数学对应。

| 对象 | 严格对应 | 必须保留的条件 |
| --- | --- | --- |
| 有限路径规划 | Bellman = 路径最优 = 流最小化 = 势对偶 | 有限 DAG、完整状态、真实边代价、终止 |
| 正权路径谱 | Gibbs 变分 = 软递归 = 切面配分 | 参考律、正温度、同一完整路径空间 |
| 黄金合法语言 | Fibonacci 递归 = Perron 增长 = 熵率上界 | 禁 $11$、权重、平稳性及最大熵目标 |
| 线性相干预测 | 局部递归 = 唯一零残差最小元 = 驻点 | 有限 DAG、复线性结构、正定内积权重 |
| 黄金门历史 | 电路相容 = 正传播算子的零能态 | 指定门、输入与地址寄存器 |
| 纤维耗散 | 质量作用流 = 能量耗散身份取等 | 指定自由能、mobility、边界与可积性 |
| 实时间量子态 | Schrödinger 方程 = 驻作用 | Hermitian 生成元、复结构、允许变分 |
| 有限门编译 | 预算最优误差递减至下确界 | 固定码、菜单、精度及资源；未必达到 |

**统一命题。** 在指定相容关系、边界、评分和资源之后，预测可以解释为完整结构的可辨识完成；递归是它的局部合成方式；在上述结构类中，变分给出同一解的全局表达。最小元、驻点与仅在闭包中达到的下确界则必须分别证明。

这也给“观察者内生”一个可工作的定义：观察者是结构中的记录、记忆、控制与预测读出子系统，其状态必须连同实际来源和代价一并纳入相容问题。观察者可以改变切面或进行内部消元，但不能省掉共享来源关系、非交换次序、校准或停止资源，再宣称所得预测仍属于同一个问题。

最值得继续研究的三个具体问题是：第一，哪些项目原生相容与对称条件能够选择特定参考律和度量，而非仅允许大量残差泛函；第二，怎样在完整记录与实际门菜单下实现这些变分求解，并给总工作、制备和读出成本；第三，能否在固定编码上把定理 [14.2](#thm-paritybound) 的长度下界与构造性上界接近起来。上述问题没有由本轮的表示等价自动解决，也不产生 $P=NP$ 或其反命题的证明。

<a id="sec-bibliography"></a>

## 文献与项目来源

<a id="ref-bellman"></a>

1. R. Bellman. *The Theory of Dynamic Programming*. Bulletin of the American Mathematical Society 60 (1954), 503–515. [DOI: 10.1090/S0002-9904-1954-09848-8](https://doi.org/10.1090/S0002-9904-1954-09848-8). 本文有限 DAG 结论已给自足证明；项目 KL 原卷亦已有有限势证书。

<a id="ref-todorov"></a>

2. E. Todorov. *Linearly-solvable Markov decision problems*. NIPS 2006. [原论文](https://papers.nips.cc/paper_files/paper/2006/file/d806ca13ca3449af72a1ea5aedbed26a-Paper.pdf)。KL 控制成本与指数变换的背景；本文不迁移其特定效率结论。

<a id="ref-parry"></a>

3. W. Parry. *Intrinsic Markov Chains*. Transactions of the American Mathematical Society 112 (1964), 55–66. [DOI: 10.1090/S0002-9947-1964-0161372-1](https://doi.org/10.1090/S0002-9947-1964-0161372-1). 本轮核对原论文全文转录；黄金二状态特例另附完整证明。

<a id="ref-gneiting"></a>

4. T. Gneiting and A. E. Raftery. *Strictly Proper Scoring Rules, Prediction, and Estimation*. JASA 102 (2007), 359–378. [作者提供的原论文](https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf)。

<a id="ref-aharonov"></a>

5. D. Aharonov, W. van Dam, J. Kempe, Z. Landau, S. Lloyd, O. Regev. *Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation*. [arXiv:quant-ph/0405098](https://arxiv.org/abs/quant-ph/0405098). 历史态及传播 Hamiltonian 的先行背景。

<a id="ref-mielke"></a>

6. A. Mielke, M. A. Peletier, D. R. M. Renger. *A generalization of Onsager's reciprocity relations to gradient flows with nonlinear mobility*. [arXiv:1510.06219](https://arxiv.org/abs/1510.06219). 局部速度变分及能量耗散结构的背景。

<a id="ref-yuan"></a>

7. X. Yuan, S. Endo, Q. Zhao, Y. Li, S. C. Benjamin. *Theory of variational quantum simulation*. Quantum 3, 191 (2019). [arXiv:1812.08767](https://arxiv.org/abs/1812.08767). 区分静态、实时间与虚时间变分。

<a id="ref-repo"></a>

8. *trureturing*, `dev` 快照 `f22ccafb22873bb5445053498b0f64f9ea111ede`. [不可变理论目录](https://github.com/the-omega-institute/trureturing/tree/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory)。本文各处的项目标题链接指向该快照；理论正文与形式证明身份分开。

<a id="ref-v15"></a>

9. *黄金门的 NAND 式普适性与精确实现的算术边界*, v15.0. [项目中的前稿转换正文](https://github.com/the-omega-institute/trureturing/blob/f22ccafb22873bb5445053498b0f64f9ea111ede/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)。历史研究快照为 `52ce13dc…`；前稿回流不构成独立认证。
