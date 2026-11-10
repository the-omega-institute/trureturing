# 正交时间场论 OTF-001：方向、转向、读出与内禀时钟

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。图示以文内文字和公式呈现。

OTF RESEARCH SERIES / 001 / VERSION 1.0

正交时间场论

方向、转向、读出与内禀时钟

Orthogonal Time-Field Theory\
A finite-dimensional theory of relations, rotations,\
operational readouts, and internal clocks

**研究对象** 从用户提供的“各向同性时间场”构想出发，建立可逐条核验的 几何核心、量子操作扩展、内生观察者模型与静态历史表示。

**本稿的完成范围** 有限维二能级端口及其明确指定的复合系统。 本文给出完整定义、条件、证明、反例和可计算实例。 空间维数、物理质量、相对论动力学及单次结果的本体选择不由这些条件自动确定。

**学术定位** 本稿对既有几何量子力学和有限维量子操作作关系化组织， 明确指出每项桥接所需的假设；不将标准定理改称新发现。

2026 年 11 月 7 日\
根据本轮附件整理；关联 trureturing 项目的有界源码核对。 本稿未声称已经经过期刊同行评审或 Lean 形式化验证。

## 摘要

本文把“状态为方向、门为转向、观察者内生”的构想发展为一个有限维公理化模型。 首先在定向三维 Euclidean 空间中证明二元关系的内积与楔积分解， 区分端点关系、半角旋转元及路径复合，并刻画稳定子自由度、 对径退化与全局连续选门的障碍。其次，在球状混合状态空间上， 由概率的仿射性与尖锐端点条件唯一推出二能级 Born 规则， 继而构造 Pauli 表示、可逆动力学、测量仪器与不确定性恒等式。 对于指定两路径实验，给出可预测性、干涉可见度和含侧信息的可区分度的严格关系。 在时间部分，定义重参数不变的量子变化长度， 证明它与 Fubini–Study 长度及能量不确定度的关系， 同时证明余弦投影不能充当全局累加时钟。 通过有限传播约束构造静态全局历史态； 加上明确的输入约束后，该态可以是唯一零能态，而内部条件读出仍显示演化。 最后给出观察响应商、复合关系的相容性条件、方向场的曲率及正矩阵锥的 Lorentz 型结构。 主要贡献在于将直观统一叙述转化为假设透明、退化情形完整、 可接入 AURIC 静态相融框架的正式理论版本。

**关键词：** Clifford 代数；Bloch 球；Born 规则；几何相位；量子时钟； 内生观察者；相容性；静态历史。

## 目录

- [1　理论任务、逻辑层级与符号](#section-1)
- [2　完整公理候选 OTF-001](#section-2)
- [3　二元正交分解与真正的旋转门](#section-3)
- [4　三维自对偶、复结构与全局相容性](#section-4)
- [5　从混合一致性到 Born 读出](#section-5)
- [6　可逆演化、生成元与不确定性](#section-6)
- [7　复合端口、测量更新与实际记录](#section-7)
- [8　线与面积互补的实验定义](#section-8)
- [9　内禀变化长度、能量与历史切向](#section-9)
- [10　闭环历史、几何相位与方向场](#section-10)
- [11　内生观察者、响应商与记忆](#section-11)
- [12　静态整体中的内禀时钟](#section-12)
- [13　与时空结构的一个严格代数桥梁](#section-13)
- [14　完整有限协议、具体动力学与闭合性](#section-14)
- [15　AURIC 接口、假设审计与研究边界](#section-15)
- [16　完整候选的白话表述](#section-16)
- [A　退化情形与使用约定清单](#section-A)
- [B　构建与引用说明](#section-B)

<a id="section-1"></a>

## 1　理论任务、逻辑层级与符号

### 1.1　本稿要完成什么

原始构想的核心是：一个局部状态可以表现为方向；两个状态之间的关系 产生投影和有向转向；门、观察、记忆及时钟属于同一个整体。 本文把这三项直觉转化为具体数学对象，而不把“有几何图像” 等同于“已推出所有物理定律”。

我们区分三个层级。

1.  **几何层 G：** 单位方向、内积、楔积、旋转、路径和联络。

2.  **操作层 Q：** 混合制备、概率、复合系统、完全正仪器和实际记录。

3.  **内生层 I：** 观察者、时钟和记忆作为整体中的端口与关系约束。

G 的恒等式可以独立成立。G 到 Q 需要操作假设； Q 到 I 可以给出显式模型。将 I 解释成整个物理宇宙， 还需要决定哪些模型对应实验、哪些参数对应物理单位。

### 1.2　“内生”的精确定义

#### 定义 1.1：结构内生性

相对于一个给定模型 $\mathfrak M$，若某对象、操作或记录能够表示为 $\mathfrak M$ 内部的子系统、态、映射或关系约束，则称它对该模型内生。 若所有使用的测量器、记忆与时钟均如此表示，称模型满足观察结构内生性。

此定义排除了未建模的物理观察装置，但不排除数学上必须声明的模型条件。 “所有约束作用于内部对象”与“这些约束是唯一逻辑可能”是不同命题。 后者必须排除反模型，而不能仅通过把假设改名为定义来成立。

### 1.3　基本约定

取定向实内积空间 $V\simeq\mathbb R^3$， $S^2=\{n\in V:\left\|n\right\|=1\}$， $B^3=\{r\in V:\left\|r\right\|\leq1\}$。 定向确定叉积与 Hodge 对偶，但不预先宣称物理世界存在优先手性。 符号 $\Omega_{\rm str}$ 表示包含关系、端口与记录的整体结构； $|\Omega_N\rangle$ 表示后文构造的一个全局历史态； 双矢量用 $W$ 或 $\Theta$，避免把不同类型对象全部记成 $\Omega$。

| 符号               | 含义及类型                                       |
|:-------------------|:-------------------------------------------------|
| $n,m\in S^2$     | 一个二能级纯态的 Bloch 方向、一个二值测试的轴    |
| $r\in B^3$       | 混合态的 Bloch 向量                              |
| $n\wedge m$      | 内部空间的双矢量，不是概率，也不是基流形的二形式 |
| $R,\ U$          | 分别为 Clifford 旋转元及其 $SU(2)$ 表示        |
| $\rho,\ E$       | 密度矩阵与效果算子                               |
| $q[\gamma]$      | 无量纲的量子变化长度                             |
| $\tau_{\rm rec}$ | 对已声明计数事件的加权记录时钟                   |
| $F$              | 射线相位联络的曲率二形式                         |

<a id="section-2"></a>

## 2　完整公理候选 OTF-001

下列条件共同定义本轮候选。它们既给出一个非空模型类， 也表明哪些物理结构确实被作为输入。

#### 假设 2.1：G：局部方向几何

基本方向端口使用一个定向三维正定实内积空间。 纯状态以 $S^2$ 参数化，公共坐标改变不改变可观测预测。 几何运算使用该空间的外代数和 Clifford 代数。

#### 假设 2.2：M：混合与操作等价

所有有限随机混合均允许；混合后的端口状态由 $r=\sum_jp_jn_j$ 决定。 具有相同 $r$ 的制备，对该端口的所有测试操作等价。 状态空间是 $B^3$，测试概率对混合是仿射函数。

#### 假设 2.3：S：尖锐二值读出

每个 $m\in S^2$ 对应一个二值测试。 其“$+$”概率 $p_m:B^3\to[0,1]$ 满足 $p_m(m)=1$、$p_m(-m)=0$，另一结果概率为 $1-p_m(r)$。

#### 假设 2.4：R：可逆连续控制

允许的基本可逆方向变换为球的所有定向仿射自同构， 实际连续控制由这些变换的连续、分段 $C^1$ 路径给出。 其旋转元提升在选定初值后连续；路径信息在组合时保留。 对特殊任务的受限控制菜单，必须另行明确删去哪些变换。

#### 假设 2.5：C：复合的量子正性

在基本端口的矩阵表示建立后，复合端口使用复张量积； 联合效果是全部 $0\leq E\leq I$ 的矩阵。 联合操作态定义为这组效果上的归一正可加概率泛函； 允许所有这样的泛函，下面证明它们恰由正半定、迹一矩阵表示。 局部操作线性延拓后，在任意有限辅助端口存在时仍保持正性。 这是一项复合系统假设，不由单个球的几何推得。

#### 假设 2.6：J：仪器与理想重复读出

一次仪器由有限个完全正分支组成，其和保迹。 结果通过指定记录端口保存；未被记录的形式分支不自动成为事实记录。 若称二值秩一读出为“理想”，额外要求其结果立即重复时不变。

#### 假设 2.7：I：内生记录及有限历史

系统、测量器、记忆、辅助端口和时钟都属于同一个有限整体。 一项实验由有限因果关系和有限深度仪器协议指定； 初始资料及控制规则作为整体的已声明关系。 若使用累加记录时钟，则对计数事件赋予正权重，并显式保留其顺序或偏序。

#### 注 2.8

由 M、S 将推出概率公式，故基本二值 Born 规则没有重复写入公理。 但 C 明确选择量子复合结构，J 明确选择仪器类型。 R 也没有从“存在”推出具体 Hamiltonian。 这份候选是透明的有限维量子关系模型，而不是没有物理输入的唯一宇宙论。

<a id="section-3"></a>

## 3　二元正交分解与真正的旋转门

#### 定义 3.1：有序二元几何关系

对 $a,b\in S^2$，定义

$$
c=a\cdot b,\qquad b_\parallel=ca,\qquad
b_\perp=b-ca,\qquad W_{ab}=a\wedge b.
$$

在 $\operatorname{Cl}_{3,0}$ 中采用 $xy+yx=2x\cdot y$， 定义端点关系 $Q_{ab}=ab=c+W_{ab}$。

#### 定理 3.2：分解与守恒

上述分解唯一，且

$$
a\cdot b_\perp=0,\qquad
\left\|b_\perp\right\|^2=\left\|W_{ab}\right\|^2=1-c^2,\qquad
W_{ab}^2=-(1-c^2).
$$

若 $0<\theta=\arccos c<\pi$， $I_{ab}=W_{ab}/\sin\theta$ 满足

$$
I_{ab}^2=-1,\qquad Q_{ab}=\cos\theta+I_{ab}\sin\theta.
$$

**证明。**

正交投影给唯一分解。计算 $\left\|b-ca\right\|^2=1-2c^2+c^2=1-c^2$。 若 $b=\pm a$，则 $b_\perp=W_{ab}=0$，各式直接成立。 以下设 $b\ne\pm a$。 取平面正交基 $a,u=b_\perp/\left\|b_\perp\right\|$， 有 $W_{ab}=\sin\theta\,au$； 由 $ua=-au$ 及 $a^2=u^2=1$， $(au)^2=-1$。其余式子随即成立。

$\square$

**图示：二元关系中的平行分量与楔积。** 阴影是两向量张成的平行四边形，其面积为 $\sin\theta$；它与角度 $\theta$、球面包围面积是不同量。

原图以文字和公式表示如下：两个单位方向 $a,b$ 从共同原点 $0$ 出发，夹角为 $\theta$。$b$ 沿 $a$ 的投影点为 $C=ca$，其中 $c=a\cdot b$；垂直分量为 $b_\perp=b-ca$，且 $a\cdot b_\perp=0$。平行四边形面积满足 $\lVert a\wedge b\rVert=\sin\theta$。

#### 定理 3.3：半角最短旋转元

设 $b\ne-a$，则

$$
\boxed{R_{ab}=\frac{1+ba}{\sqrt{2(1+a\cdot b)}}}
$$

满足 $R_{ab}\widetilde R_{ab}=1$、 $R_{ab}a\widetilde R_{ab}=b$。 当 $a\ne b$ 时， $R_{ab}=\exp(-I_{ab}\theta/2)$。 这里 $\widetilde{\phantom R}$ 为反序，采用夹心作用 $x\mapsto Rx\widetilde R$； 旋转元指 $\operatorname{Spin}(3)\subset\operatorname{Cl}_{3,0}^{+}$ 中的单位偶元素。

**证明。**

由 $ab+ba=2c$，

$$
(1+ba)(1+ab)=2(1+c).
$$

又 $(1+ba)a=a+b=b(1+ba)$，归一后得 $Ra=bR$， 右乘 $\widetilde R$ 即得结论。 用 $1+\cos\theta=2\cos^2(\theta/2)$ 与 $\sin\theta=2\sin(\theta/2)\cos(\theta/2)$ 即得指数式。 对于 $a\ne b$，连续旋转元 $R(t)=\exp(-tI_{ab}\theta/2)$ 的方向轨迹为 $n(t)=\cos(t\theta)a+\sin(t\theta)u$，$0\leq t\leq1$， 其中 $u=b_\perp/\|b_\perp\|$。 其长度为端点球面距离 $\theta$，故为最短弧；同向时取常值路径。

$\square$

#### 命题 3.4：端点不能唯一确定整个门

令 $J=e_1e_2e_3$。所有将 $a$ 送到 $b\ne-a$ 的旋转元均为

$$
S=R_{ab}\exp(-Ja\phi/2),\qquad \phi\pmod{4\pi}.
$$

当 $b=-a$ 时，任意单位 $u\perp a$ 给出一个解 $R=-au$。

**证明。**

若 $Sa\widetilde S=b$，则 $T=\widetilde R_{ab}S$ 固定 $a$。 固定一条方向的三维旋转正是绕该方向的旋转， 其旋量提升为 $\exp(-Ja\phi/2)$。 反过来这些 $T$ 确实固定 $a$。 对于对径情形，直接计算 $(-au)a(au)=-a$。

$\square$

因此，有向面积给出转向平面， *门还需要转角、半角作用约定和稳定子选择* 。 特别地 $a\wedge(-a)=0$，却必须发生半周转动。 将“楔积面积为零”解释成“一定没有演化”会漏掉这一边界。 右乘等式 $a(ab)=b$ 只描述指定输入； 对 $a=e_1,b=e_2$，右乘使 $e_3(ab)=J$，已经不是向量。

#### 定理 3.5：不能在全部端点对上连续选门

不存在连续映射 $F:S^2\times S^2\to SO(3)$ 使 $F(a,b)a=b$ 对所有 $(a,b)$ 成立。

**证明。**

固定 $a_0$ 与单位 $u_0\perp a_0$。 若 $F$ 存在，$u(b)=F(a_0,b)u_0$ 是球面上的连续单位切向场。 于是 $H(b,t)=\cos(\pi t)b+\sin(\pi t)u(b)$ 是恒等映射到对径映射的同伦。 这两个 $S^2$ 映射的度分别为 $1$ 和 $-1$，矛盾。

$\square$

<a id="section-4"></a>

## 4　三维自对偶、复结构与全局相容性

#### 定理 4.1：线与全部二面积的自对偶维数

若非零有限维实向量空间 $V$ 满足线性同构 $V\simeq\Lambda^2V$，则 $\dim V=3$。 反之，定向三维内积空间的 Hodge 星给出该等距同构。

**证明。**

令 $n=\dim V>0$。维数相等要求 $n=n(n-1)/2$，故 $n=3$。 在定向正交基中， $\star(e_1\wedge e_2)=e_3$ 及循环置换给出反向构造。

$\square$

“全部线与全部面积一一对应”是一项强条件。 各向同性本身对 $S^{n-1}$ 的任意 $n$ 都成立，不能单独选择 $n=3$。 三维 Bloch 方向也不是三维物理位置空间的证明。

#### 命题 4.2：局部复平面与中心复标量

每个单位简单双矢量 $I$ 生成 $\operatorname{span}_{\mathbb R}\{1,I\}\simeq\mathbb C$。 不同平面的这种子代数一般不对易。 在 $\operatorname{Cl}_{3,0}$ 中，$J=e_1e_2e_3$ 为中心元且 $J^2=-1$； Pauli 表示满足 $J\mapsto\mathrm i\mathbf 1$， $e_1e_2\mapsto\mathrm i\sigma_3$。

**证明。**

$I^2=-1$ 给第一项。 例如 $[e_1e_2,e_2e_3]=2e_1e_3\ne0$。 $J$ 与三个基向量都对易，且 $J^2=(-1)^3=-1$。 Pauli 乘法律 $\sigma_j\sigma_k=\delta_{jk}\mathbf 1+ \mathrm i\epsilon_{jk\ell}\sigma_\ell$ 给出最后两式。

$\square$

故“转向平面具有复数代数”成立， “所有平面的面积元都是同一个中心标量 $\mathrm i$”不成立。 完整 Clifford 代数作为实代数同构于 $M_2(\mathbb C)$： 上述表示保持关系，且两侧实维数同为八，八个基像线性独立。

#### 定理 4.3：有限方向关系的全局实现条件

实对称矩阵 $G=(g_{ij})_{i,j=1}^N$ 是一组 $\mathbb R^3$ 单位向量的 Gram 矩阵，当且仅当

$$
G\succeq0,\qquad g_{ii}=1,\qquad \operatorname{rank}G\leq3.
$$

**证明。**

若 $g_{ij}=n_i\cdot n_j$，对任意实数列 $x$， $x^TGx=\left\|\sum_ix_in_i\right\|^2\geq0$； 对角线与秩条件显然。 反之，对正半定 $G$ 作谱分解，取至多三个非零特征值的平方根， 得到 $G=X^TX$，将 $X$ 补零为三行；其列即所需单位向量。

$\square$

对三个单位方向，设成对内积为 $x,y,z$， 相容条件包含

$$
1+2xyz-x^2-y^2-z^2\geq0.
$$

该行列式等于三重积的平方； 非零时仍留下整体镜像的符号选择。

#### 反例 4.4：每个三元可实现，不保证整体三维可实现

$G=I_4$ 的每个三阶主子矩阵都能由 $\mathbb R^3$ 正交基实现， 但 $G$ 自身秩为四，不能由四个 $\mathbb R^3$ 向量实现。

二元和三元关系的递归检查因此还需要全局正性、秩及共同嵌入条件。 这也是“局部相融”与“整个结构相融”之间必须保留的数学差别。

<a id="section-5"></a>

## 5　从混合一致性到 Born 读出

#### 定理 5.1：球上尖锐仿射概率的唯一性

在 M、S 下，对每个 $m\in S^2$，

$$
\boxed{p_m(r)=\frac{1+m\cdot r}{2}.}
$$

公共旋转协变性 $p_{Om}(Or)=p_m(r)$ 随后自动成立。

**证明。**

球有非空内部，仿射函数可唯一写成 $p_m(r)=\alpha+b\cdot r$。 在整个球上取最小值、最大值，概率界等价于 $\left\|b\right\|\leq\min(\alpha,1-\alpha)$。 两端标定给 $\alpha+b\cdot m=1$、$\alpha-b\cdot m=0$， 因此 $\alpha=1/2$、$b\cdot m=1/2$。 由 Cauchy–Schwarz， $1/2\leq\left\|b\right\|\leq1/2$；等号条件迫使 $b=m/2$。 最后公共正交变换保持内积，故协变。

$\square$

#### 反例 5.2：各向同性本身没有唯一概率律

对任意整数 $k\geq1$，函数

$$
p_m^{(k)}(r)=\frac{1+(m\cdot r)^{2k+1}}2
$$

满足概率界、端点标定、互补性和公共旋转协变， 但不满足混合仿射性。 例如 $k=1$ 时，$p_m(m/2)=9/16$， 而混合一致性要求 $[p_m(m)+p_m(0)]/2=3/4$。

因此，概率规则的关键输入是制备混合的操作等价性。 不能仅由勾股恒等式或“所有方向平权”推出它。

#### 定义 5.3：矩阵表示

选一个定向正交标架，令

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-\mathrm i\\\mathrm i&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

定义

$$
\rho(r)=\tfrac12(\mathbf 1+r\cdot\boldsymbol{\sigma}),\qquad
P_m=\tfrac12(\mathbf 1+m\cdot\boldsymbol{\sigma}).
$$

#### 定理 5.4：二能级量子表示

$r\mapsto\rho(r)$ 是 $B^3$ 到所有二阶密度矩阵的仿射双射。 纯态恰对应 $\left\|r\right\|=1$，且

$$
\operatorname{tr}(\rho(r)P_m)=\frac{1+r\cdot m}{2}.
$$

若 $a,b\in S^2$ 的夹角为 $\theta$，则

$$
|\langle \psi_a|\psi_b\rangle|^2
=\operatorname{tr}(P_aP_b)=\cos^2(\theta/2).
$$

**证明。**

Pauli 关系给 $(r\cdot\boldsymbol{\sigma})^2=\left\|r\right\|^2\mathbf 1$， 故 $\rho(r)$ 的特征值为 $(1\pm\left\|r\right\|)/2$。 任意迹一 Hermitian 二阶矩阵在 $\{\mathbf 1,\sigma_1,\sigma_2,\sigma_3\}$ 基中唯一展开， 正性恰要求 $\left\|r\right\|\leq1$。 秩一恰要求 $\left\|r\right\|=1$。 利用 $\operatorname{tr}\sigma_j=0$、 $\operatorname{tr}(\sigma_j\sigma_k)=2\delta_{jk}$ 得到概率式。 最后写 $P_a=|\psi_a\rangle\langle \psi_a|$ 即得重叠公式。

$\square$

这一区分至关重要：Bloch 方向垂直，测试概率为 $1/2$； Bloch 方向反向，Hilbert 纯态才正交。 不能把三维向量夹角 $\theta$ 直接当成复射线距离。

#### 命题 5.5：全部基本效果的分类

所有仿射概率函数 $f:B^3\to[0,1]$ 恰为 $f(r)=\alpha+b\cdot r$， 其中 $\left\|b\right\|\leq\min(\alpha,1-\alpha)$。 它对应唯一效果 $E=\alpha\mathbf 1+b\cdot\boldsymbol{\sigma}$，满足 $0\leq E\leq\mathbf 1$ 及 $f(r)=\operatorname{tr}(\rho(r)E)$。

**证明。**

概率界与系数界的等价性已在定理 5.1 中计算。 $E$ 的特征值为 $\alpha\pm\left\|b\right\|$， 所以同一条件恰好是 $0\leq E\leq\mathbf 1$。 迹计算给配对公式及唯一性。

$\square$

#### 定理 5.6：全部效果上的概率表示

在有限维复空间上，若 $f$ 对全部效果非负， $f(\mathbf 1)=1$，并在 $E,F,E+F$ 都是效果时满足 $f(E+F)=f(E)+f(F)$， 则存在唯一密度矩阵 $\rho$ 使 $f(E)=\operatorname{tr}(\rho E)$。

**证明。**

有限可加性给有理数齐次性；正性给单调性， 用有理数从上下逼近，得到 $f(tE)=tf(E)$，$0\leq t\leq1$。 对正矩阵 $A$ 选 $c>0$ 且 $c\geq\left\|A\right\|$，定义 $\ell(A)=cf(A/c)$。齐次性保证定义与 $c$ 无关。 选共同充分大的 $c$，可证明正锥上的可加性与齐次性。 再以 $\ell(A-B)=\ell(A)-\ell(B)$ 延拓到自伴矩阵； 若 $A-B=A'-B'$，由 $A+B'=A'+B$ 知定义无歧义。 有限维迹内积给唯一自伴 $\rho$ 表示 $\ell$。 在所有秩一投影上非负说明 $\rho\succeq0$， 而 $f(\mathbf 1)=1$ 给 $\operatorname{tr}\rho=1$。

$\square$

此证明明确使用全部效果，而不仅是投影。 它适用于二维情形，与效果版本的概率表示研究相接 [\[1\]](#ref-Busch)。在复合端口上使用该定理，仍然依赖 C 所选择的矩阵效果空间。

<a id="section-6"></a>

## 6　可逆演化、生成元与不确定性

#### 定理 6.1：从球自同构到投影酉性

球 $B^3$ 的仿射自同构群为 $O(3)$， 恒等连通分支为 $SO(3)$。 每个 $O\in SO(3)$ 可由 $U\in SU(2)$ 实现：

$$
\rho(Or)=U\rho(r)U^\dagger.
$$

该实现恰有 $\pm U$ 两个 $SU(2)$ 选择。

**证明。**

仿射双射保持中心对称中心，而球的中心唯一，故它固定零点。 于是变换是线性 $A$。球面保持给 $r^TA^TAr=r^Tr$，极化得 $A^TA=I$。 行列式符号沿连续路径不变，$SO(3)$ 连通。 轴角为 $(u,\theta)$ 的旋转由 $U=\exp(-\mathrm i\theta u\cdot\boldsymbol{\sigma}/2)$ 实现； 直接用 Pauli 乘法律得到 Rodrigues 旋转公式。 若两个 $SU(2)$ 元实现相同作用，它们的比值与全部 Pauli 矩阵对易， 只能为标量；行列式一给标量 $\pm1$。

$\square$

#### 定理 6.2：微分生成元

设 $U(t)$ 是可微酉路径。令 $H(t)=\mathrm i\hbar\dot U(t)U(t)^\dagger$，其中 $\hbar>0$， 则 $H(t)$ 自伴，且

$$
\mathrm i\hbar\dot\psi=H(t)\psi,\qquad
\dot\rho=-\frac{\mathrm i}{\hbar}[H,\rho].
$$

对于 $H=h_0\mathbf 1+\frac{\hbar}{2}\omega\cdot\boldsymbol{\sigma}$， 有 $\dot r=\omega\times r$。

**证明。**

对 $UU^\dagger=I$ 求导， 得 $\dot UU^\dagger$ 反自伴，故 $H$ 自伴。 由定义代回 $\psi=U\psi_0$ 和 $\rho=U\rho_0U^\dagger$， 得到前两式。再用 $[a\cdot\boldsymbol{\sigma},b\cdot\boldsymbol{\sigma}]=2\mathrm i(a\times b)\cdot\boldsymbol{\sigma}$， 比较 Pauli 系数即得末式。

$\square$

这是“可微酉演化具有 Schrödinger 生成元”的定理， 不是“几何已唯一决定 $H$ 和 $\hbar$”的定理。 若再给单参数群律，则 $H$ 可取时间无关； 一般控制路径无需满足这一更强条件。

#### 定理 6.3：给定方向轨迹的最小转向

对 $C^1$ 路径 $n(t)\in S^2$，全部满足 $\dot n=\omega\times n$ 的角速度恰为

$$
\omega=n\times\dot n+\chi n.
$$

其范数满足 $\left\|\omega\right\|^2=\left\|\dot n\right\|^2+\chi^2$， 所以唯一最小范数选择为 $\chi=0$。

**证明。**

归一化给 $n\cdot\dot n=0$， 向量三重积给 $(n\times\dot n)\times n=\dot n$。 两个解的差与 $n$ 叉乘为零，故平行 $n$。 两项正交，再用勾股定理得范数式。

$\square$

这精确表达“状态与其切向关系产生最小门”。 沿 $n$ 的稳定子自由度影响其他输入态和相位历史， 所以一条已知方向轨迹不能确定整个控制协议。

#### 定理 6.4：二能级不确定性的精确三维恒等式

对单位 $u,v$，令 $X_u=u\cdot\boldsymbol{\sigma}$、$X_v=v\cdot\boldsymbol{\sigma}$， $a=u\cdot r$、$b=v\cdot r$、$c=u\cdot v$。 则

$$
\begin{aligned}
\operatorname{Var}(X_u)\operatorname{Var}(X_v)
={}&(c-ab)^2+\bigl[(u\times v)\cdot r\bigr]^2\\
&+(1-\left\|r\right\|^2)\left\|u\times v\right\|^2.
\end{aligned}
$$

特别地 $\operatorname{Var}(X_u)\operatorname{Var}(X_v) \geq|\langle[X_u,X_v]\rangle/(2\mathrm i)|^2$。

**证明。**

$X_u^2=X_v^2=I$，故方差为 $1-a^2$、$1-b^2$； 对称协方差为 $c-ab$。 Gram 行列式恒等式给

$$
\bigl[(u\times v)\cdot r\bigr]^2
=(1-c^2)\left\|r\right\|^2-a^2-b^2+2cab.
$$

将其代入右边展开，恰得 $(1-a^2)(1-b^2)$。 最后一项非负，交换子公式给所述不等式。

$\square$

<a id="section-7"></a>

## 7　复合端口、测量更新与实际记录

### 7.1　为什么单个方向不够表示整体

由 C，复合系统使用 $\mathcal H_A\otimes\mathcal H_B$； 基本端口可取 $\mathbb C^2$，有限辅助空间可通过增加端口和指定子空间表示。 联合态的局部读出由偏迹给出。

#### 命题 7.1：局部方向不决定联合态

态

$$
\rho_{\rm ent}=|\Phi^+\rangle\langle \Phi^+|,\quad
|\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},
\qquad
\rho_{\rm mix}=\frac{|00\rangle\langle 00|+|11\rangle\langle 11|}2
$$

具有相同的两个局部态 $I/2$，但

$$
\operatorname{tr}(\rho_{\rm ent}\,\sigma_1\otimes\sigma_1)=1,\qquad
\operatorname{tr}(\rho_{\rm mix}\,\sigma_1\otimes\sigma_1)=0.
$$

**证明。**

偏迹消去 $|00\rangle\langle 11|$ 及其伴随项， 两者都得到 $I/2$。 $\sigma_1\otimes\sigma_1$ 交换 $|00\rangle$ 与 $|11\rangle$， 故 $|\Phi^+\rangle$ 为本征值一的态； 它在两个单独基态上的对角期望均为零。

$\square$

该区别与项目已存在的局部边缘盲区结论一致 [\[10\]](#ref-RepoBlind)。单端口理论也允许只保留可分联合态的替代组合规则； 因此局部球、局部 Born 概率和局部旋转不唯一决定纠缠结构。

#### 定理 7.2：有限维完全正映射的内部实现

线性映射 $\Phi:M_d(\mathbb C)\to M_e(\mathbb C)$ 完全正， 当且仅当存在有限组矩阵 $K_\alpha$，使

$$
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
$$

它保迹当且仅当 $\sum_\alpha K_\alpha^\dagger K_\alpha=I$。 对保迹映射， $V\psi=\sum_\alpha K_\alpha\psi\otimes|\alpha\rangle$ 是等距映射，并给出 $\Phi(\rho)=\operatorname{tr}_M(V\rho V^\dagger)$。

**证明。**

完全正性使 Choi 矩阵 $C_\Phi=\sum_{i,j}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)$ 非负。 取谱分解 $C_\Phi=\sum_\alpha|v_\alpha\rangle\langle v_\alpha|$， 把每个 $v_\alpha=\sum_i|i\rangle\otimes K_\alpha|i\rangle$ 重排成矩阵。逐块比较给 Kraus 式。 反向中，每项在任意辅助空间上仍为共轭，故完全正。 迹的循环性给保迹条件；直接计算 $V^\dagger V$ 及偏迹得余下结论。

$\square$

等距映射可通过补齐正交基扩展为较大空间的酉操作。 这项标准构造允许把仪器作为内部系统，而无需加入模型外的物理测量者。

#### 定义 7.3：量子仪器

一项有限仪器为 $\{\mathcal J_s\}$， $\mathcal J_s(X)=\sum_\alpha K_{s\alpha}XK_{s\alpha}^\dagger$， 且 $\sum_{s,\alpha}K_{s\alpha}^\dagger K_{s\alpha}=I$。 定义

$$
E_s=\sum_\alpha K_{s\alpha}^\dagger K_{s\alpha},\quad
p_s=\operatorname{tr}(\rho E_s),\quad
\rho_s=\frac{\mathcal J_s(\rho)}{p_s}\quad(p_s>0).
$$

零概率分支不指定条件态。

#### 命题 7.4：概率不唯一确定更新

同一个效果 $E_s$ 可以由 $\rho\mapsto\sqrt{E_s}\rho\sqrt{E_s}$ 或 $\rho\mapsto\operatorname{tr}(\rho E_s)\sigma_s$ 实现， 其中 $\sigma_s$ 为任意指定密度态。 两者结果概率相同，条件输出一般不同。

**证明。**

两者的迹均为 $\operatorname{tr}(\rho E_s)$，且均完全正。 若输入经第一种操作仍保留变化，而第二种恒输出 $\sigma_s$， 则它们不是同一仪器。取非平凡秩一效果且不同的 $\sigma_s$ 即得例子。

$\square$

#### 定理 7.5：尖锐秩一重复读出唯一给出 Lüders 仪器

若 $E_s=P_s$ 为正交秩一完备投影， 且结果 $s$ 产生后立即重复必得 $s$， 则 $\mathcal J_s(\rho)=P_s\rho P_s$。

**证明。**

从 $\sum_\alpha K_{s\alpha}^\dagger K_{s\alpha}=P_s$， 可知每个 $K_{s\alpha}$ 在 $\ker P_s$ 上为零， 故可写 $K_{s\alpha}=|v_\alpha\rangle\langle s|$。 重复性要求所有输出支撑都在 $\operatorname{span}\{|s\rangle\}$， 所以 $v_\alpha=c_\alpha|s\rangle$。 归一条件给 $\sum_\alpha|c_\alpha|^2=1$，代回即得结论。

$\square$

高秩投影的块内可逆变换也可保持重复性， 所以本结论的秩一条件不能省略。

#### 定理 7.6：原构想中“相融点”的精确操作含义

对于方向轴 $m$ 的完整理想读出， 忽略结果后的态为

$$
\Delta_m(\rho)=P_m\rho P_m+P_{-m}\rho P_{-m}
=\rho\bigl((m\cdot r)m\bigr).
$$

实际选择分支的条件 Bloch 向量为 $+m$ 或 $-m$， 其概率分别为 $(1\pm m\cdot r)/2$。

**证明。**

秩一性给 $P_{\pm m}\rho P_{\pm m}=p_{\pm}P_{\pm m}$。 相加后 Pauli 系数为 $(p_+-p_-)m=(m\cdot r)m$。

$\square$

所以 $C=(m\cdot r)m$ 是 *未读取结果时的去相干态* ， 而不是一次测量的唯一确定输出。除退化情形外，$C$ 位于球内，已不是纯态方向。

#### 命题 7.7：去相干的不可逆性及其范围

$\Delta_m$ 不是单射。其无选择输出满足 $S(\Delta_m\rho)\geq S(\rho)$， 其中 $S(\rho)=-\operatorname{tr}(\rho\log\rho)$。 该结论不意味着每个条件分支的熵增加，也不意味着整体酉演化不可逆。

**证明。**

所有横向分量被删除，故不同输入可有相同输出。 又 $\Delta_m(\rho)=(\rho+X_m\rho X_m)/2$， $X_m=m\cdot\boldsymbol{\sigma}$ 为酉矩阵。 由熵的凹性及酉不变性得不等式。 条件分支为纯态，熵可降至零；定理 7.2 的联合实现仍可酉。

$\square$

<a id="section-8"></a>

## 8　线与面积互补的实验定义

线投影与楔积的勾股关系可以成为波粒互补的一个严格模型， 但必须指定路径编码、合束器及实际读取的量。

#### 定义 8.1：两路径可预测性与可见度

在指定路径基下写

$$
\rho=\begin{pmatrix}p&c\\\bar c&1-p\end{pmatrix},\qquad
|c|^2\leq p(1-p).
$$

先验路径可预测性定义为 $P=|2p-1|$。 对理想平衡合束器扫描相位 $\phi$， 输出一端的概率可写为

$$
I(\phi)=\tfrac12+\operatorname{Re}(e^{\mathrm i\phi}c).
$$

定义可见度 $V=(I_{\max}-I_{\min})/(I_{\max}+I_{\min})$。

#### 定理 8.2：精确的线面互补式

有 $V=2|c|$，且

$$
\boxed{P^2+V^2=\left\|r\right\|^2\leq1.}
$$

若 $m$ 为路径轴，则 $P=|m\cdot r|$、$V=\left\|m\wedge r\right\|$。 纯态时等号为一。

**证明。**

$I_{\max,\min}=1/2\pm|c|$，故 $V=2|c|$。 在路径轴为第三轴的坐标中， $r=(2\operatorname{Re}c,-2\operatorname{Im}c,2p-1)$。 因此 $P^2+V^2=\left\|r\right\|^2$。 公共旋转后得到坐标无关表达；态正性给 $\left\|r\right\|\leq1$。

$\square$

这给原始图像一个准确用途：*纵向分量描述路径偏向， 横向相干描述特定干涉仪的可见度。* 它没有把所有粒子定义成线、所有波定义成面； 空间波包的传播、局域计数和粒子统计尚需相应的物理模型。 标量振幅也可以带符号或相位而相消， 所以“标量没有面积，故不可能干涉”并不成立。

#### 定理 8.3：带路径记录的可区分度

令 $p+q=1$，路径与标记器的纯联合态为

$$
|\Psi\rangle=\sqrt p\,|0\rangle|d_0\rangle
 +e^{\mathrm i\phi_0}\sqrt q\,|1\rangle|d_1\rangle,
\qquad \left\|d_0\right\|=\left\|d_1\right\|=1.
$$

若仅在路径端口合束，且标记器用于最优路径判别，则

$$
V=2\sqrt{pq}\,|\langle d_0,d_1\rangle|,\quad
D=\left\|p|d_0\rangle\langle d_0|-q|d_1\rangle\langle d_1|\right\|_1,
$$

并有

$$
D=\sqrt{1-4pq|\langle d_0,d_1\rangle|^2},\qquad D^2+V^2=1.
$$

对一般混合联合态 $\rho_{SD}$，定义 $p\rho_0=\langle 0|\rho_{SD}|0\rangle$、 $q\rho_1=\langle 1|\rho_{SD}|1\rangle$， 其中零权重时直接使用未归一对角块； 令 $D=\|p\rho_0-q\rho_1\|_1$， $V$ 仍取路径端口的干涉可见度，则 $D^2+V^2\leq1$。

**证明。**

偏迹给路径非对角元的模为 $\sqrt{pq}|\langle d_0,d_1\rangle|$，于是得到 $V$。 Hermitian 差矩阵的非零部分至多二维， 迹为 $p-q$，行列式为 $-pq(1-|\langle d_0,d_1\rangle|^2)$。 两特征值异号或至少一个为零， 其绝对值之和即所述平方根，包括 $pq=0$ 及重合标记的边界。 最优二元判别成功率为 $(1+D)/2$： 对猜测零的效果 $E$，成功率为 $q+\operatorname{tr}[E(p\rho_0-q\rho_1)]$； 取正谱子空间投影达到最大，得到迹范数公式。

对混合联合态作纯化，把新增辅助端口并入总标记器。 路径可见度不变，而丢弃新增辅助不会提高 $D$。 后一项由 Hermitian $A$ 的变分式证明：

$$
\|\operatorname{tr}_EA\|_1
=\max_{\substack{B=B^\dagger\\\|B\|_\infty\leq1}}
\operatorname{tr}[(B\otimes I)A]\leq\|A\|_1.
$$

对纯化应用已证等式即得一般不等式。

$\square$

这里 $D$ 含标记器的侧信息，与 $P$ 不同。 若 $p=q=1/2$ 且标记正交，$P=0$，但 $D=1,V=0$。 因此读出路径信息不是简单把测量轴转到状态方向； 它涉及路径与记录端口的联合关系。 本节是标准干涉互补结果的具体推导，参见 Englert [\[5\]](#ref-Englert)。

<a id="section-9"></a>

## 9　内禀变化长度、能量与历史切向

#### 定义 9.1：方向路径的量子变化量

对连续、分段 $C^1$ 路径 $\gamma:\lambda\mapsto n(\lambda)\in S^2$， 定义双矢量值一形式及累计变化长度

$$
\Theta=n\wedge\mathrm dn,\qquad
\boxed{q[\gamma]=\frac12\int_\gamma\|\Theta\|
=\frac12\int\left\|n'(\lambda)\right\|\,\mathrm d\lambda.}
$$

这里范数沿路径作用于切向量，积分所得为无量纲实数。

#### 定理 9.2：变化长度的结构

$q$ 在保向分段光滑重参数下不变； 对路径拼接可加；反向路径有相同 $q$； 且 $q=0$ 当且仅当路径恒定。 采用 $d_{\mathrm{FS}}([\psi],[\varphi])=\arccos|\langle \psi|\varphi\rangle|$ 的度规约定时，

$$
\mathrm ds_{\mathrm{FS}}=\frac12\left\|\mathrm dn\right\|
=\frac12\left\|n\wedge\mathrm dn\right\|,\qquad
q[\gamma]\geq\frac12\arccos(n_{\rm in}\cdot n_{\rm out}).
$$

**证明。**

$n\cdot\mathrm dn=0$ 给 $\left\|n\wedge\mathrm dn\right\|=\left\|\mathrm dn\right\|$。 重参数不变性、可加性、反向对称性及零长度结论由普通弧长性质得到。 写 $\psi=(\cos(\theta/2),e^{\mathrm i\phi}\sin(\theta/2))^T$， 直接计算

$$
\mathrm ds_{\mathrm{FS}}^2
=\langle \mathrm d\psi,\mathrm d\psi\rangle-|\langle \psi,\mathrm d\psi\rangle|^2
=\frac14(\mathrm d\theta^2+\sin^2\theta\,\mathrm d\phi^2)
=\frac14\,\mathrm dn\cdot\mathrm dn.
$$

任意曲线长度不小于端点球面距离的一半，得最后不等式。

$\square$

因此，双矢量 $n\wedge\mathrm dn$ 的 *范数* 可以量化状态变化； 其积分是长度，不是一般的有向球面面积。 把 $\mathrm ds_{\mathrm{FS}}$ 直接写成 $\left\|n\wedge\mathrm dn\right\|$ 会多出二倍。 本节的 $q$ 定义用于纯态路径；混态若需相应几何必须另行指定度规。

#### 定理 9.3：速度与能量不确定度

对于分段 $C^1$ 酉路径作用下的基本二能级归一化纯态， 定义 $q(t)=q[\gamma|_{[0,t]}]$，则在各光滑段

$$
\frac{\mathrm dq}{\mathrm dt}=\frac{\Delta_\psi H(t)}{\hbar}.
$$

若 $\overline{\Delta H}=T^{-1}\int_0^T\Delta H(t)\,\mathrm dt>0$， 则

$$
T\geq
\frac{\hbar\,\arccos|\langle \psi(0)|\psi(T)\rangle|}
{\overline{\Delta H}}.
$$

**证明。**

将 $\dot\psi=-\mathrm iH\psi/\hbar$ 代入 FS 线元， 得 $\dot q^2=(\langle H^2\rangle-\langle H\rangle^2)/\hbar^2$。 积分并使用端点距离不超过曲线长度即得界。 若积分能量不确定度为零，则射线恒定，不用除以零。

$\square$

这是量子演化几何中的标准速度关系 [\[2\]](#ref-AnandanAharonov), [\[3\]](#ref-BrodyHughston)。 对于一般有限维纯态，可直接以 $\mathrm ds_{\mathrm{FS}}^2=\langle \mathrm d\psi,\mathrm d\psi\rangle-|\langle \psi,\mathrm d\psi\rangle|^2$ 定义 $q$，同一证明给出相同速度关系； 此时不再把整体纯态强行表示为一个 $S^2$ 方向。 它需要动力学和能量单位的标定， 不能反过来凭几何长度直接确定秒或静止质量。

#### 定理 9.4：余弦投影不是全局时钟

不存在仅依赖当前方向的实函数 $T(n)$， 使全部非恒定可逆闭合路径上的时间增量都严格为正。 特别地 $\tau(n)=a\cdot n$ 不能作为一般累加时钟。

**证明。**

闭合路径起终点相同，所以任何状态函数的增量为零； 若每段增量为正且可加，总增量应为正，矛盾。 具体取 $n(s)=\cos s\,e_1+\sin s\,e_2$， 则 $e_1\cdot n(s)=\cos s$ 周期、可负且不单调； 但一整圈的 $q$ 为 $\pi$。

$\square$

正的累计长度说明发生过多少变化； 路径反向仍有正长度，所以它没有单独产生不可逆的时间箭头。 单向历史还需要记录或因果序。

### 9.1　最短路径与已给定历史切向

#### 命题 9.5：一个明确的变分控制规则

固定持续参数区间和端点，若选择使 $\mathcal E[n]=\frac12\int\left\|\dot n\right\|^2\,\mathrm dt$ 驻定的球面路径，则

$$
\ddot n+\left\|\dot n\right\|^2n=0.
$$

非恒定解以恒速沿大圆运动。

**证明。**

带约束 $n^2=1$ 的变分给 $\ddot n=\lambda n$。 二次求导约束给 $n\cdot\ddot n=-\left\|\dot n\right\|^2$， 所以 $\lambda=-\left\|\dot n\right\|^2$。 与 $\dot n$ 作内积可知速度恒定。 常系数方程的解为 $n(t)=a\cos(vt)+u\sin(vt)$， $a\perp u$、$|a|=|u|=1$。

$\square$

该变分选择是额外控制原则；不是归一化条件自动给出的唯一动力学。 若初始历史切向已指定为 $u$，到达目标 $b$ 的大圆解要求 $b\in\operatorname{span}\{a,u\}$，且弧段方向匹配。 不满足时须改变控制或允许曲线弯曲；仅由端点和切向不能推出轨迹必为椭圆。

<a id="section-10"></a>

## 10　闭环历史、几何相位与方向场

#### 定理 10.1：端点关系的消去与门历史的保留

端点关系满足 $Q_{ab}Q_{bc}=Q_{ac}$， 故闭合点列的全部 $Q$ 乘积恒为一。 但最短旋转元的实际复合可在回到同一方向后仍非恒等。 具体地，沿 $e_1\to e_2\to e_3\to e_1$，

$$
R_{31}R_{23}R_{12}=\frac{1-e_2e_3}{\sqrt2}.
$$

**证明。**

$Q_{ab}Q_{bc}=ab\,bc=ac$，逐项消去得闭环结论。 另一方面由定理 3.3，

$$
R_{12}=\frac{1-e_1e_2}{\sqrt2},\
R_{23}=\frac{1-e_2e_3}{\sqrt2},\
R_{31}=\frac{1-e_3e_1}{\sqrt2}.
$$

用 $e_ie_j=-e_je_i$ 逐项相乘，分子为 $2(1-e_2e_3)$，分母为 $2\sqrt2$，得到所述结果。

$\square$

该门绕 $e_1$ 转 $\pi/2$，固定方向 $e_1$； 其正向本征旋量获得 $-\pi/4$ 相位。 单独的整体相位不可观测，但与另一条相干路径比较时相位差可以影响概率。 这里三个边的总变化长度为 $3\pi/4$，又不同于相位的大小。

#### 定义 10.2：射线相位联络

对局部归一化旋量 $\psi$，定义 $A=\mathrm i\langle \psi|\mathrm d\psi\rangle$。 变换 $\psi\mapsto e^{\mathrm i\chi}\psi$ 下， $A\mapsto A-\mathrm d\chi$； 因此 $F=\mathrm dA$ 是规范不变量。

#### 定理 10.3：二能级几何相位

在球面坐标的上述旋量截面中，

$$
A=-\frac{1-\cos\theta}{2}\,\mathrm d\phi,\qquad
F=-\frac12\sin\theta\,\mathrm d\theta\wedge\mathrm d\phi.
$$

对闭合回路及相容定向，几何相位为 $\gamma_{\rm geom}=-\Omega_{\rm solid}/2\pmod{2\pi}$。 对无零重叠的三个纯态，

$$
\mathcal B(a,b,c):=\operatorname{tr}(P_aP_bP_c)
=\frac{1+a\cdot b+b\cdot c+c\cdot a
+\mathrm i(a\times b)\cdot c}{4}.
$$

以最短测地弧闭合的三角回路满足 $\gamma_{\triangle}=-\arg\mathcal B\pmod{2\pi}$。

**证明。**

对 $\psi=(\cos(\theta/2),e^{\mathrm i\phi}\sin(\theta/2))^T$ 求导， 得到 $A=-\sin^2(\theta/2)\mathrm d\phi$； 外微分给 $F$。分片使用 Stokes 公式及截面过渡， 得到固体角公式；更换所取球面区域使固体角相差 $4\pi$， 相位仅改变 $2\pi$ 的整数倍。

展开三重 Pauli 乘积并取迹得到 $\mathcal B$ 的显式式子。 又 $\mathcal B=\langle a|b\rangle\langle b|c\rangle\langle c|a\rangle$。 沿一条最短弧的水平输运可将相邻态代表选成重叠为正； 连续三次这样的选择，末态与初态的相对相位为 上述三个重叠相角之和的负值，故得到末式。

$\square$

这是一项标准几何相位结构 [\[4\]](#ref-SamuelBhandari)。原稿中的投影点 $C=(a\cdot b)a$ 由 $a,b$ 决定，不增加自由度； 但真实实验路径中的第三态 $c$ 可能携带不可删除的闭环信息。

#### 例 10.4：长度与有向面积不是同一种时间量

纬角为 $\theta_0$ 的一周回路有

$$
q=\pi\sin\theta_0,\qquad
\gamma_{\rm geom}=-\pi(1-\cos\theta_0)\pmod{2\pi}.
$$

反转绕行方向不改变 $q$，却反转几何相位。 所以不能用一个无条件恒等式把两者混为同一时钟。

#### 定义 10.5：连续方向场

给定光滑参数流形 $M$ 和映射 $n:M\to S^2$， 定义

$$
\Theta=n\wedge\mathrm dn\in\Omega^1(M;\Lambda^2V),\quad
g_Q(X,Y)=\tfrac14\,\mathrm dn(X)\cdot\mathrm dn(Y),
$$

$$
F(X,Y)=-\tfrac12n\cdot
       \bigl(\mathrm dn(X)\times\mathrm dn(Y)\bigr).
$$

参数流形用于索引内部关系； 将它指定为物理时空需要另加解释。

#### 定理 10.6：方向场的严格能力边界

$g_Q$ 为正半定，秩不超过二； $F$ 闭合，且 $F\wedge F=0$。 若 $M=S^2$ 且 $n$ 为恒等映射， $\int_M F=-2\pi$，因此不存在全局单值一形式 $A$ 满足 $F=\mathrm dA$。

**证明。**

$\mathrm dn$ 的像属于二维切平面，故 $g_Q$ 正半定且秩至多二。 $F$ 是目标球面曲率二形式的拉回； 目标上的外微分及四形式均为零，所以 $\mathrm dF=0$、$F\wedge F=0$。 最后由球面积分得到 $-2\pi$。 若 $F=\mathrm dA$ 全局成立，闭流形上的 Stokes 公式给积分零，矛盾。

$\square$

这已经是一套明确的方向场几何。 它不会自动产生四维非退化 Lorentz 度规，也没有给出 Maxwell 或 Yang–Mills 的场方程及全部自由度。要完成这些扩展，必须添加基流形、 作用量、耦合、边界条件与可实验标定的变量。

<a id="section-11"></a>

## 11　内生观察者、响应商与记忆

#### 定义 11.1：有限内生观察者

一个观察者模型为 $\mathcal O=(M,\mathcal Q_{\mathcal O},\mathcal I_{\mathcal O},\preceq)$： $M$ 是整体内的记忆端口， $\mathcal Q_{\mathcal O}$ 是允许的测试或协议族， $\mathcal I_{\mathcal O}$ 是可用仪器， $\preceq$ 是记录的因果关系。 单个测量轴 $m$ 可以属于该结构，但不能代替整个结构。

#### 定义 11.2：观察响应等价

令 $X$ 为共同模型的合法态或配置集合， 每个可用协议 $q$ 给响应分布 $R_q(x)$。 定义

$$
x\sim_{\mathcal O}y
\quad\Longleftrightarrow\quad
R_q(x)=R_q(y)\quad\text{对所有 }q\in\mathcal Q_{\mathcal O}.
$$

观察者的操作描述为响应商 $X/{\sim_{\mathcal O}}$。

#### 定理 11.3：响应商的最小充分性与包含关系

编码 $E:X\to Z$ 能精确恢复全部观察响应， 当且仅当每个 $R_q$ 在 $E$ 的每个纤维上常值。 因此响应商是保留这些目标的最粗充分划分。 若 $\mathcal Q_1\subseteq\mathcal Q_2$， 则存在规范满射 $X/{\sim_2}\to X/{\sim_1}$。

**证明。**

若 $R_q=d_q\circ E$，同一编码值必有相同响应。 反之，在达到像 $E(X)$ 上定义 $d_q(E(x))=R_q(x)$，纤维常值性保证良定义。 联合响应本身显然满足条件； 任何充分编码的纤维只能细于其等价类。 协议包含时，$\sim_2$ 蕴含 $\sim_1$， 故 $[x]_2\mapsto[x]_1$ 良定义且满射。

$\square$

这把“观察者只看到整体的一部分”表述为可核验的恢复条件。 两个观察者的协议族若没有包含关系，不能仅凭两条方向线 推出他们知道彼此的全部历史。

#### 定理 11.4：仪器的全部记录可内生实现

对任意有限仪器，可令

$$
V\psi=\sum_{s,\alpha}K_{s\alpha}\psi\otimes|s,\alpha\rangle_M.
$$

则 $V^\dagger V=I$；对记忆子空间 $P_s^M=\sum_\alpha|s,\alpha\rangle\langle s,\alpha|$ 读出结果 $s$ 并忽略其他记忆坐标，精确得到 $\mathcal J_s$。

**证明。**

归一条件给 $V^\dagger V=\sum_{s,\alpha}K_{s\alpha}^\dagger K_{s\alpha}=I$。 记忆投影后取偏迹，仅保留同一 $(s,\alpha)$ 的对角项， 得到 $\sum_\alpha K_{s\alpha}\rho K_{s\alpha}^\dagger$。

$\square$

这里 Kraus 标签 $\alpha$ 可以属于未访问辅助系统； 它不会因为出现在数学表达中就自动成为观察者可读的经典资料。

#### 命题 11.5：记忆容量和不可克隆

一个 $d$ 维端口最多承载 $d$ 个可完美区分的纯记录。 不存在同一等距操作能复制所有未知纯态。

**证明。**

若效果 $E_i$ 完美区分记录 $|m_i\rangle$，则 $E_i|m_i\rangle=|m_i\rangle$， $E_i|m_j\rangle=0$ 对 $j\ne i$ 成立； 所以 $\langle m_i,m_j\rangle=0$，记录数至多为 $d$。 若等距克隆器复制两个重叠为 $z$ 的纯态且不留辅助差别， 内积保持要求 $z=z^2$，与 $0<|z|<1$ 矛盾。 即使保留输入相关辅助，取绝对值仍要求 $|z|\leq|z|^2$，仍矛盾。

$\square$

一个 qubit 的连续球面因此不等于无限容量的完美记录器。 内生记录可以复制已选正交指针的信息，不能克隆任意量子方向。

#### 例 11.6：内生描述不自动选定唯一测量本体

考虑

$$
|\Phi\rangle=\frac{|0\rangle|M_0\rangle+|1\rangle|M_1\rangle}{\sqrt2},
\qquad\langle M_0,M_1\rangle=0.
$$

条件于记忆 $M_0$，系统态是 $|0\rangle$。 但联合投影 $|\Phi\rangle\langle \Phi|$ 在纯联合态下的概率为一， 在删去两项相干后的混合态下为 $1/2$。 这两种全局描述不是同一个可检验状态。

所以 $O\cdot O=1$ 只是一条向量归一式， 不能证明所有观察者都具有某种绝对经典状态。 本理论容纳内生仪器与条件记录； 若进一步主张客观坍缩、唯一隐藏结果或特定多分支本体， 必须添加对应规则并重新检验联合预测。

<a id="section-12"></a>

## 12　静态整体中的内禀时钟

### 12.1　任意有限酉历史的精确静态表示

#### 定义 12.1：传播约束

给有限维空间 $\mathcal H$、酉序列 $U_1,\ldots,U_N$， 令 $W_0=I$、$W_k=U_k\cdots U_1$。 在 $\mathbb C^{N+1}\otimes\mathcal H\simeq\mathcal H^{\oplus(N+1)}$ 上定义

$$
D(x_0,\ldots,x_N)
=(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
\qquad K_{\rm prop}=D^\dagger D.
$$

若 $N=0$，取 $D=0$。

#### 定理 12.2：静态历史与内部条件演化

映射

$$
V_{\rm hist}\psi=\frac1{\sqrt{N+1}}
\sum_{k=0}^N|k\rangle_C\otimes W_k\psi
$$

是 $\mathcal H$ 到 $\ker K_{\rm prop}$ 的等距同构。 对单位输入 $\psi_0$，静态向量 $|\Omega_N\rangle=V_{\rm hist}\psi_0$ 满足 $K_{\rm prop}|\Omega_N\rangle=0$。 内部时钟投影到 $k$ 的概率为 $1/(N+1)$， 相应条件态恰为 $W_k\psi_0$。

**证明。**

$\langle x,K_{\rm prop}x\rangle=\left\|Dx\right\|^2$， 所以核向量恰好满足全部二元传播关系 $x_k=U_kx_{k-1}$。 它由 $x_0$ 唯一确定，故上述映射满到该核。 又各 $W_k$ 酉，时钟基正交，得 $\langle V_{\rm hist}\psi,V_{\rm hist}\varphi\rangle =(N+1)^{-1}\sum_k\langle W_k\psi,W_k\varphi\rangle =\langle\psi,\varphi\rangle$。 最后直接投影并归一，即得钟条件态。

$\square$

#### 推论 12.3：唯一静态全局态的显式模型

给定单位输入 $\psi_0$，再加内部输入约束

$$
K_{\rm in}=|0\rangle\langle 0|_C\otimes
 (I-|\psi_0\rangle\langle \psi_0|),\qquad
K=K_{\rm prop}+K_{\rm in}.
$$

则 $K\succeq0$， $\ker K=\operatorname{span}\{|\Omega_N\rangle\}$。 因此 $|\Omega_N\rangle$ 是唯一的零能纯态射线， 但内部条件读出仍可遍历任意已指定的有限酉历史。

**证明。**

两个加项均非负。 向量在和的核中，当且仅当同时在两者的核中。 传播核中所有分量由 $x_0$ 决定； 输入约束迫使 $x_0$ 平行 $\psi_0$， 故共同核一维。反向代入显然成立。

$\square$

这里“唯一”来自明确的传播条件和输入条件， 不是仅由归一化或静态性推出。 条件位于整体数学结构之内，但其内容仍须声明。 该构造也没有断言物理宇宙的 Hamiltonian 恰等于这个 $K$。

### 12.2　有限周期时钟与 Schrödinger 序列

#### 定理 12.4：配对能谱的有限内部时钟

取 $d\geq2$、$T>0$， $E_j=2\pi\hbar j/T$，$j=0,\ldots,d-1$。 设 $H_S|j\rangle=E_j|j\rangle$、 $H_C|j\rangle=-E_j|j\rangle$， 并令

$$
|\Omega_{\rm pw}\rangle=\sum_{j=0}^{d-1}c_j|j\rangle_C|j\rangle_S,
\qquad \sum_j|c_j|^2=1.
$$

则 $(H_C+H_S)|\Omega_{\rm pw}\rangle=0$。 定义 $t_\ell=\ell T/d$（$\ell=0,\ldots,d-1$）和正交时钟基

$$
|t_\ell\rangle_C=\frac1{\sqrt d}
\sum_j e^{\mathrm iE_jt_\ell/\hbar}|j\rangle_C.
$$

每个钟结果的概率为 $1/d$，系统条件态为

$$
|\psi_\ell\rangle
=e^{-\mathrm iH_St_\ell/\hbar}\sum_jc_j|j\rangle,
\qquad
\psi_{\ell+1}=e^{-\mathrm iH_ST/(d\hbar)}\psi_\ell.
$$

递推在 $\ell<d-1$ 时成立，也可按模 $d$ 解释，因为 $e^{-\mathrm iH_ST/\hbar}=I$。

**证明。**

每个 $|j\rangle_C|j\rangle_S$ 的总能量为零，故全局约束成立。 有限 Fourier 正交性给时钟基正交归一。 钟方向内积为 $d^{-1/2}\sum_jc_je^{-\mathrm iE_jt_\ell/\hbar}|j\rangle_S$， 范数平方为 $1/d$；归一后即得条件态和递推式。

$\square$

这是静态整体包含内部时间关系的一个明确模型， 与 Page–Wootters 的研究方向一致 [\[6\]](#ref-PageWootters)。 分解、配对能谱、周期和系数均为已声明数据。 该有限时钟只有 $d$ 个可完美区分的读数； 连续 Schrödinger 插值是另行给定的可逆结构， 不是有限记忆自动获得无限精确的时间读数。

### 12.3　记录时间与可逆门并存

#### 定义 12.5：累加记录时钟

若观察者已记录有限事件序列 $e_1,\ldots,e_k$， 给每个计数事件权重 $w(e)>0$，定义

$$
\tau_{\rm rec}(k)=\sum_{j=1}^k w(e_j).
$$

该定义只对指定的实际计数对象生效； 相同门标签出现在不同位置可以是不同事件。

#### 命题 12.6：状态返回不删除历史

若 $U_2=U_1^\dagger$，则系统的第二步态与初态相同， 但 $q$ 可为正，记录时钟可严格增加， 且历史钟状态 $|2\rangle$ 与 $|0\rangle$ 正交。

**证明。**

$U_2U_1=I$ 给系统返回。 若路径非恒定，定理 9.2 给正长度； 正事件权重给正记录增量； 历史钟的正交性来自其定义。 这些量没有要求系统端口本身不可逆。

$\square$

这一点使“可逆量子门”与“历史不断追加”可以同时成立。 但是无限历史需要无限增长的记录资源、压缩或遗忘条件； 固定有限记忆不会自动容纳无限个可完美区分的时刻。

<a id="section-13"></a>

## 13　与时空结构的一个严格代数桥梁

#### 定理 13.1：Hermitian 正锥与 Lorentz 型二次型

对 $X=x^0I+x\cdot\boldsymbol{\sigma}$，

$$
\det X=(x^0)^2-\left\|x\right\|^2.
$$

若 $A\in SL(2,\mathbb C)$，变换 $X\mapsto AXA^\dagger$ 保持该二次型并保持正半定锥。 非零正半定矩阵对应 $x^0>0$、 $x^0\geq\left\|x\right\|$；其秩一边界对应等号。

**证明。**

$X$ 的特征值为 $x^0\pm\left\|x\right\|$， 相乘得行列式，正性条件随即成立。 又 $\det(AXA^\dagger)=\det A\,\det X\,\overline{\det A}=\det X$。 对于任何向量 $v$， $v^\dagger AXA^\dagger v=(A^\dagger v)^\dagger X(A^\dagger v)\geq0$。

$\square$

例如 $A=\exp(\eta\sigma_3/2)$ 给

$$
\begin{pmatrix}x^{0\prime}\\x^{3\prime}\end{pmatrix}
=\begin{pmatrix}\cosh\eta&\sinh\eta\\
\sinh\eta&\cosh\eta\end{pmatrix}
\begin{pmatrix}x^0\\x^3\end{pmatrix},
\qquad x^{1\prime}=x^1,\quad x^{2\prime}=x^2.
$$

这是真正的 Lorentz 型代数结构，比简单把 Euclidean 勾股式 改写成时空公式更精确。 但它尚未赋予 $x^0,x$ 物理时空量纲； 也未证明实际惯性变换就是这些矩阵的作用。

特别地，$X=2\rho=I+r\cdot\boldsymbol{\sigma}$ 时， 球是正锥在 $x^0=1$ 的截面。 任意纯 qubit 都落在该代数锥的秩一边界， 包括用于描述有质量粒子内部自旋的纯态。 因此“秩一边界”不能直接解释成“这个粒子无质量”。 一般非酉 $A$ 的归一化作用还是滤波型变化， 并非任意态上确定成功的可逆量子通道。 从本节走向物理相对论，仍须建立事件、钟标定、因果传播与能动量的对应。

<a id="section-14"></a>

## 14　完整有限协议、具体动力学与闭合性

#### 定义 14.1：OTF 有限协议

协议给出有限个量子端口及内部记录端口、共同初态、 有限深度的因果仪器网络、允许的控制和终端读出。 每个节点的分支完全正、总和保迹； 反馈只依赖已经存在的因果前驱记录。 不可复制未声明的未知量子端口。

#### 定理 14.2：有限操作闭合与内生历史表示

在 G、M、S、R、C、J、I 下，所有 OTF 有限协议：

1.  产生非负、归一且对公共标架变换不变的联合结果分布；

2.  对串行、并行和有限记录反馈闭合；

3.  可在有限扩大后的整体内用酉操作及内部记录实现；

4.  在选定纯化和初始资料后，可用定理 12.2 表示为静态历史，并用推论 12.3 的输入约束选择唯一历史态。

在其操作范围内，所得理论与相应的标准有限维量子操作模型具有相同预测。

**证明。**

任一分支对应 Kraus 算子乘积的有限求和， 正性由完全正性保证，概率为该分支输出的迹。 在协议树的最后一层按结果求和，利用 $\sum K^\dagger K=I$ 消去该层； 向前归纳到初态的迹一，得到总概率一。 公共标架变化对状态、操作和效果作一致共轭， 迹不变，故预测不变。

完全正映射的复合和张量积仍完全正； 总保迹条件在串并联及按实际记录分支的有限反馈下保持， 故前两项成立。 逐节点使用定理 7.2， 保留所有原本会丢弃的辅助端口，并令它们不再参与原协议后续的可访问操作； 实际经典记录保留正交副本，避免以未声明的相干复合替代经典反馈。 后来会返回的环境则按原协议继续连接。 有限反馈可由正交记录控制的酉操作实现。 共同混合初态可作有限纯化，因此得到同一有限大空间上的酉序列。 对该序列应用静态历史构造和输入选态条件，得到后两项。 所有概率、态更新和组合规则都已经是其矩阵量子表示， 因而与对应标准模型操作等价。

$\square$

静态钟的单次条件读出不自动等于任意多时刻的无扰动联合读取。 若任务涉及多时刻测量，必须把这些实际仪器和记录包含在协议内， 再对完整协议应用定理。

### 14.1　一个会产生纠缠的明确动力学

#### 例 14.3：两端口相互作用使单个方向进入球内

指定 $H_{\rm int}=(\hbar g/2)\sigma_3\otimes\sigma_3$ 及初态 $|+x\rangle|+x\rangle$。 有

$$
|\psi(t)\rangle
=\frac12\left[
e^{-\mathrm igt/2}(|00\rangle+|11\rangle)
+e^{\mathrm igt/2}(|01\rangle+|10\rangle)\right].
$$

两个局部态的 Bloch 向量均为 $r_1=r_2=(\cos gt,0,0)$。 当 $gt=\pi/2$ 时，每个局部态为 $I/2$，整体仍为纯纠缠态。

**证明。**

相互作用在计算基上对偶宇称、奇宇称分别给相位 $e^{-\mathrm igt/2}$、$e^{\mathrm igt/2}$。 偏迹得到对角元 $1/2$、非对角元 $\cos(gt)/2$。 在 $gt=\pi/2$ 时，局部秩为二； 整体纯态若可分则局部必纯，故此时纠缠。

$\square$

这个实例给出实际运动定律及可计算预测， 也表明将整个复合理论始终限制为“一端口一条单位方向”并不闭合。 对有限关系图可以明确指定更多局部项和耦合项； 图、耦合常数和 Hamiltonian 都是模型数据。

### 14.2　可直接核对的预测

| 已声明协议 | 本模型的精确结果 |
|:---|:---|
| 两纯态 Bloch 夹角 $\theta$ | 投影概率 $(1+\cos\theta)/2$； $\theta=0,\pi/2,\pi$ 时分别为 $1,1/2,0$。 |
| 平衡两路径、标记重叠 $\mu$ | $V=\vert \mu\vert$，纯联合标记时 $D=\sqrt{1-\vert \mu\vert ^2}$。 |
| 三个正交轴间的最短闭合门 | 方向返回；旋转元为 $(1-e_2e_3)/\sqrt2$； 相应正本征旋量相位为 $-\pi/4$。 |
| $ZZ$ 相互作用与双 $+x$ 输入 | 单端口 $x$ 测试的正结果概率为 $(1+\cos gt)/2$。 |
| 有限历史的内部钟读数 $k$ | 概率 $1/(N+1)$；条件态 $U_k\cdots U_1\psi_0$。 |

这些是所定义模型的预测，不是本稿声称已新完成的实验。 当前版本没有给出区别于标准有限维量子理论的实验偏差； 若要提出新物理，需要明确修改哪项条件并重新推导可检验差异。

<a id="section-15"></a>

## 15　AURIC 接口、假设审计与研究边界

### 15.1　与已核对项目版本的对应

本稿对项目的有界核对固定于 `dev` 的提交

`ab546d9d5d2c85eda586a6feb67c6d925f66e337`

该提交在 2026 年 11 月 7 日获取。 主要读取《AURIC $\Omega$ 静态相融纤维理论》的定义 1.1–1.3、 响应商部分、有限传播与内部记录部分，以及有限关系图定义 [\[9\]](#ref-RepoOmega)；没有把整个仓库或所有历史证明视为已复核。

| 项目中的接口 | 本稿采用的准确对应 |
|:---|:---|
| 静态相融整体 | 整体包括配置、合法运输及读出； 相融不自动传递，也不要求所有配置同时可实现。 |
| 观察响应纤维 | 使用定理 11.3 的目标族等价与因子化条件。 |
| 正历史和内部时钟 | 保留记录计数、连续控制参数、变化长度和几何相位的区别。 |
| 量子表示的附加条件 | G 不承担 Q 的全部逻辑任务； 复合正性、概率与仪器条件分别声明。 |
| 静态历史与实际记录 | 采用传播约束的零空间构造； 形式路径索引与可访问记录端口分开处理。 |

项目已有的局部边缘盲区也要求保留联合相关， 与命题 7.1 一致。 上述源码阅读没有替代 Lean 构建或全部已有定理的重新验证。

### 15.2　二能级方向与 AURIC 五模式的合法接口

本稿的 $S^2$ 是一个二能级端口的纯态表示。 一个完整五维复端口的纯态空间为 $\mathbb CP^4$，实维数为八； 其一般密度态空间的仿射维数为 $5^2-1=24$。 因而不能把五模式整体无损替换成单个 Bloch 球。 若从更大端口选取二维子空间，必须检查实际控制是否保持该子空间。

#### 命题 15.1：无泄漏的二能级嵌入条件

令 $P$ 为有限空间中的秩二正交投影，$U$ 为酉门。 压缩 $K=PUP$ 在 $P\mathcal H$ 上为酉，当且仅当

$$
(I-P)UP=0.
$$

若不满足，则

$$
K^\dagger K=P-PU^\dagger(I-P)UP,
\quad
p_{\rm leak}=\operatorname{tr}[\rho U^\dagger(I-P)U]
$$

分别给出压缩的范数缺失和输入 $\rho=P\rho P$ 的泄漏概率。

**证明。**

把 $I=P+(I-P)$ 插入 $PU^\dagger UP=P$， 得到所述 $K^\dagger K$ 公式。 缺失项为 $[(I-P)UP]^\dagger[(I-P)UP]$， 故其为零当且仅当泄漏算子为零。 在同一有限二维空间上，等距即酉。 漏到正交补的概率由 Born 配对直接给出。

$\square$

此处没有声称项目全部实际门都满足该条件。 一个五模式控制菜单也不自动提供任意 $SU(2)$ 控制。 这条接口允许将方向理论接入更大关系结构，同时保留端口维数和控制权限。

### 15.3　反向检验：去掉条件会失去什么

| 被删除或混淆的条件 | 明确后果或反模型 |
|:---|:---|
| 混合概率的仿射性 M | 奇次幂概率族仍各向同性，Born 规则失去唯一性。 |
| 完整复合结构 C | 可分态复合规则仍有同样局部球，却没有一般纠缠。 |
| 辅助系统下的正性 | 矩阵转置保持单系统正性，但对 Bell 态作局部转置会出现负特征值。 |
| 理想读出的重复性 | 同一效果可连接不同制备输出，概率不能唯一确定测量更新。 |
| 完整路径和稳定子资料 | 端点关系消去闭环，无法恢复转向相位和历史。 |
| 全局 Gram 相容条件 | 每个三元可实现仍可能整体秩为四，三维拼接失败。 |
| 独立的记录结构 I | 当前状态无法区分空历史和门后逆门的历史，也无法形成全局累加时钟。 |

关于转置的反例可直接核算： $(\operatorname{id}\otimes T)(|\Phi^+\rangle\langle \Phi^+|)$ 为交换算子的一半， 谱为 $1/2,1/2,1/2,-1/2$。 这说明“在所有内生辅助关系中保持合法”确实强于孤立端口的正性。

### 15.4　已经推导的量子公理及尚未推导的部分

| 标准结构 | OTF-001 中的来源 |
|:---|:---|
| 二能级态与复射线 | G、M 的三维球经 Pauli 表示； 球面对应秩一投影与 $\mathbb CP^1$。 |
| 二值 Born 概率 | M、S 唯一推出；不是把 Euclidean 内积直接平方。 |
| 一般有限维效果概率 | C 的完整效果空间与正可加归一条件， 经定理 5.6 得到迹配对。 |
| 基本可逆酉性 | 球的仿射可逆性和恒等连通分支，经双覆盖得到。 |
| Schrödinger 形式 | 可微酉路径及 $\hbar$ 标定给自伴生成元； 具体 $H$ 仍为动力学输入。 |
| 理想秩一测量更新 | 概率效果、完全正性和重复性共同给 Lüders 仪器。 |
| 张量积与全部纠缠态 | C 中明确加入，未从单个二元几何关系唯一推出。 |
| 观察者和内部时钟 | J、I 的端口、记录、传播约束与条件化构造。 |
| 物理时空、质量和粒子统计 | 本轮未由上述条件导出；正锥只给代数桥梁。 |

量子重构已有更强的全局操作公理路线。 Masanes–Müller 从制备、变换、测量与复合条件研究量子结构， Chiribella–D’Ariano–Perinotti 使用信息原则及纯化条件 [\[7\]](#ref-MasanesMuller), [\[8\]](#ref-Chiribella)。 本稿不声称这些条件都可被“正交”一个词替代。 进一步减少 C 的输入，需要给出独立重构定理及精确的反模型排除。

### 15.5　明确保留的研究任务

1.  **复合重构：** 寻找比显式矩阵正锥更弱的内生关系条件， 并证明它们唯一选择量子张量积，而非只验证一个量子模型可以成立。

2.  **物理标定：** 从内部钟比较和传播实验建立秒、能量、距离与因果锥的对应， 再研究正矩阵锥的代数结构能否成为真实时空结构。

3.  **动力学选择：** 提出具有明确自由度、耦合与对称性的作用量或 Hamiltonian， 检验其谱、稳定性、守恒量和实验预测。

4.  **全局拼接：** 对多层二元、三元读出给出完整相容条件； 正性、秩及量子边缘问题不能由局部归一化自动代替。

5.  **新物理判别：** 若修改 Born、复合或演化条件， 必须展示与标准理论不同且可测的统计量，并检查概率与组合的一致性。

上述项目是明确的后续数学问题，而不是已由本稿证明的结论。

<a id="section-16"></a>

## 16　完整候选的白话表述

一个最小量子端口可以用球上的方向表示。 两个方向之间既有沿测量轴的重合程度，也有垂直于它的转向关系。 转向关系能生成旋转，但必须保留转角、路径和相位； 只看起点、终点会丢掉一些历史。 当我们还要求“随机混合的同一种制备不能因为换了分解方式就给出不同概率”， 并要求两个相反方向能够被可靠地区分时， 读出概率便被唯一固定为 Born 形式。 测量器和观察者由同样的量子端口及记忆构成： 记录某个结果得到条件态，忽略记录得到去相干态。 方向变化积累成可比较的变化长度， 而单向历史来自内部记录的追加；二者需要分别定义。 把时钟、系统和记忆一起写入传播约束， 整个结构可以是一个静态态，其中不同钟读数对应不同系统状态。 因而“整体静态、内部有演化”在数学上可以相容。 要进一步解释物理空间、质量、光速与唯一结果， 还必须给出新的关系条件和实验对应，不能让一个已经成立的几何恒等式 替这些问题承担尚未完成的证明。

<a id="section-A"></a>

## A　退化情形与使用约定清单

1.  $b=a$：最短门取恒等，旋转面没有唯一意义； 可有非平凡稳定子或闭合历史。

2.  $b=-a$：楔积为零，但需半周转动；最短平面不唯一。

3.  $p_s=0$：不定义该分支的归一条件态。

4.  $r=0$：最大混合态无优先纯方向，但所有合法效果概率仍有定义。

5.  $q=0$ 或 $\Delta H$ 积分为零：纯射线恒定，不能除以零定义速率下界。

6.  $\mathcal B=0$：三重积相角无定义，不套用非零重叠三角回路公式。

7.  $N=0$：传播算子为零；加入输入约束后仍可选出唯一初态射线。

8.  固定有限记忆：不能无条件延伸为无限正交时钟。

9.  所有相位角等式按模 $2\pi$；旋转元稳定子参数按模 $4\pi$。

10. 公共坐标变化与实际操作不是同一件事； 若使用随位置变化的标架，普通导数须相应换成协变导数。

<a id="section-B"></a>

## B　构建与引用说明

**转换说明：** 本节保留原稿的 XeLaTeX 构建约定；本文件为纯 Markdown，图示已改用文内文字和公式呈现。

本文为自包含 XeLaTeX 源码，内嵌图形和参考文献。 安装 `ctex`、TikZ 和 Noto CJK 字体后，连续编译两次即可。 证明为纸面数学论证，项目核对范围见第 15 节。

## 参考来源

<a id="ref-Busch"></a>

\[1\] P. Busch. Quantum states and generalized observables: a simple proof of Gleason’s theorem.     *Physical Review Letters*     **91**, 120403 (2003). <https://doi.org/10.1103/PhysRevLett.91.120403>. 预印本：<https://arxiv.org/abs/quant-ph/9909073v3>.

<a id="ref-AnandanAharonov"></a>

\[2\] J. Anandan and Y. Aharonov. Geometry of quantum evolution.     *Physical Review Letters*     **65**, 1697–1700 (1990). <https://doi.org/10.1103/PhysRevLett.65.1697>.

<a id="ref-BrodyHughston"></a>

\[3\] D. C. Brody and L. P. Hughston. Geometric quantum mechanics.  *Journal of Geometry and Physics*  **38**, 19–53 (2001). <https://doi.org/10.1016/S0393-0440(00)00052-8>. 预印本：<https://arxiv.org/abs/quant-ph/9906086v2>.

<a id="ref-SamuelBhandari"></a>

\[4\] J. Samuel and R. Bhandari. General setting for Berry’s phase.     *Physical Review Letters*     **60**, 2339–2342 (1988). <https://doi.org/10.1103/PhysRevLett.60.2339>.

<a id="ref-Englert"></a>

\[5\] B.-G. Englert. Fringe visibility and which-way information: an inequality.     *Physical Review Letters*     **77**, 2154–2157 (1996). <https://doi.org/10.1103/PhysRevLett.77.2154>.

<a id="ref-PageWootters"></a>

\[6\] D. N. Page and W. K. Wootters. Evolution without evolution: dynamics described by stationary observables.  *Physical Review D*  **27**, 2885–2892 (1983). <https://doi.org/10.1103/PhysRevD.27.2885>.

<a id="ref-MasanesMuller"></a>

\[7\] L. Masanes and M. P. Müller. A derivation of quantum theory from physical requirements.  *New Journal of Physics*  **13**, 063001 (2011). <https://doi.org/10.1088/1367-2630/13/6/063001>. 版本：<https://arxiv.org/abs/1004.1483v4>.

<a id="ref-Chiribella"></a>

\[8\] G. Chiribella, G. M. D’Ariano, and P. Perinotti. Informational derivation of quantum theory.  *Physical Review A*  **84**, 012311 (2011). <https://doi.org/10.1103/PhysRevA.84.012311>. 版本：<https://arxiv.org/abs/1011.6451v3>.

<a id="ref-RepoOmega"></a>

\[9\] The Omega Institute. AURIC $\Omega$ 静态相融纤维理论.   *trureturing*  ，固定提交 `ab546d9d5d2c85eda586a6feb67c6d925f66e337`， 本稿核对定义 1.1–1.3、响应商、有限传播与内部记录、 有限量子关系图等有界部分。 <https://github.com/the-omega-institute/trureturing/blob/ab546d9d5d2c85eda586a6feb67c6d925f66e337/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md>.

<a id="ref-RepoBlind"></a>

\[10\] The Omega Institute. Local marginal correlation blind spot.   *trureturing*  ，同一固定提交，数学说明及 Lean 源码。 <https://github.com/the-omega-institute/trureturing/blob/ab546d9d5d2c85eda586a6feb67c6d925f66e337/Blueprint/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.md>. Lean 路径为 `D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean`； 本轮阅读源码，未重新运行构建。
