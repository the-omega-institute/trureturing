# 正交时间场论 OTF-002：单态的轴面对偶与关联波

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。图示以文内文字和公式呈现。

OTF RESEARCH SERIES / 002 / VERSION 1.0

正交时间场论

单态的轴面对偶与关联波

横向复结构、量子涨落、旋量相位与内部读出

Axis-Plane Duality of a Single State\
Transverse Fluctuations and Internal Phase

**本轮核心** 一个纯态方向确定一个有向正交面，并确定其横向量子涨落核。 指定与该态相容的 Hamiltonian 后，定态的两时关联可以振荡； 相位通过整体内部的相干比较读出。

$$
Q_{\mathbf n}(\mathbf u,\mathbf v)
 =\mathbf u\cdot\mathbf v-(\mathbf u\cdot\mathbf n)(\mathbf v\cdot\mathbf n)
  +\mathrm i\,\mathbf n\cdot(\mathbf u\times\mathbf v),
 \qquad
 G_{\mathbf u\mathbf v}(t)=e^{-\mathrm i\Delta t/\hbar}Q_{\mathbf n}(\mathbf u,\mathbf v).
$$

**理论范围** 局部纯二能级端口、明确指定的有限复合系统，以及单独列出的自旋相干态比较族。 Hodge 对偶、横向标架、量子相位、时空波函数和电磁场按其数学类型分别定义。

**研究定位** 本文是 OTF-001 的独立续篇。 新组织在于把轴面对偶、最小横向核、跃迁振幅、定态关联与内部相位协议连接为完整证明链。 标准几何与量子定理均保留来源，不声称已由三维对偶推导电子、自旋量子数或真空能。

2026 年 11 月 8 日 / Asia–Singapore

项目来源固定于 `591f599ea8777d6d533451d8736d99f9a3425a85`。

本稿为普通数学证明与有界源码核对，未声称通过新的 Lean 构建或实验验证。

## 摘要

单个 Bloch 纯态方向是否已经包含与其相伴的“波”？ 本文首先证明：在定向 Euclidean 三维空间中，方向 $\mathbf n$、 单位双向量 $`B_{\mathbf n}=*\mathbf n`$、正交复线 $(\mathbf n^\perp,J_{\mathbf n})$ 及规范的秩一 Hermitian 横向核包含等价的信息。 这个结果不增加状态自由度，也不自动产生转动频率。 在二能级量子表示中，横向核恰等于 Pauli 涨落协方差； 正交复线进一步等同于 $\operatorname{Hom}_{\mathbb C}(L_{\mathbf n},L_{-\mathbf n})$， 其中 $L_{\mathbf n}$ 为对应的纯态复线。 由此得到切线丛与 Hopf 态线丛的平方对偶关系，并严格区分平面标架和旋量相位。 对于任意以 $\mathbf n$ 为本征方向的二能级 Hamiltonian， 证明定态两时关联为 $e^{-\mathrm i\Delta t/\hbar}Q_{\mathbf n}$： 方向不动、能量方差为零，与横向关联振荡可以同时成立。 随后构造只使用内部参考端口的相干读出协议，区分复关联与强顺序测量的实关联。 自旋 $j$ 的对称张量族表明，相同的轴面对偶不能确定自旋值或相位曲率系数。 全文给出混合态、零能隙、零可见度、无向平面、有限时钟采样等边界， 并将候选结构约束与 AURIC 已有相位纤维、记录相干及跨块参考合同逐项衔接。

**关键词：** Hodge 对偶；Bloch 球；量子涨落；Hopf 纤维； 关联函数；内生参考；自旋相干态。

## 目录

- [1　问题、语义与完整候选约束](#section-1)
- [2　单态轴面对偶与正交复线](#section-2)
- [3　最小横向核的几何刻画](#section-3)
- [4　二能级读出与单态量子涨落](#section-4)
- [5　正交面作为相干跃迁复线](#section-5)
- [6　Hopf 相位、横向标架与二倍权重](#section-6)
- [7　量子几何张量：从固定横向核到参数场](#section-7)
- [8　定态的横向关联波](#section-8)
- [9　方向历史、纵向相位与三个时间量](#section-9)
- [10　内部相干比较与关联的实际读出](#section-10)
- [11　自旋大小不能由同一轴面对偶唯一确定](#section-11)
- [12　粒子性、物理波包、磁矩与零点能的边界](#section-12)
- [13　全局内生闭合与静态历史表示](#section-13)
- [14　与 AURIC 固定版本的衔接与归属](#section-14)
- [15　推导范围、反例检查与研究结论](#section-15)
- [A　符号与规范约定](#section-A)
- [B　编译与核验说明](#section-B)

<a id="section-1"></a>

## 1　问题、语义与完整候选约束

本稿接受一个可证明的起点：单个纯方向已经确定其正交有向平面， 不必再任选第二个制备态。需要进一步证明的是，这个平面怎样进入相位、 不确定性和可观测关联。文中的“关联波”专指复两时关联中的相位振荡， 不预先等同于空间中传播的物质波、电磁场或真空场。

纯态方向是二能级端口的操作坐标。一根有向轴可以表示某个读出确定， 但这不意味着粒子位置被确定。后文给出空间波包不同而该方向完全相同的反例。 本文用 $\mathcal I=e_1e_2e_3$ 表示三维 Clifford 体积元， 用 $\mathrm i$ 表示复数单位，用 $I$ 表示 Hilbert 空间上的恒等算子。 全文固定 $\hbar>0$；其物理标定不由归一方向几何给出。

### 1.1　候选 AX-002

以下七条组成一个完整的有限维候选模型。它们是定义允许模型的结构约束， 不是从“存在”一词无条件推出的逻辑真理。所有物理对象都可以编码于同一整体中， 而数学上仍需明确哪些关系被要求成立。

#### 结构约束 1.1：A1：归一方向与定向度量

局部纯端口为定向三维 Euclidean 空间 $V$ 中的 $S^2$； 读出轴、内积、外积和 Hodge 算子使用同一定向度量。 定向是表示约定；不据此宣称宇宙具有绝对物理手性。

#### 结构约束 1.2：A2：混合与锐二元读出

所有有限随机混合允许，具有相同平均向量 $\mathbf r$ 的制备操作等价， 完整局部态空间为 $B^3$。概率对混合仿射。 每个单位读出轴 $\mathbf m$ 都有概率函数 $p_{\mathbf m}$， 满足 $p_{\mathbf m}(\mathbf m)=1$、$p_{\mathbf m}(-\mathbf m)=0$。

#### 结构约束 1.3：A3：横向核与量子表示

采用保持定向的旋转协变性，并选定复二能级 Pauli 表示 $X_{\mathbf u}=\mathbf u\cdot\boldsymbol{\sigma}$，满足

$$
X_{\mathbf u}X_{\mathbf v}=(\mathbf u\cdot\mathbf v)I+\mathrm iX_{\mathbf u\times\mathbf v}.
$$

这是一项明确的乘积/表示条件。第 3 节证明与它一致的 横向核可由正性、归一实部、最小复秩和定向符号唯一刻画； 该核刻画本身不代替复合系统公理。

#### 结构约束 1.4：A4：内部动力学

允许的动力学及其参数均属于整体内部模型。 局部连续闭合演化由连续、分段 $C^1$ 的幺正传播子 $U(t)$、$U(t_0)=I$ 指定；在可微处 $H(t)=\mathrm i\hbar\dot U U^\dagger$ 为相应 Hermitian 生成元。 离散门步骤在后文另按有限序列处理。 方向本身不指定 $H$、能隙、能量零点或时钟单位。

#### 结构约束 1.5：A5：复合与记录

复合端口采用有限复 Hilbert 张量积、正密度矩阵、全部效应和有限结果完全正仪器； 每个仪器的所有结果之和保持迹。 联合概率配对明确取 $p(E\mid\rho)=\operatorname{tr}(\rho E)$、$p(a\mid\rho)=\operatorname{tr}\mathcal I_a(\rho)$。 这项复合读出规则不由 A2 的局部重构自动推出。 实际记录用内部正交指针态实现。

#### 结构约束 1.6：A6：相干比较的访问合同

每个观察者具有明确协议菜单。下文相位可读定理以菜单包含指定的内部参考、 受控已知幺正和末端干涉测量为条件。若菜单只含分块读出或有相应超选限制， 不把跨块相位自动宣布为可观测量。

#### 结构约束 1.7：A7：整体内生与响应等价

系统、参考、记忆、控制和计时装置均属于整体 $\Omega$。 两个描述若对全部允许内部协议给出相同分布，即操作等价。 有限协议保留所需记录及其因果次序，并允许在更大有限整体中作幺正扩张。

#### 注 1.8

Hodge 对偶不需要第二个状态输入，但需要度量和定向。 振荡不需要第二个独立制备态，却需要动力学关系。 干涉读出不需要外部观察者，却需要整体内部可访问的相干参照。 这三个层次分别由几何、动力学和访问合同承担。

<a id="section-2"></a>

## 2　单态轴面对偶与正交复线

#### 定义 2.1：轴、面、面积形式与复结构

对 $\mathbf n\in S^2$，定义

$$
B_{\mathbf n}=*\mathbf n=\mathbf n\mathcal I,\qquad
 E_{\mathbf n}=\mathbf n^\perp,\qquad
 \Pi_{\mathbf n}=I_3-\mathbf n\mathbf n^{\mathsf T},
$$

$$
\omega_{\mathbf n}(\mathbf u,\mathbf v)=\mathbf n\cdot(\mathbf u\times\mathbf v),\qquad
 J_{\mathbf n}\mathbf v=\mathbf n\times\mathbf v\quad(\mathbf v\in E_{\mathbf n}).
$$

通过 Euclidean 平移识别，$E_{\mathbf n}$ 是球面在 $\mathbf n$ 处的切向量空间； 其中心平面 $\mathbf n^\perp$ 与过 $\mathbf n$ 的仿射切平面 $\mathbf n+\mathbf n^\perp$ 位置不同。

#### 定理 2.2：单态轴面对偶

上述结构满足

$$
\left\|B_{\mathbf n}\right\|=1,\qquad B_{\mathbf n}^{\,2}=-1,\qquad
 \mathbf nB_{\mathbf n}=\mathcal I,\qquad
 J_{\mathbf n}^2=-I_{E_{\mathbf n}}.
$$

若 $(\mathbf u,\mathbf v,\mathbf n)$ 为正向正交单位标架，则 $B_{\mathbf n}=\mathbf u\wedge\mathbf v$。此外

$$
\omega_{\mathbf n}(\mathbf u,\mathbf v)=\langle J_{\mathbf n}\mathbf u,\mathbf v\rangle.
$$

给定整体定向，$\mathbf n$、$B_{\mathbf n}$ 以及有向度量平面 $E_{\mathbf n}$ 互相唯一确定。

**证明。**

在三维 Euclidean Clifford 代数中，$\mathcal I$ 为中心元， $\mathcal I^2=-1$。故 $(\mathbf n\mathcal I)^2=\mathbf n^2\mathcal I^2=-1$， 且 $\mathbf nB_{\mathbf n}=\mathcal I$。取正向单位标架后直接得到 $\mathbf n\mathcal I=\mathbf u\mathbf v=\mathbf u\wedge\mathbf v$。 向量三重积给出 $\mathbf n\times(\mathbf n\times\mathbf v)=\mathbf n(\mathbf n\cdot\mathbf v)-\mathbf v=-\mathbf v$。 标量三重积给出最后一个内积公式。Hodge 算子在一阶和二阶外幂之间互逆， 有向正交面又具有唯一正向单位法线，因此相互唯一。

$\square$

#### 命题 2.3：没有增加自由度

映射 $\mathbf n\mapsto(\mathbf n,B_{\mathbf n})$ 的像与 $S^2$ 微分同胚， 仍只有两个实自由度。若只保留无向平面 $\mathbf n^\perp$，则该映射为二对一： $\mathbf n$ 和 $-\mathbf n$ 给出同一平面。

**证明。**

图映射的逆就是投影到第一分量，二者均光滑。 无向正交面恰有两个相反单位法线。

$\square$

因此“轴与面相伴”是同一几何信息的对偶表达。 单位双向量表示单位有向面积，不是已经装上了旋转指针的实体圆盘。 可定义半径为一的圆盘 $D_{\mathbf n}=\{\mathbf v\in E_{\mathbf n}:\left\|\mathbf v\right\|\leq1\}$， 但它的普通面积为 $\pi$，也不应与单位双向量的范数混同。

#### 定理 2.4：轴不能协变选出横向指针

不存在映射 $f:S^2\to S^2$ 同时满足 $f(\mathbf n)\perp\mathbf n$ 和 $f(R\mathbf n)=Rf(\mathbf n)$ 对所有 $R\in SO(3)$ 成立。 此结论不需要连续性假设。

**证明。**

固定 $\mathbf n$，令 $R$ 为绕 $\mathbf n$ 旋转 $\pi$ 的变换。 因 $R\mathbf n=\mathbf n$，协变性要求 $f(\mathbf n)=Rf(\mathbf n)$； 而 $f(\mathbf n)\perp\mathbf n$ 意味着 $Rf(\mathbf n)=-f(\mathbf n)$。 于是 $f(\mathbf n)=0$，与单位长度矛盾。

$\square$

#### 命题 2.5：平面旋转不等于面自身变化

绕 $\mathbf n$ 的任意旋转 $R_{\mathbf n}(\alpha)$ 满足

$$
R_{\mathbf n}(\alpha)\mathbf n=\mathbf n,\qquad
 (\Lambda^2R_{\mathbf n}(\alpha))B_{\mathbf n}=B_{\mathbf n}.
$$

所以仅给定 $(\mathbf n,B_{\mathbf n})$，不能读出一个绕轴转角 $\alpha$。

**证明。**

在 $E_{\mathbf n}$ 上旋转的行列式为 $1$，故保持其单位面积元。 也可用 Hodge 算子的 $SO(3)$ 协变性直接证明。

$\square$

**图 1：** 单态的轴面对偶。中心正交面与球面切向量空间通过平移识别； 图中的横向基不是额外“自发出现”的优选方向。

方向 $\mathbf n$ 确定有向平面 $`B_{\mathbf n}=*\mathbf n`$ 与横向空间 $E_{\mathbf n}=\mathbf n^\perp$，平面上的四分之一转为 $J_{\mathbf n}$。图中的 $\mathbf u$ 和 $J_{\mathbf n}\mathbf u$ 是展示用的局部横向基；选择指针仍需要相位参照，$\mathbf u$ 不由 $\mathbf n$ 唯一给出。

<a id="section-3"></a>

## 3　最小横向核的几何刻画

#### 定义 3.1：允许的横向 Hermitian 核

固定 $\mathbf n$。考虑 $V_{\mathbb C}=V\otimes_{\mathbb R}\mathbb C$ 上的 Hermitian 半正定形式 $C$， 采用第一变量共轭线性约定。要求对实向量满足

$$
C(\mathbf n,\mathbf v)=0,\qquad
 \operatorname{Re}C(\mathbf u,\mathbf v)
 =\mathbf u\cdot\mathbf v-(\mathbf u\cdot\mathbf n)(\mathbf v\cdot\mathbf n).
$$

具体地，若实输入的矩阵为 $M$，复输入采用 $C(z,w)=z^\dagger Mw$，第一槽共轭线性。 实向量上的虚部必为实反对称双线性形式。

#### 定理 3.2：一参数分类与最小秩

对实向量 $\mathbf u,\mathbf v$，每个这样的核唯一写成

$$
C_\lambda(\mathbf u,\mathbf v)
 =\mathbf u\cdot\Pi_{\mathbf n}\mathbf v+\mathrm i\lambda\omega_{\mathbf n}(\mathbf u,\mathbf v),
 \qquad -1\leq\lambda\leq1.
$$

其特征值为 $0,1+\lambda,1-\lambda$。 因此 $\operatorname{rank}_{\mathbb C}C_\lambda=1$ 当且仅当 $\lambda=\pm1$。 若另外规定正向单位横向对 $(\mathbf u,J_{\mathbf n}\mathbf u)$ 满足 $\operatorname{Im}C(\mathbf u,J_{\mathbf n}\mathbf u)>0$，最小秩唯一选出

$$
\boxed{Q_{\mathbf n}(\mathbf u,\mathbf v)
 =\mathbf u\cdot\mathbf v-(\mathbf u\cdot\mathbf n)(\mathbf v\cdot\mathbf n)
  +\mathrm i\mathbf n\cdot(\mathbf u\times\mathbf v).}
$$

**证明。**

轴向核条件使虚部也在 $E_{\mathbf n}$ 上定义。 二维实空间上的反对称二形式只有一个独立分量，所以虚部为 $\lambda\omega_{\mathbf n}$。在正向横向单位基中，非零块为

$$
\begin{pmatrix}1&\mathrm i\lambda\\-\mathrm i\lambda&1\end{pmatrix}.
$$

其特征值为 $1+\lambda,1-\lambda$。 半正定等价于 $|\lambda|\leq1$，秩一等价于一个特征值为零。 正向虚部的符号在两个端点中选出 $\lambda=1$。

$\square$

#### 注 3.3

该定理给出“最小复横向自由度”的精确数学版本。 正交面自身只给出实度规与面积形式；若不要求最小复秩， $\lambda=0$ 的纯实核也完全正定于横向实平面。 选出 $Q_{\mathbf n}$ 需要最小复秩与定向符号约束； 仅要求虚部非零仍允许 $0<|\lambda|<1$。 指定 Pauli 乘积是实现同一核的另一条路径， 但这个局部核刻画没有独自推出完整算符代数。 取另一整体定向得到复共轭理论，不由此产生绝对物理手性。

#### 命题 3.4：几何核的正性与信息完备性

在三维矩阵记号下，

$$
Q_{\mathbf n}=\Pi_{\mathbf n}-\mathrm iJ_{\mathbf n},
$$

其中 $J_{\mathbf n}$ 在全空间上延拓为叉乘矩阵。 若 $\mathbf u$ 为单位横向向量，$\mathbf v=J_{\mathbf n}\mathbf u$，则

$$
t=\mathbf u-\mathrm i\mathbf v,\qquad Q_{\mathbf n}=t\,t^\dagger.
$$

核的特征值为 $2,0,0$；其虚部唯一恢复 $\mathbf n$。

**证明。**

由 $\mathbf u^{\mathsf T}J_{\mathbf n}\mathbf v=-\omega_{\mathbf n}(\mathbf u,\mathbf v)$ 得矩阵式。 展开 $tt^\dagger$ 得 $\mathbf u\mathbf u^{\mathsf T}+\mathbf v\mathbf v^{\mathsf T} +\mathrm i(\mathbf u\mathbf v^{\mathsf T}-\mathbf v\mathbf u^{\mathsf T})$， 恰为 $\Pi_{\mathbf n}-\mathrm iJ_{\mathbf n}$。$t^\dagger t=2$ 给出谱。 若采用正向基，$\operatorname{Im}Q_{ab}=\epsilon_{abk}n_k$， 故 $n_k=\frac12\epsilon_{kab}\operatorname{Im}Q_{ab}$。

$\square$

<a id="section-4"></a>

## 4　二能级读出与单态量子涨落

### 4.1　Born 读出的有限维重构

#### 定理 4.1：锐仿射读出的唯一公式

在 A2 下，

$$
p_{\mathbf m}(\mathbf r)=\frac{1+\mathbf m\cdot\mathbf r}{2}.
$$

**证明。**

仿射函数写成 $p(\mathbf r)=a+\mathbf b\cdot\mathbf r$。 在整个单位球取值于 $[0,1]$ 要求 $\left\|\mathbf b\right\|\leq\min(a,1-a)$。 两个锐端点给出 $a=1/2$ 和 $\mathbf b\cdot\mathbf m=1/2$。 Cauchy–Schwarz 不等式因此取等，得到 $\mathbf b=\mathbf m/2$。

$\square$

令

$$
\rho(\mathbf r)=\frac12(I+\mathbf r\cdot\boldsymbol{\sigma}),\qquad
 P_{\mathbf n}=\frac12(I+\mathbf n\cdot\boldsymbol{\sigma}).
$$

$\rho(\mathbf r)$ 的特征值为 $(1\pm\left\|\mathbf r\right\|)/2$， 从而 $B^3$ 与二能级密度矩阵一一对应，且 $p_{\mathbf m}(\mathbf r)=\operatorname{tr}(\rho(\mathbf r)P_{\mathbf m})$。 这一表示沿用 OTF-001 的条件重构。 不满足混合仿射性的函数 $[1+(\mathbf m\cdot\mathbf r)^3]/2$ 说明单独的各向同性并不确定此公式。

#### 命题 4.2：单态对偶面与虚数作用的精确关系

在 Pauli 表示 $e_a\mapsto\sigma_a$ 下，

$$
\mathcal I\mapsto\mathrm iI,\qquad
 B_{\mathbf n}=\mathbf n\mathcal I\mapsto\mathrm iX_{\mathbf n}.
$$

因此 $B_{\mathbf n}$ 在 $L_{\mathbf n}$ 上作用为 $\mathrm i$， 在 $L_{-\mathbf n}$ 上作用为 $-\mathrm i$。 每个 $\operatorname{span}_{\mathbb R}\{1,B_{\mathbf n}\}$ 都是一个复数子代数， 但 $B_{\mathbf n}$ 不是在整个二能级空间上统一作用的中心复单位。

**证明。**

$\sigma_1\sigma_2\sigma_3=\mathrm iI$ 给出第一个映射； 再乘 $X_{\mathbf n}$ 得第二个映射。 $X_{\mathbf n}$ 在两态线上分别取特征值 $\pm1$。 最后 $B_{\mathbf n}^2=-1$ 给出所述二维实子代数。

$\square$

#### 命题 4.3：赤道的操作含义

对纯态 $P_{\mathbf n}$，单位读出轴 $\mathbf m\in E_{\mathbf n}$ 的两个结果概率均为 $1/2$； 唯一概率为零的正向锐事件是 $P_{-\mathbf n}$。

**证明。**

分别代入 $\mathbf m\cdot\mathbf n=0$ 与 $\mathbf m\cdot\mathbf n=-1$。 单位向量内积等于 $-1$ 当且仅当 $\mathbf m=-\mathbf n$。

$\square$

所以 Bloch 赤道是一族无偏读出轴。 它不是 Hilbert 意义下“一整圈与 $|\mathbf n\rangle$ 正交的纯态”； 二能级中与 $L_{\mathbf n}$ 正交的态射线只有 $L_{-\mathbf n}$。

### 4.2　横向核就是量子协方差

#### 定义 4.4：中心化 Pauli 读出

在纯态 $P_{\mathbf n}$ 中定义

$$
X_{\mathbf u}=\mathbf u\cdot\boldsymbol{\sigma},\qquad
 \delta X_{\mathbf u}=X_{\mathbf u}-(\mathbf u\cdot\mathbf n)I.
$$

#### 定理 4.5：单态轴面对偶的操作实现

对任意实向量 $\mathbf u,\mathbf v$，

$$
\boxed{\operatorname{tr}(P_{\mathbf n}\,\delta X_{\mathbf u}\delta X_{\mathbf v})=Q_{\mathbf n}(\mathbf u,\mathbf v).}
$$

特别地，

$$
\operatorname{Var}_{P_{\mathbf n}}(X_{\mathbf u})
 =\left\|\mathbf u\right\|^2-(\mathbf u\cdot\mathbf n)^2,
$$

$$
\frac1{2\mathrm i}\langle[X_{\mathbf u},X_{\mathbf v}]\rangle_{P_{\mathbf n}}
 =\mathbf n\cdot(\mathbf u\times\mathbf v).
$$

**证明。**

由 A3， $X_{\mathbf u}X_{\mathbf v}=(\mathbf u\cdot\mathbf v)I+\mathrm iX_{\mathbf u\times\mathbf v}$。 对 $P_{\mathbf n}$ 取期望后，得到 $\mathbf u\cdot\mathbf v+\mathrm i\mathbf n\cdot(\mathbf u\times\mathbf v)$。 再减去两个均值之积即得 $Q_{\mathbf n}$。取对角或反对称部分给出余式。

$\square$

#### 推论 4.6：轴向确定与横向不确定共存

若 $(\mathbf u,\mathbf v,\mathbf n)$ 为正向正交单位标架，则

$$
\operatorname{Var}(X_{\mathbf n})=0,\qquad
 \operatorname{Var}(X_{\mathbf u})=\operatorname{Var}(X_{\mathbf v})=1,
$$

$$
Q_{\mathbf n}(\mathbf u,\mathbf v)=\mathrm i,\qquad
 \Delta X_{\mathbf u}\,\Delta X_{\mathbf v}
 =\frac12|\langle[X_{\mathbf u},X_{\mathbf v}]\rangle|=1.
$$

若这些算子被物理解释为自旋 $S_{\mathbf u}=(\hbar/2)X_{\mathbf u}$， 则 $\Delta S_{\mathbf u}=\Delta S_{\mathbf v}=\hbar/2$。

**证明。**

将正交单位关系代入定理 4.5。

$\square$

这是一种严格的“单态自带横向量子结构”。 它描述非对易测量的涨落和相关关系，并不意味着同一粒子已经具有一组同时确定、 沿圆盘运动的隐藏横向数值。

#### 定理 4.7：完整混合态边界

在 $\rho(\mathbf r)$ 中，相应协方差矩阵为

$$
Q(\mathbf r)_{ab}=\delta_{ab}-r_ar_b+\mathrm i\epsilon_{abk}r_k.
$$

令 $s=\left\|\mathbf r\right\|\in[0,1]$，其特征值为

$$
1+s,\qquad1-s,\qquad1-s^2.
$$

因此纯态 $s=1$ 时复秩为一；$s<1$ 时复秩为三； $s=0$ 时没有优选轴。

**证明。**

将 $\mathbf r$ 旋转到 $(0,0,s)$。 横向块为 $\bigl(\begin{smallmatrix}1&\mathrm is\\-\mathrm is&1\end{smallmatrix}\bigr)$， 纵向项为 $1-s^2$。这给出全部特征值，包括两个端点。

$\square$

<a id="section-5"></a>

## 5　正交面作为相干跃迁复线

#### 定义 5.1：态线与跃迁算子

定义 $L_{\mathbf n}=\operatorname{ran}P_{\mathbf n}$、 $L_{-\mathbf n}=\operatorname{ran}P_{-\mathbf n}$，以及

$$
K_{\mathbf n}(\mathbf u)=P_{-\mathbf n}X_{\mathbf u}P_{\mathbf n},\qquad \mathbf u\in E_{\mathbf n}.
$$

两个态线由 $\mathbf n$ 唯一确定；不需要任选另一个独立纯态。

#### 定理 5.2：横向复线与跃迁复线同构

映射

$$
K_{\mathbf n}:(E_{\mathbf n},J_{\mathbf n})\longrightarrow
 \operatorname{Hom}_{\mathbb C}(L_{\mathbf n},L_{-\mathbf n})
$$

为复线性等距同构。具体地，

$$
K_{\mathbf n}(J_{\mathbf n}\mathbf u)=\mathrm iK_{\mathbf n}(\mathbf u),
$$

$$
\operatorname{tr}\!\left(K_{\mathbf n}(\mathbf u)^\dagger K_{\mathbf n}(\mathbf v)\right)
 =Q_{\mathbf n}(\mathbf u,\mathbf v).
$$

**证明。**

对 $\psi\in L_{\mathbf n}$ 有 $X_{\mathbf n}\psi=\psi$。 若 $\mathbf u\perp\mathbf n$，反对易关系给出 $X_{\mathbf n}X_{\mathbf u}\psi=-X_{\mathbf u}\psi$，故 $X_{\mathbf u}\psi\in L_{-\mathbf n}$。 又由 $X_{\mathbf n}X_{\mathbf u}=\mathrm iX_{\mathbf n\times\mathbf u}$， 得 $X_{J_{\mathbf n}\mathbf u}\psi=\mathrm iX_{\mathbf u}\psi$。 所以映射复线性。 在单位 $\psi\in L_{\mathbf n}$ 上， $\operatorname{tr}(K(\mathbf u)^\dagger K(\mathbf v)) =\langle X_{\mathbf u}\psi,X_{\mathbf v}\psi\rangle=Q_{\mathbf n}(\mathbf u,\mathbf v)$。 特别地，$K(\mathbf u)=0$ 蕴含 $\left\|\mathbf u\right\|=0$。 两端均为一维复空间，因此单射即同构。

$\square$

#### 注 5.3

有向正交面提供一个可以容纳相干跃迁振幅的复线空间。 它没有选出该空间中某个非零向量，也没有为这个向量指定角速度。 这一区分保留了“内禀对应面”的正确部分，同时明确了相位和动力学需要的数据。

<a id="section-6"></a>

## 6　Hopf 相位、横向标架与二倍权重

### 6.1　两个不同的纤维映射

#### 定义 6.1：Hopf 态线丛

令

$$
h:S^3\subset\mathbb C^2\longrightarrow S^2,\qquad
 h(\psi)=\psi^\dagger\boldsymbol{\sigma}\psi.
$$

其对应复线丛记为 $L$，纤维 $L_{\mathbf n}=\operatorname{ran}P_{\mathbf n}$。

#### 定理 6.2：相位纤维

$h(\psi)=h(\phi)$ 当且仅当存在 $\chi\in\mathbb R$ 使 $\phi=e^{\mathrm i\chi}\psi$。因此每个纤维为一个 $U(1)$ 圆。

**证明。**

同一 Bloch 向量给出同一秩一投影 $\psi\psi^\dagger=\phi\phi^\dagger$； 两个单位向量张成同一复线，当且仅当相差单位复标量。

$\square$

令 $C(z_0,z_1)=(-\bar z_1,\bar z_0)$。 对单位 $\psi$，

$$
U_\psi=[\psi,C\psi]\in SU(2).
$$

它通过共轭 Pauli 矩阵给出一个三维正向标架。

#### 定理 6.3：相位与横向标架的二倍关系

若 $\psi\mapsto e^{\mathrm i\chi}\psi$，则

$$
U_\psi\longmapsto
 U_\psi\begin{pmatrix}e^{\mathrm i\chi}&0\\0&e^{-\mathrm i\chi}\end{pmatrix}.
$$

因此横向实标架绕 $\mathbf n$ 旋转 $-2\chi$，而 $\mathbf n$ 不变。 单位旋量到完整标架的映射为 $S^3\to SO(3)$ 的二对一覆盖； 它与 $S^3\to S^2$ 的整圆相位纤维不同。

**证明。**

反线性给出 $C(e^{\mathrm i\chi}\psi)=e^{-\mathrm i\chi}C\psi$。 右乘矩阵等于 $\exp(\mathrm i\chi\sigma_3)$，在 Pauli 共轭作用下对应 绕第三轴旋转 $-2\chi$。只有 $\psi$ 和 $-\psi$ 给出相同完整标架， 而所有 $e^{\mathrm i\chi}\psi$ 都给出相同 $\mathbf n$。

$\square$

#### 推论 6.4：切线丛是态线丛的平方对偶

以 $J_{\mathbf n}\mathbf u=\mathbf n\times\mathbf u$ 为复结构，有

$$
(TS^2,J)\simeq\operatorname{Hom}_{\mathbb C}(L,L^\perp)\simeq(L^*)^{\otimes2}.
$$

**证明。**

第一个同构由定理 5.2 逐纤维给出，且依赖 $\mathbf n$ 光滑。 固定 $\mathbb C^2$ 的标准行列式体积形式后， $`L^\perp\simeq L^*`$，因为 $L\otimes L^\perp\simeq\det\mathbb C^2$ 为平凡复线。 于是 $`\operatorname{Hom}(L,L^\perp)\simeq L^*\otimes L^\perp\simeq(L^*)^{\otimes2}`$。

$\square$

等价地，绕 $\mathbf n$ 主动转动 $\alpha$ 时，横向复向量具有权重 $e^{\mathrm i\alpha}$， 而正向自旋量子代表具有权重 $e^{-\mathrm i\alpha/2}$。 因此一张普通平面中的指针不能未经二重覆盖就当作自旋量子相位。

### 6.2　Berry 联络与全局截面障碍

取北极局部代表

$$
\psi_N(\theta,\phi)=
 \begin{pmatrix}\cos(\theta/2)\\e^{\mathrm i\phi}\sin(\theta/2)\end{pmatrix}.
$$

定义 $A=\mathrm i\psi^\dagger\mathrm d\psi$，则

$$
A_N=-\frac{1-\cos\theta}{2}\mathrm d\phi,\qquad
 F=\mathrm dA=-\frac12\sin\theta\,\mathrm d\theta\wedge\mathrm d\phi.
$$

相位改写 $\psi\mapsto e^{\mathrm i\chi}\psi$ 使 $A\mapsto A-\mathrm d\chi$。 本文采用此约定，故

$$
\frac1{2\pi}\int_{S^2}F=-1.
$$

相应切线复线丛的第一 Chern 数为 $+2$。

#### 定理 6.5：不存在连续全局相位代表

Hopf 映射没有连续全局截面；球面上也不能连续选择处处非零的横向指针。

**证明。**

若 Hopf 映射存在连续截面 $s$， $(\mathbf n,e^{\mathrm i\chi})\mapsto e^{\mathrm i\chi}s(\mathbf n)$ 将给出 $S^2\times S^1$ 与 $S^3$ 的连续双射。 紧致性和 Hausdorff 性使其为同胚，但二者基本群分别为 $\mathbb Z$ 与 $0$， 矛盾。横向指针则是 $TS^2$ 的非零截面； 其存在会平凡化该复线丛，与 Chern 数 $2$ 矛盾。

$\square$

这些相位与联络结构属于标准几何量子力学及几何相位理论 [\[2\]](#ref-berry), [\[3\]](#ref-simon), [\[4\]](#ref-brody)。Hestenes 对旋量相位与正交旋转平面的讨论提供了直接相关的 几何代数前例，但其论证使用已给定的 Dirac/时空结构[\[1\]](#ref-hestenes)； 不能把其中的物理输入删去后声称三维 Hodge 对偶已经独立导出电子理论。

<a id="section-7"></a>

## 7　量子几何张量：从固定横向核到参数场

#### 定义 7.1：量子几何张量

设 $x\mapsto\mathbf n(x)$ 为光滑参数场，$\psi(x)$ 为局部归一代表， 令 $P(x)=\psi(x)\psi(x)^\dagger$。定义

$$
T_{\mu\nu}
 =\langle\partial_\mu\psi,(I-P)\partial_\nu\psi\rangle.
$$

它在 $\psi\mapsto e^{\mathrm i\chi(x)}\psi$ 下不变。

#### 定理 7.2：单态涨落核的拉回

有

$$
\boxed{
 T_{\mu\nu}
 =\frac14\left[
 \partial_\mu\mathbf n\cdot\partial_\nu\mathbf n
 +\mathrm i\mathbf n\cdot
   (\partial_\mu\mathbf n\times\partial_\nu\mathbf n)
 \right]
 =\frac14\partial_\mu n_a\,Q_{ab}\,\partial_\nu n_b.}
$$

其几何度规与 Berry 曲率为

$$
g_{\mu\nu}=\operatorname{Re}T_{\mu\nu},\qquad
 F_{\mu\nu}=-2\operatorname{Im}T_{\mu\nu}.
$$

**证明。**

秩一投影求导给 $T_{\mu\nu}=\operatorname{tr}(P\,\partial_\mu P\,\partial_\nu P)$。 由 $\partial_\mu P=(\partial_\mu\mathbf n)\cdot\boldsymbol{\sigma}/2$， Pauli 乘积给出第一式。单位约束使 $\mathbf n\cdot\partial_\mu\mathbf n=0$，故等于 $Q_{\mathbf n}$ 的拉回。 最后对 $A=\mathrm i\psi^\dagger\mathrm d\psi$ 求外微分， 得 $F_{\mu\nu}=\mathrm i(\langle\partial_\mu\psi,\partial_\nu\psi\rangle -\langle\partial_\nu\psi,\partial_\mu\psi\rangle) =-2\operatorname{Im}T_{\mu\nu}$。

$\square$

几何度规与 Berry 曲率通过量子几何张量统一，是已有几何量子理论的重要结构。 针对受控二能级系统的实验也已用相干响应测量该张量[\[5\]](#ref-yu)。 本稿的作用是给出它与单态轴面对偶、横向协方差之间的明确公式。

#### 命题 7.3：固定对偶面与场强不是同一对象

若 $\mathbf n(x)$ 为常值，则 $Q_{\mathbf n}$ 仍为非零秩一核， 但拉回的 $T$ 和 $F$ 都为零。 对任意 $\mathbf n:M\to S^2$，有 $\operatorname{rank}g\leq2$ 且 $F\wedge F=0$。

**证明。**

常值场的导数为零。一般情形下，$\mathrm d\mathbf n$ 的像至多二维， 故拉回度规秩至多二。又 $F$ 是球面二形式的拉回， 而该二形式在二维球面上的平方为零，故 $F\wedge F=0$。

$\square$

因此本模型中的参数空间曲率不自动等于电子在物理时空中的磁场。 例如一般四维电磁二形式可以满足 $F_{\rm EM}\wedge F_{\rm EM}\ne0$； 它不能全部由一个 $S^2$ 方向场的上述拉回来表示。

<a id="section-8"></a>

## 8　定态的横向关联波

### 8.1　所有相容 Hamiltonian 的分类

#### 定理 8.1：固定纯态不确定其能隙

一个二阶 Hermitian 算子 $H$ 保持纯态 $P_{\mathbf n}$ 静止， 即 $[H,P_{\mathbf n}]=0$，当且仅当

$$
H=E_+P_{\mathbf n}+E_-P_{-\mathbf n}
 \qquad(E_+,E_-\in\mathbb R).
$$

所以同一 $(\mathbf n,B_{\mathbf n},Q_{\mathbf n})$ 允许任意有向能隙 $\Delta=E_--E_+$，也允许任意共同能量平移。

**证明。**

对秩一投影的对易关系使 $H$ 在 $L_{\mathbf n}\oplus L_{-\mathbf n}$ 分解下分块对角。 每个块为一维，Hermitian 性使其系数为实数。 反方向直接代入即可。

$\square$

#### 定义 8.2：定态两时关联核

在 $P_{\mathbf n}$ 中，令

$$
\delta X_{\mathbf u}(t)
 =e^{\mathrm iHt/\hbar}\delta X_{\mathbf u}e^{-\mathrm iHt/\hbar},
 \qquad
 G_{\mathbf u\mathbf v}(t)
 =\operatorname{tr}\bigl(P_{\mathbf n}\,\delta X_{\mathbf u}(t)\delta X_{\mathbf v}(0)\bigr).
$$

时间标签由 A4 指定；第 10 节将有限次读出放回内部时钟协议。

#### 定理 8.3：单态关联波主定理

对上述 $H$ 与任意实 $\mathbf u,\mathbf v$，

$$
\boxed{
 G_{\mathbf u\mathbf v}(t)
 =e^{-\mathrm i\Delta t/\hbar}Q_{\mathbf n}(\mathbf u,\mathbf v),
 \qquad \Delta=E_--E_+.}
$$

因此方向 $\mathbf n$ 和密度矩阵完全不动时，横向关联仍可振荡。

**证明。**

取单位 $\psi\in L_{\mathbf n}$。 中心化消去纵向分量，故 $\delta X_{\mathbf v}\psi\in L_{-\mathbf n}$。 于是

$$
\begin{aligned}
 G_{\mathbf u\mathbf v}(t)
 &=\langle\psi,
  e^{\mathrm iHt/\hbar}\delta X_{\mathbf u}
  e^{-\mathrm iHt/\hbar}\delta X_{\mathbf v}\psi\rangle\\
 &=e^{\mathrm iE_+t/\hbar}e^{-\mathrm iE_-t/\hbar}
   \langle\psi,\delta X_{\mathbf u}\delta X_{\mathbf v}\psi\rangle\\
 &=e^{-\mathrm i\Delta t/\hbar}Q_{\mathbf n}(\mathbf u,\mathbf v).
 \end{aligned}
$$

最后一步使用定理 4.5。

$\square$

#### 推论 8.4：静止态、零能量方差与关联振荡共存

若 $H=E_0P_{\mathbf n}+(E_0+\Delta)P_{-\mathbf n}$ 且 $\Delta>0$， 则 $P_{\mathbf n}$ 为非简并基态，且

$$
\Delta H=0,\qquad
 \dot\mathbf n=0,\qquad
 G_{\mathbf u\mathbf u}(t)=e^{-\mathrm i\Delta t/\hbar}
$$

对任意单位横向 $\mathbf u$ 成立。 同一模型允许 $E_0=0$。

**证明。**

$H\psi=E_0\psi$，故能量方差为零且密度矩阵不变。 单位横向读出的 $Q_{\mathbf n}(\mathbf u,\mathbf u)=1$。

$\square$

此处“波”指关联核的相位模式；它不是基态密度矩阵正在沿球面旋转。 涨落在定态中存在，也不自动意味着存在一个正的、由方向几何决定的零点能。

#### 例 8.5：完全显式的北极模型

令 $\mathbf n=e_3$，

$$
H=\begin{pmatrix}0&0\\0&\Delta\end{pmatrix},
 \qquad \psi=\begin{pmatrix}1\\0\end{pmatrix},
 \qquad \nu=\Delta/\hbar.
$$

则

$$
Q=
 \begin{pmatrix}1&\mathrm i&0\\-\mathrm i&1&0\\0&0&0\end{pmatrix},
 \qquad
 G_{11}(t)=e^{-\mathrm i\nu t},\qquad
 G_{12}(t)=\mathrm ie^{-\mathrm i\nu t}.
$$

所以 $\operatorname{Re}G_{11}=\cos\nu t$， $\operatorname{Re}G_{12}=\sin\nu t$。 若 $\Delta=0$，这些关联退化为常数，虽然正交面与横向方差仍存在。

**图 2：** 同一静止北极态的横向关联。图示横轴为无量纲能隙历时； 其振荡不要求 $\mathbf n$ 发生变化。

横轴 $s=\Delta t/\hbar$ 为无量纲能隙历时。在 $0\leq s\leq2\pi$ 的一周中，实部为 $\operatorname{Re}G_{11}=\cos s$，虚部为 $\operatorname{Im}G_{11}=-\sin s$，振幅均为一；两者分别呈现余弦和负正弦变化。

#### 命题 8.6：能量平移不变与频率可识别边界

$H\mapsto H+cI$ 不改变 $G_{\mathbf u\mathbf v}(t)$。 若已标定连续时间并知道单位横向自关联的全部局部复值， 则 $\Delta=\mathrm i\hbar G'_{\mathbf u\mathbf u}(0)$ 唯一。 若以 $\tau>0$ 只在 $t=k\tau$ 取样，且包含 $k=1$，则只能识别

$$
\Delta\quad\bmod\quad\frac{2\pi\hbar}{\tau}.
$$

**证明。**

共同平移不改变 $E_--E_+$。 由 $G_{\mathbf u\mathbf u}(t)=e^{-\mathrm i\Delta t/\hbar}$ 求导得第二项。 离散样本对两个能隙相同，当且仅当 $e^{-\mathrm i(\Delta'-\Delta)\tau/\hbar}=1$， 即 $\Delta'-\Delta\in(2\pi\hbar/\tau)\mathbb Z$。

$\square$

<a id="section-9"></a>

## 9　方向历史、纵向相位与三个时间量

#### 定理 9.1：给定方向历史的全部局部生成元

设 $\mathbf n(t)\in S^2$ 可微，写

$$
H=h_0I+\frac{\hbar}{2}\boldsymbol\omega\cdot\boldsymbol{\sigma}.
$$

它产生指定方向历史，当且仅当

$$
\dot\mathbf n=\boldsymbol\omega\times\mathbf n,
 \qquad
 \boldsymbol\omega=\mathbf n\times\dot\mathbf n+\chi\mathbf n
$$

对某个实函数 $\chi(t)$ 成立。 若 $\psi(t)=e^{\mathrm i\alpha(t)}s(\mathbf n(t))$ 为局部代表，则

$$
\dot\alpha
 =A(\dot\mathbf n)-\frac{h_0}{\hbar}-\frac{\chi}{2}.
$$

**证明。**

Pauli 对易关系给出 Bloch 方程。 对 $\boldsymbol\omega\times\mathbf n=\dot\mathbf n$ 左侧再与 $\mathbf n$ 作叉积， 得到 $\boldsymbol\omega-(\boldsymbol\omega\cdot\mathbf n)\mathbf n =\mathbf n\times\dot\mathbf n$；令 $\chi=\boldsymbol\omega\cdot\mathbf n$。 对 Schrödinger 方程取 $\psi$ 的期望，

$$
\mathrm i\hbar\langle\psi,\dot\psi\rangle
 =-\hbar\dot\alpha+\hbar A(\dot\mathbf n)
 =h_0+\hbar\chi/2.
$$

整理即得。

$\square$

因此知道整条方向轨迹，仍不能恢复全部纵向相位动力学。 这不是丢失了某个由 Hodge 算子本来能够计算的数，而是状态轨迹对生成元具有非唯一性。

#### 反例 9.2：从代表相位重建的标架不等于实际转动

取 $H=cI$。真实传播 $U(t)=e^{-\mathrm ict/\hbar}I$ 对全部 Pauli 算子的共轭作用均为恒等。 但若每个时刻都按定理 6.3 从 $\psi(t)=e^{-\mathrm ict/\hbar}\psi(0)$ 重建 $U_{\psi(t)}$， 其横向标架转角为 $2ct/\hbar$。 该转角随任意能量零点改变，所以不能称为状态真实的可观测圆盘转动。

#### 定义 9.3：三个不同的时间相关量

对纯态方向路径定义几何历时

$$
q[\gamma]=\frac12\int_\gamma\left\|\mathrm d\mathbf n\right\|.
$$

对两能级关联定义能隙相位 $\varphi_\Delta(t)=\int_0^t\Delta(s)\mathrm ds/\hbar$， 其中时间依赖对角模型使用固定本征轴。 对实际计入的事件定义记录历时 $\tau_{\rm rec}(k)=\sum_{j=1}^k w_j$，$w_j>0$。

OTF-001 已证明 $q$ 是纯态 Fubini–Study 长度， 且闭合 Schrödinger 演化满足 $\dot q=\Delta H/\hbar$。 在定理 8.3 的静止本征态中，$q=0$， 但能隙相位可以增加。两者描述不同关系，因此并不矛盾。 下一节进一步证明：当两个支路权重均非零且相对相位变化时， 相位读出所需的内部联合态具有非零几何长度。

<a id="section-10"></a>

## 10　内部相干比较与关联的实际读出

### 10.1　内部参考端口的精确协议

#### 定理 10.1：双支路干涉公式

设 $C$ 为整体内部的二能级路径端口，$S$ 初态为 $\rho$。 制备 $C$ 于 $(|0\rangle+e^{\mathrm i\phi}|1\rangle)/\sqrt2$， 并施加已指定的受控幺正

$$
U_{\rm ctl}=|0\rangle\langle 0|\otimes U_0+|1\rangle\langle 1|\otimes U_1.
$$

对 $C$ 测量 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，则

$$
\boxed{p_+(\phi)=\frac12
 \left[1+\operatorname{Re}(e^{\mathrm i\phi}z)\right],\quad
 z=\operatorname{tr}(\rho U_0^\dagger U_1).}
$$

扫描 $\phi$ 的可见度为 $|z|$。

**证明。**

纯态情形的输出为 $(|0\rangle U_0\psi+e^{\mathrm i\phi}|1\rangle U_1\psi)/\sqrt2$。 投影到 $|+\rangle$ 后的平方范数即为所示概率。 对任意混合态用凸线性延拓。 最大最小概率分别为 $(1\pm|z|)/2$，故可见度为 $|z|$。

$\square$

#### 推论 10.2：无需第二个独立制备态

同一输入 $\psi$ 的两条相干内部历史即可读出相位。 若 $U_1\psi=e^{\mathrm i\eta}U_0\psi$，则两条历史的系统末端 Bloch 向量相同， 但

$$
p_+(\phi)=\frac12[1+\cos(\phi+\eta)].
$$

相位 $\eta$ 属于两条历史的关系，不由任意一个末端方向单独恢复。

**证明。**

代入 $z=e^{\mathrm i\eta}$。

$\square$

#### 命题 10.3：通道不能独自指定受控实现

对系统而言，$U$ 与 $e^{\mathrm i\eta}U$ 定义相同通道 $\rho\mapsto U\rho U^\dagger$。但以它们作为某一支路的相干受控实现， 在定理 10.1 中一般给出不同概率。 因此仅有系统 CPTP 通道、SO(3) 转向或端点数据不足以指定该相干协议。

**证明。**

通道中的相位与其共轭抵消；交叉项 $z$ 中只出现某一支路的相位， 故变为 $e^{\mathrm i\eta}z$。

$\square$

这也说明为什么 A6 必须保留实际相干实现。 不能把一个只给出黑盒系统通道的接口，自动当作提供了任意受控版本。 改变同一整个系统的共同代表相位不影响任何概率； 只对一个相干支路施加相位，则已经改变了联合系统中的相对关系。 Ramsey 型实验正是相对相位影响读出信号的经典物理背景之一[\[6\]](#ref-ramsey)。

### 10.2　复关联与强顺序测量

#### 定理 10.4：用内部辅助端口读取复关联

令 $\mathbf u,\mathbf v$ 为单位横向向量，

$$
V=X_{\mathbf u}(t)X_{\mathbf v}.
$$

$V$ 为幺正，且在 $P_{\mathbf n}$ 中 $\operatorname{tr}(P_{\mathbf n}V)=G_{\mathbf u\mathbf v}(t)$。 在定理 10.1 中取 $U_0=I,U_1=V$， 则 $\phi=0$ 读取 $\operatorname{Re}G$， $\phi=-\pi/2$ 读取 $\operatorname{Im}G$。

**证明。**

单位 Pauli 读出及其幺正共轭均为 Hermitian 幺正， 故其乘积为幺正。横向读出均值为零，不需要中心化修正。 分别代入两种相位，利用 $\operatorname{Re}(-\mathrm iz)=\operatorname{Im}z$。

$\square$

#### 定理 10.5：强顺序投影测量的乘积均值

令 $A=A^\dagger$、$B=B^\dagger$ 且 $A^2=B^2=I$。 先对 $B$ 作 Lüders 测量，演化 $U(t)$， 再对 $A$ 作投影测量。两次 $\pm1$ 结果的乘积均值为

$$
\mathbb E[ab]
 =\frac12\operatorname{tr}\bigl(\rho\{A(t),B\}\bigr)
 =\operatorname{Re}\operatorname{tr}(\rho A(t)B),
 \qquad A(t)=U^\dagger AU.
$$

**证明。**

令 $P_b=(I+bB)/2$。对第一结果求加权和，有

$$
\sum_{b=\pm1}bP_b\rho P_b=\frac12(B\rho+\rho B).
$$

第二次测量的加权和为 $A$，故总乘积均值等于 $\operatorname{tr}[A(t)(B\rho+\rho B)]/2$。利用迹循环即得。

$\square$

因此不能将非实的 $G$ 直接解释为一对已经存在的实数记录的乘积均值。 但更换读出轴可以构造不同强测量协议：北极例中， 同轴读出得到 $\cos\nu t$，正交横向读出得到 $\sin\nu t$。 这仍然是包含测量扰动的两个协议，不能据此删除测量过程。

### 10.3　相位参考的几何历时补偿

#### 定理 10.6：联合态中的相位运动

设 $|\phi_0\rangle,|\phi_1\rangle$ 为固定单位系统态， $p+q=1$、$p,q\geq0$，并令

$$
|\Psi(\varphi)\rangle
 =\sqrt p\,|0\rangle|\phi_0\rangle
 +e^{\mathrm i\varphi}\sqrt q\,|1\rangle|\phi_1\rangle.
$$

采用 $ds_{\rm FS}^2=\langle\mathrm d\Psi,\mathrm d\Psi\rangle -|\langle\Psi,\mathrm d\Psi\rangle|^2$，有

$$
ds_{\rm FS}^2=pq\,\mathrm d\varphi^2.
$$

若 $H_{\rm rel}=\Delta|1\rangle\langle 1|\otimes I$， 则 $\dot\varphi=-\Delta/\hbar$，

$$
\frac{\mathrm dq_{\rm joint}}{\mathrm dt}
 =\frac{|\Delta|\sqrt{pq}}{\hbar}
 =\frac{\Delta H_{\rm rel}}{\hbar}.
$$

**证明。**

路径标签正交，故 $\langle\partial_\varphi\Psi,\partial_\varphi\Psi\rangle=q$， $\langle\Psi,\partial_\varphi\Psi\rangle=\mathrm iq$。 相减得 $q-q^2=pq$，与两系统末态的内积无关。 $H_{\rm rel}$ 的结果为 $0,\Delta$，概率为 $p,q$， 故方差为 $\Delta^2pq$。余式直接得到。

$\square$

孤立定态的方向可以完全静止；当 $0<p,q<1$ 且相对相位发生变化时， 内部参考联合态仍发生变化。 平衡支路的联合速度为 $|\Delta|/(2\hbar)$。 $p=0$ 或 $q=0$ 时没有相干两支路，度规退化为零，边界亦符合解释。

#### 命题 10.7：记录重叠控制可见度

若两支路还留下单位记录 $|e_0\rangle,|e_1\rangle$， 则干涉系数变为

$$
z_{\rm rec}
 =\langle U_0\psi,U_1\psi\rangle
   \langle e_0,e_1\rangle.
$$

完全正交的支路记录使忽略记录后的条纹可见度为零。

**证明。**

对记录系统作偏迹时，非对角路径块乘上 $\langle e_1,e_0\rangle$；在末端概率中得到上述等价共轭配对。 直接展开联合纯态也可验证。

$\square$

<a id="section-11"></a>

## 11　自旋大小不能由同一轴面对偶唯一确定

#### 定义 11.1：自旋相干比较族

令 $q=2j$ 为正整数， $\mathcal H_j=\operatorname{Sym}^{q}(\mathbb C^2)$， 在每个局部规范中选择归一代表 $\psi_{\mathbf n}$，并在其中取

$$
|\mathbf n;j\rangle=\psi_{\mathbf n}^{\otimes q},\qquad
 S_a=\frac{\hbar}{2}\sum_{\ell=1}^{q}\sigma_a^{(\ell)}.
$$

维数为 $2j+1$。全局对象是该向量的射线或秩一投影； 不假定 $\psi_{\mathbf n}$ 存在连续全局选择。 当 $j>1/2$ 时，该方向球只是全部纯态空间中的相干态子族。

#### 定理 11.2：共同方向、不同自旋与不同相位权重

对全部上述 $j$，

$$
\langle\mathbf S\rangle=j\hbar\mathbf n,
$$

$$
\langle\delta S_a\delta S_b\rangle
 =\frac{j\hbar^2}{2}\,Q_{\mathbf n,ab},
$$

而 Berry 曲率为

$$
F_j=-j\sin\theta\,\mathrm d\theta\wedge\mathrm d\phi,
 \qquad c_1(L_j)=-2j.
$$

绕 $\mathbf n$ 旋转 $\alpha$ 的最高权态相位为 $e^{-\mathrm ij\alpha}$。

**证明。**

对称乘积态中每个因子的平均为 $\mathbf n$， 所以平均自旋为 $q\hbar\mathbf n/2$。 不同因子的中心化关联因乘积性为零，同一因子贡献 $\hbar^2Q_{ab}/4$，求和得到 $q\hbar^2Q_{ab}/4$。 对 $\psi^{\otimes q}$ 求导共有 $q$ 项，故联络为 $qA$、曲率为 $qF$。 每个因子在绕自身轴转动时乘 $e^{-\mathrm i\alpha/2}$， 相乘即为 $e^{-\mathrm ij\alpha}$。

$\square$

该族共有相同的 $\mathbf n$、$`*\mathbf n`$ 和 $J_{\mathbf n}$， 却有不同的自旋大小、涨落尺度和相位曲率系数。 因此 Hodge 对偶单独不选择 $j=1/2$。 任意自旋的几何相位系数与立体角关系具有明确原始文献背景 [\[2\]](#ref-berry), [\[7\]](#ref-layton)。

#### 推论 11.3：在额外条件下选出二分之一自旋

若另要求完整纯态空间恰为 $\mathbb C^d$ 的全部射线且同胚于 $S^2$， 以及物理旋转采用非平凡不可约 $SU(2)$ 自旋表示 （等价地，允许相应 $SO(3)$ 投影表示），则 $d=2$、$j=1/2$。

**证明。**

$\mathbb CP^{d-1}$ 的实维数为 $2(d-1)$，与球面维数 $2$ 相等给出 $d=2$。 不可约自旋表示维数为 $2j+1$，故 $j=1/2$。

$\square$

这里“二能级端口”与“物理自旋二分之一粒子”仍需区分： 一个受限子空间、路径比特或其他编码也可具有同样 Pauli 代数， 其物理旋转与耦合含义必须另外给定。

<a id="section-12"></a>

## 12　粒子性、物理波包、磁矩与零点能的边界

### 12.1　方向确定不等于位置定域

#### 反例 12.1：同一轴面对应任意空间宽度

在 $L^2(\mathbb R)\otimes\mathbb C^2$ 中取

$$
\phi_s(x)=(2\pi s^2)^{-1/4}e^{-x^2/(4s^2)},\qquad
 \Psi_s=\phi_s\otimes|e_3\rangle,\qquad s>0.
$$

所有 $\Psi_s$ 的自旋方向都是 $e_3$，对偶面与横向核相同， 但位置方差为 $s^2$。因此该方向不能决定粒子的位置定域程度， 也不能决定一个空间波包。

**证明。**

$|\phi_s|^2$ 是均值零、方差 $s^2$ 的归一 Gaussian 密度。 对空间自由度偏迹后始终得到 $|e_3\rangle\langle e_3|$。

$\square$

#### 命题 12.2：相干性相对于读出基

对二能级态 $\rho(\mathbf r)$ 与路径轴 $\mathbf m$，定义

$$
\mathcal P_{\mathbf m}=|\mathbf r\cdot\mathbf m|,
 \qquad
 \mathcal V_{\mathbf m}
 =2|\langle+\mathbf m|\rho|-\mathbf m\rangle|.
$$

则

$$
\mathcal V_{\mathbf m}
 =\sqrt{\left\|\mathbf r\right\|^2-(\mathbf r\cdot\mathbf m)^2},
 \qquad
 \mathcal P_{\mathbf m}^2+\mathcal V_{\mathbf m}^2=\left\|\mathbf r\right\|^2.
$$

**证明。**

把 $\mathbf m$ 旋转到第三轴，非对角元为 $(r_1-\mathrm ir_2)/2$。

$\square$

对于纯态 $\mathbf n$，以自身轴读出时 $\mathcal V_{\mathbf n}=0$， 以任意横向轴作为路径基时 $\mathcal V_{\mathbf m}=1$。 因此同一态的 $`*\mathbf n`$ 始终有单位范数，并不意味着每个干涉实验都具有同样可见度。 “轴向确定”和“横向相干”是相对于明确读口的同一量子态性质。

### 12.2　磁矩和真实电磁场需要耦合条件

#### 命题 12.3：磁矩耦合的欠确定性

固定同一自旋表示和同一轴面对偶，对任意实数 $\kappa$，

$$
\boldsymbol\mu=\kappa\mathbf S,\qquad
 H_{\rm mag}=-\kappa\mathbf S\cdot\mathbf B_{\rm phys}
$$

都满足相同的旋转协变性。特别地 $\kappa=0$ 也不破坏 Hodge 几何。 故这些几何条件不确定磁矩系数。

**证明。**

自旋和物理磁场按相应轴向量变换，点积保持； 常数 $\kappa$ 不出现在对称性约束中。

$\square$

电子磁矩涉及电荷、质量、$g$ 因子及相应相互作用。 实际精密实验和量子电动力学比较明确使用这些物理数据[\[8\]](#ref-fan)。 参数空间中 Berry 曲率的“磁单极子”类比，不能直接替代电子产生的时空电磁场。

### 12.3　零点涨落与零点能的区别

#### 定理 12.4：有限矩阵不能实现精确正则对易关系

在非零有限维空间中，不存在矩阵 $x,p$ 满足 $[x,p]=\mathrm i\hbar I$（$\hbar\ne0$）。

**证明。**

有限矩阵交换子的迹为零，而右侧的迹为 $\mathrm i\hbar d\ne0$。

$\square$

谐振子的零点能使用另一个模型： 取 $\omega>0$，在具有适当共同定义域的无限维空间中， $[a,a^\dagger]=I$ 与 $H_{\rm osc}=\hbar\omega(a^\dagger a+1/2)$、 $a|0\rangle=0$ 给出基态能量 $\hbar\omega/2$。 这些是 Hamiltonian、对易关系和真空条件共同的结论[\[9\]](#ref-tong)。 它们并不由一个有限二能级端口的正交平面推出。

在本稿的有限定态模型中， $H=0$ 仍允许 $\operatorname{Var}(X_{\mathbf u})=1$ 的横向涨落， 却没有关联振荡；取 $\Delta>0$ 时， $H=\Delta P_{-\mathbf n}$ 具有相同横向涨落且基态能量为零， 却有频率 $\Delta/\hbar$ 的关联振荡。 这两个显式模型同时区分了方差、能隙频率与能量零点。

<a id="section-13"></a>

## 13　全局内生闭合与静态历史表示

#### 定理 13.1：内部参考协议的有限整体闭合

在 A5–A7 下，本文任意有限次制备、相干比较、反馈和记录协议 都可以放入一个有限整体中表示为幺正历史及内部读出； 它不要求整体外部的参考系统。

**证明。**

对每个完全正仪器取 Kraus 算子 $K_{a\mu}$。 映射 $\psi\mapsto\sum_{a,\mu}K_{a\mu}\psi\otimes|a,\mu\rangle$ 由迹保持条件成为等距映射，可在扩大后的有限空间中扩展为幺正。 保留所有必要环境和正交结果记录， 把有限反馈写成记录控制的后续操作。 初始混合态可由有限辅助系统纯化。 把所有系统和控制寄存器列入整体即可。 其后仍需保持原访问合同；被原协议丢弃的环境不能无条件重新开放。

$\square$

#### 定理 13.2：带内部参考的唯一静态历史态

将上述有限整体协议的幺正步骤记为 $U_1,\ldots,U_N$， $W_0=I$、$W_k=U_k\cdots U_1$。 给定单位输入 $\psi_0$，定义

$$
|\Omega_N\rangle
 =\frac1{\sqrt{N+1}}\sum_{k=0}^N|k\rangle_C\otimes W_k\psi_0.
$$

令

$$
D(x_0,\ldots,x_N)=(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
$$

$$
K=D^\dagger D+|0\rangle\langle 0|\otimes(I-|\psi_0\rangle\langle \psi_0|).
$$

则 $K\succeq0$ 且 $\ker K=\operatorname{span}\{|\Omega_N\rangle\}$。 时钟条件 $k$ 的系统态为 $W_k\psi_0$。若 $N=0$，取 $D=0$。

**证明。**

$D^\dagger D$ 的核恰满足 $x_k=W_kx_0$。 输入项要求 $x_0$ 平行 $\psi_0$。 两个正算子的共同核因此为一维，由所示历史态张成。 时钟正交性和幺正性给出归一化及条件态。

$\square$

这复用并扩展 OTF-001 的静态历史构造： 参考、相位控制、读出和观察者记录全部包括在同一 $\Omega_N$ 中。 “内生”意味着模型内没有遗漏的物理控制者； 它并不意味着传播算子、边界条件和协议菜单已由一个方向唯一推导出来。 连续时间相关函数可在任意选定有限时刻被此构造精确表示； 有限个可区分时钟标签不等于无限精度连续时钟。

<a id="section-14"></a>

## 14　与 AURIC 固定版本的衔接与归属

本轮读取的仓库默认分支为 `dev`，固定提交为 `591f599ea8777d6d533451d8736d99f9a3425a85`， 时间为 2026 年 11 月 8 日 02:20:27（新加坡）。 它不是 `main` 分支的当前头。 目录 API 的 theory 列表达到 1000 项上限，因此这里只报告已经打开的相关文件和小节， 不声称穷尽全仓。固定来源列于参考文献。

| 已有来源 | 已核对的内容 | OTF-002 的接口 |
|:---|:---|:---|
| V48，第 4 节[\[10\]](#ref-v48) | 定向度量平面的 $J$；$J_{\mathbf n}\mathbf v=\mathbf n\times\mathbf v$； 三维全空间上不能有 $J^2=-I$ | 复用横向复结构，再连接 Hodge、最小核和跃迁算子 |
| C137，第 5 节至 5.3，命题 5.5[\[11\]](#ref-c137) | Hopf 圆纤维、无全局相位截面；与 $SU(2)\to SO(3)$ 两点核区分 | 复用相位纤维边界；显式证明 $`TS^2\simeq(L^*)^{\otimes2}`$ |
| AURIC $\Omega$，假设 1.3、第 7 节、命题 82.5[\[12\]](#ref-omega) | 量子表示为明确附加结构；内部记录；跨块相干可使块相位成为相对相位 | 用实际受控协议读取 $G$，不把新增参考菜单免费并入旧合同 |
| 记录相干互补模块[\[13\]](#ref-record) | 记录重叠的 $V$、按 $\sqrt{1-V^2}$ 定义的 $D$ 及恒等式 | 仅复用重叠和端点代数；不把最优 Helstrom 判别证明归给该声明 |

AURIC $\Omega$ 文件在本轮固定提交下与 OTF-001 所读版本逐字相同， 不能把本次重新发现的相位菜单段落说成仓库刚刚新增。 RecordCoherence 的数学说明与对应 74 行 Lean 源码已完整阅读， 但本轮没有重新运行 Lean 构建。本文新增普通证明与仓库既有形式化结果分别归属。

<a id="section-15"></a>

## 15　推导范围、反例检查与研究结论

### 15.1　从候选约束到标准量子结构

| 目标结构 | 本文依据 | 逻辑状态 |
|:---|:---|:---|
| 轴面对偶与横向 $J$ | A1、Hodge 与叉积 | 几何定理；无新增态参数 |
| Born 二元概率 | A2 的完整球、仿射性、锐端点 | 唯一性定理 |
| Pauli 乘积与复二维表示 | A3 明确指定 Clifford/Pauli 条件 | 表示输入；不能由 Hodge 独自代替 |
| 单态横向核 $Q$ | A3 的 Pauli 乘积；或几何核的最小复秩与定向选择 | 两条明确相容的刻画 |
| Schrödinger 形式 | A4 的可微幺正演化 | $H=\mathrm i\hbar\dot U U^\dagger$ 的条件结论 |
| 定态关联频率 | 给定本征能隙 $\Delta$ | $G=e^{-\mathrm i\Delta t/\hbar}Q$；频率不是几何常数 |
| 纠缠、仪器、概率归一化 | A5 的量子复合与完全正性 | 明确复合输入及操作闭合 |
| 相对相位可观测 | A6 的实际相干菜单 | 受控干涉协议定理 |
| 观察者、记录与时钟内生 | A7、有限幺正扩张和历史约束 | 整体内表示定理 |

### 15.2　关键边界与反向检验

| 省略的条件或混同 | 具体后果 |
|:---|:---|
| 省略有向性 | $\mathbf n$ 与 $-\mathbf n$ 具有同一无向面，却对应正交纯态。 |
| 由轴自动选择横向指针 | 绕轴半周旋转给出直接协变性矛盾。 |
| 只要求实向量上的核正性 | 任意 $\lambda$ 的反对称虚部均不影响 $C(\mathbf u,\mathbf u)$，无法得到 $\vert \lambda\vert \leq1$。 |
| 省略最小复秩 | $\lambda=0$ 的实横向核也满足归一实部与正性。 |
| 把单态方向当空间位置 | 同一自旋方向允许任意宽度的 Gaussian 空间波包。 |
| 把平面存在当振荡 | $H=0$ 保留全部轴面结构，却没有关联相位变化。 |
| 把定态全局相位当物理转动 | $H=cI$ 对所有系统算子作用恒等，规范重建标架却随 $c$ 转动。 |
| 把同一方向球当特定自旋值 | 所有 $j=1/2,1,3/2,\ldots$ 的相干态族共享同一方向球。 |
| 只给末态或 CPTP 通道 | 丢失两条相干实现之间的相对相位。 |
| 把有限采样当连续频率识别 | 等间隔 $\tau$ 只能识别能隙模 $2\pi\hbar/\tau$。 |

### 15.3　本轮的正式结论与白话表述

在所声明的二能级条件下，一个纯态方向同时确定： 轴向确定读出、有向横向复结构、最小量子涨落核，以及相干跃迁的复线空间。 指定内部动力学后，该核沿两次读出之间的关系获得能隙相位； 指定内部相干访问合同后，相位进入可检验的干涉概率。 这些结论构成

$$
\mathbf n
 \longleftrightarrow
 (B_{\mathbf n},E_{\mathbf n},J_{\mathbf n},Q_{\mathbf n})
 \longleftrightarrow
 \operatorname{Hom}_{\mathbb C}(L_{\mathbf n},L_{-\mathbf n})
$$

与

$$
(Q_{\mathbf n},H,\text{内部协议})
 \longrightarrow
 G_{\mathbf u\mathbf v}(t)
 \longrightarrow
 p_+(\phi)
$$

两种不同类型的关系：前一行是同一单态信息的等价表达， 后一行在增加明确动力学及协议条件后产生可观测预测。

**白话。** 一个纯量子态可以像一根确定的轴，但它并不只有“沿轴确定”这一面。 它同时规定了周围所有横向读出的不确定性、它们的配合方向， 以及一种把两条正交振幅连接起来的复数结构。 这就是那张“随轴而有的面”的严格含义。 这张面没有自己偷偷装上一根永远转动的指针； 当整体内部给出相互作用和能隙时，两次横向读出之间才会积累相位。 观察者用同一整体里的另一条相干路径比较，就能把这个相位读成条纹。 所以单态能够包含波的结构与响应潜能，实际振荡和读出则由内部关系共同实现。

本候选在允许协议上仍是标准有限维量子理论的几何组织。 下一步若要产生不同的物理预测，必须明确改变某一动力学、复合或读出条件， 并同时证明正性、归一化和内部协议相容性。本文已经给出可以承接这些扩展的定义域、 核心恒等式与可反驳边界。

<a id="section-A"></a>

## A　符号与规范约定

| 符号 | 精确定义 |
|:---|:---|
| $\mathcal I=e_1e_2e_3$ | Euclidean 三维体积元，$\mathcal I^2=-1$。 |
| $B_{\mathbf n}=\mathbf n\mathcal I$ | Hodge 对偶单位双向量，保留定向。 |
| $E_{\mathbf n}=\mathbf n^\perp$ | 实二维横向空间，不是另一个 Hilbert 态空间。 |
| $J_{\mathbf n}\mathbf v=\mathbf n\times\mathbf v$ | 在 $E_{\mathbf n}$ 上的复结构；全三维中有轴向核。 |
| $Q_{\mathbf n}$ | 复三维上的秩一 Hermitian 协方差矩阵；其横向实部秩为二。 |
| $L_{\mathbf n}=\operatorname{ran}P_{\mathbf n}$ | Hopf 态复线，$c_1=-1$。 |
| $\operatorname{Hom}(L_{\mathbf n},L_{-\mathbf n})$ | 相干跃迁复线，等同于切线复线，$c_1=+2$。 |
| $A=\mathrm i\psi^\dagger\mathrm d\psi$ | 相位变换下 $A\mapsto A-\mathrm d\chi$；曲率 $F=\mathrm dA$。 |
| $\Delta=E_--E_+$ | 有向能隙；可为正、负或零，基态例另取 $\Delta>0$。 |
| $G_{\mathbf u\mathbf v}$ | 有序的复两时关联，不直接等于两个实记录的乘积均值。 |
| $q$ | Fubini–Study 弧长；在自旋比较族中另以文字声明 $q=2j$ 的整数记号。 |

<a id="section-B"></a>

## B　编译与核验说明

> Markdown 转换说明：本文件为纯 Markdown。下述 XeLaTeX 编译要求保留自原稿，仅说明原始排版源码的构建方式；两幅原图已转为文内文字和公式。

本文源文件自包含图形和参考文献。 使用安装了 `ctex`、TikZ、TeX Gyre 与 Noto CJK 字体的 XeLaTeX 连续编译两次。 普通证明已检查矩阵符号、相位约定、纯混合边界、零能隙和零支路； 源码核对范围见第 14 节。 图示与公式只呈现本文给定模型，不是新的实验数据。

## 参考来源

<a id="ref-hestenes"></a>

\[1\] D. Hestenes. Real Spinor Fields.  *Journal of Mathematical Physics*  **8**, 798–808 (1967). <https://doi.org/10.1063/1.1705279>. 作者原文：<https://davidhestenes.net/geocalc/pdf/RealSpinorFields.pdf>.

<a id="ref-berry"></a>

\[2\] M. V. Berry. Quantal phase factors accompanying adiabatic changes.  *Proceedings of the Royal Society A*  **392**, 45–57 (1984). <https://doi.org/10.1098/rspa.1984.0023>.

<a id="ref-simon"></a>

\[3\] B. Simon. Holonomy, the quantum adiabatic theorem, and Berry’s phase.   *Physical Review Letters*   **51**, 2167–2170 (1983). <https://doi.org/10.1103/PhysRevLett.51.2167>.

<a id="ref-brody"></a>

\[4\] D. C. Brody and L. P. Hughston. Geometric quantum mechanics.  *Journal of Geometry and Physics*  **38**, 19–53 (2001). <https://arxiv.org/abs/quant-ph/9906086v2>.

<a id="ref-yu"></a>

\[5\] M. Yu et al. Experimental measurement of the quantum geometric tensor using coupled qubits in diamond.  *National Science Review*  **7**, 254–260 (2020). <https://doi.org/10.1093/nsr/nwz193>. <https://arxiv.org/abs/1811.12840>.

<a id="ref-ramsey"></a>

\[6\] N. F. Ramsey and H. B. Silsbee. Phase shifts in the molecular beam method of separated oscillating fields.  *Physical Review*  **84**, 506 (1951). <https://doi.org/10.1103/PhysRev.84.506>.

<a id="ref-layton"></a>

\[7\] E. Layton, Y. Huang, and S.-I. Chu. Cyclic quantum evolution and Aharonov–Anandan geometric phases in SU(2) spin-coherent states.  *Physical Review A*  **41**, 42 (1990). <https://doi.org/10.1103/PhysRevA.41.42>.

<a id="ref-fan"></a>

\[8\] X. Fan et al. Measurement of the electron magnetic moment.   *Physical Review Letters*   **130**, 071801 (2023). <https://doi.org/10.1103/PhysRevLett.130.071801>. 用于磁矩的物理耦合与测量背景，不声称是截至本稿日期的最新数值。

<a id="ref-tong"></a>

\[9\] D. Tong.  *Quantum Field Theory* , Chapter 2, §2.1.1. 作者讲义：<https://www.davidtong.org/pdfs/teaching/quantum-field-theory/qft2.pdf>. 用于振子 Hamiltonian、正则对易关系与零点能的条件推导。

<a id="ref-v48"></a>

\[10\] The Omega Institute. AURIC: 各向同性、手性与量子起源的条件重构，V48。 固定提交 `591f599ea8777d6d533451d8736d99f9a3425a85`，第 4 节及相关表示边界。 [固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/591f599ea8777d6d533451d8736d99f9a3425a85/docs/develop/theory/AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md).

<a id="ref-c137"></a>

\[11\] The Omega Institute. C137: 零读极性、射影圆与相位纤维。 同一固定提交，第 5 节至 5.3，命题 5.5。 [固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/591f599ea8777d6d533451d8736d99f9a3425a85/docs/develop/theory/AURIC_C137_ZERO_READOUT_POLARITY_PROJECTIVE_CIRCLE_AND_PHASE_FIBRES.md).

<a id="ref-omega"></a>

\[12\] The Omega Institute. AURIC $\Omega$ 静态相融纤维理论。 同一固定提交，假设 1.3、第 7 节、命题 82.5。 [固定提交中的原文](https://github.com/the-omega-institute/trureturing/blob/591f599ea8777d6d533451d8736d99f9a3425a85/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md).

<a id="ref-record"></a>

\[13\] The Omega Institute. Record coherence complementarity. 同一固定提交，数学说明与对应 Lean 声明。 [固定提交中的数学说明](https://github.com/the-omega-institute/trureturing/blob/591f599ea8777d6d533451d8736d99f9a3425a85/Blueprint/D5/S3/Quantum/PureState/RecordCoherenceComplementarity.md). 对应 `D5/S3/Quantum/PureState/RecordCoherenceComplementarity.lean`； 本轮读取源码，未重新运行构建。
