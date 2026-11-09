# AURIC FIB 关系丛与预测闭包理论

有限量子仪器、相位拓扑、受约束量子门与内生观察者的统一数学框架。

**模型假设。** 有限维量子系统、有限记录与输出解析仪器、光滑恒秩参数域；
五模式 AURIC FIB 实例及合法长链推广。本文是所供作者手稿的数学表述，
不据此主张历史优先权或整卷证明助手认证。定理的“证明”指所附普通数学证明；
所引两项 Lean 源结果只覆盖各自给定的单一 Heisenberg 迭代。
固定文本来源为 [trureturing](https://github.com/the-omega-institute/trureturing) 的提交
`7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c`。

## 摘要

本稿发展一套有限维的关系丛与预测闭包理论。基本原则是把来源对象、
概率兼容类、相干态、可调用操作、输出记录与资源成本分别定义，
再证明它们之间何时存在保持所需结构的映射。
五模式的可见占位金字塔具有一维经典隐关系；其射影完成经有效
$T^3$ 作用在正则矩层上约化后产生二维关系球面。本文给出商度量、正曲率、
端点锥角、主环面丛过渡函数、第一 Chern 数、预量子整性条件
与对称整数荷扇区维数的明确公式。

在读出恒秩的参数域内，隐藏差方向形成实向量丛。可逆门输运能下降到读出，
当且仅当它保持这些隐藏方向；全路径下降等价于核丛平行，
端点独立性进一步等价于商 holonomy 平凡。
输出解析的全未来效果闭包则在全部密度态上给出任意有限仪器模型的最小仿射预测摘要，
至多在 $d^2-\dim W_0$ 轮线性闭包后稳定。菜单增长由一个短正合列刻画。
有限观察者可以作为含显式记忆与环境的等距扩张中的内部子系统实现。

在 AURIC FIB 代码上，明确初始化代码后，理想的独立端点连续实参数脉冲与一个固定受控相位门
精确生成全部双逻辑量子位酉通道，且每个门前缀保持代码。
另一方面，读出均值上的自然梯度保留隐关系，而一个要求独立制备两份相同纯态的两拷贝测量
关系损失，在固定正概率关系域上给出局部指数稳定的几何梯度流。最后，以 Möbius 反演将
单一关系对推广为合法链上的高阶矩--相位层级。
全部结论均在其明示的有限维、恒秩与操作菜单假设下成立；
物理时空、最优全局控制及计算复杂性结论需要额外数据。

<a id="sec-foundations"></a>

## 1. 理论的数据、公理与对象类型

本稿所称 AURIC FIB 关系丛理论，是以下一类有限维结构及其可证明命题的集合。
“完整”取为：对象、允许操作、等价关系、几何构造、预测规则和增长条件
形成可核验的闭合体系，而不是从一个五点集合推出所有物理规律。
后文涉及的概率、量子概率、光滑性和控制许可均有显式来源。
研究的固定文本是 trureturing 的同一提交快照；来源对照列于文末。

<a id="def-contract"></a>

**定义 1.1（分层模型数据）。**
一个有限关系--预测模型由以下数据组成。

1. **C1.** **合法来源。** 一个非空有限集合 $\Sigma$，以及给定实函数
   $f_1,\ldots,f_m:\Sigma\to\mathbb R$。它们定义经典可见统计。
   若来源本来是有序语法对象，必须另外给出到 $\Sigma$ 的映射，不能默认此映射单射。

2. **C2.** **相干完成。** 另供标号 Hilbert 空间
   $\mathcal H=\mathbb C^\Sigma$，允许态为明定子集
   $\mathcal S\subseteq\mathcal D(\mathcal H)$。纯态完成和全部密度态完成
   是不同模型；未特别说明时，涉及仿射预测最小性的定理采用全部密度态。

3. **C3.** **操作与输出。** 给定允许的完全正仪器分支
   $\Phi_{a,o}$、末端效果与实际记录规则。控制动作只能按既得记录选择；
   其他相干控制必须作为更大 Hilbert 空间上的门明确供给。

4. **C4.** **可调用菜单。** 有限仪器菜单与理想连续脉冲菜单分别声明。
   一个固定 Hamiltonian 的存在，不等价于其每一项可以独立定时调用。

5. **C5.** **几何数据。** 若模型依参数变化，则给定光滑基底、
   相关丛、度量与联络。只有恒秩区域上才使用普通向量丛结论；
   奇异点单独处理。

6. **C6.** **资源数据。** 给出记录存储、独立制备、测量、
   门调用、时长或路径长度的成本。不同成本不自动可互换。

这些条件是模型合同。一个证明只可调用其陈述列出的合同部分。
例如，相位 holonomy 的数学存在不提供实验室 Hamiltonian；
数学上的线性商不自动给出量子压缩通道；
两份独立同分布制备不等于从一份未知态复制出第二份。

| 对象 | 典型形式 | 本文证明的问题 |
| --- | --- | --- |
| 来源与合法性 | $\Sigma$、有序树、合法位串 | 哪些映射保存信息与组合结构 |
| 概率兼容类 | $\{p:Ap=b,\ p\ge0\}$ | 哪些关系没有被当前均值确定 |
| 相干关系空间 | 固定矩层的相位约化 | 关系的辛对、度量、拓扑与整性 |
| 读出差方向 | $\ker L\subset\operatorname{Herm}_0$ | 量子门能否下降到摘要 |
| 未来效果空间 | $W_\infty$ | 所有允许未来究竟能分辨什么 |
| 内生观察者 | 记忆、分支、环境的联合等距映射 | 反馈和更新如何作为系统内部过程实现 |

<a id="sec-general-relations"></a>

## 2. 一般有限关系格与概率--相位对偶

本节给出五模式计算的一般形式。它同时说明哪些性质依赖整数权格，
哪些只是实线性代数，哪些还需要正概率。

<a id="def-relation-lattice"></a>

**定义 2.1（仿射关系格与矩纤维）。**
令 $\Sigma=\{0,\ldots,N-1\}$，给定 $v_s\in\mathbb Z^m$，并设

$$
A=\begin{pmatrix}1&\cdots&1\\v_0&\cdots&v_{N-1}\end{pmatrix}
 :\mathbb Z^N\longrightarrow\mathbb Z^{m+1}
$$

为满射。等价地，整数差 $v_s-v_0$ 生成 $\mathbb Z^m$。
令 $k=N-m-1$，取整数关系格
$\Lambda=\ker A$ 的一个整数基，排成 $N\times k$ 矩阵 $D$。
于是

$$
AD=0,\qquad \operatorname{rank}D=k,\qquad {\bf1}^{\mathsf T}D=0.
$$

对给定 $b\in\mathbb R^m$，定义正矩纤维

$$
\mathcal P_b^\circ
 =\{p\in\mathbb R_{>0}^N:Ap=(1,b)^{\mathsf T}\}.
$$

若它非空，选择 $p^0\in\mathcal P_b^\circ$，以唯一坐标 $q\in\mathbb R^k$
写 $p=p^0+Dq$。定义域是开凸多面体
$\mathcal Q_b=\{q:p^0+Dq>0\}$。
当 $k=0$ 时，下述关系空间是一个点，矩阵公式按空矩阵理解。

<a id="thm-general-symplectic"></a>

**定理 2.2（关系格的辛对偶与完整正域商）。**
采用 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$ 及
$\omega_{\rm FS}=\sum_s d\theta_s\wedge dp_s$ 的规范。
在全正振幅域固定矩均值 $b$，再商去共同相位与
$\theta_s\mapsto\theta_s+v_s\cdot t$，所得空间有全局坐标

$$
(q,\chi)\in\mathcal Q_b\times T^k,\qquad
 \chi=D^{\mathsf T}\theta\pmod{2\pi}.
$$

约化辛形式为

$$
\omega_{\rm rel}=\sum_{j=1}^k d\chi_j\wedge dq_j.
$$

因此每个独立仿射概率关系恰有一个共轭关系角；
正域的实维数为 $2k$。

**证明。**

由于 $A:\mathbb Z^N\to\mathbb Z^{m+1}$ 满射，选择每个标准基向量的
整数原像并排成矩阵 $S$，则 $AS=I$。每个 $u\in\mathbb Z^N$ 唯一分解为

$$
u=Dz+SAu,\qquad z\in\mathbb Z^k.
$$

确实，$u-SAu\in\ker A$，由 $D$ 是整数基得到存在和唯一性。
所以矩阵 $[D\ S]$ 为整数可逆矩阵。其对偶给出整数格的正合列

$$
0\longrightarrow\mathbb Z^{m+1}
 \overset{A^{\mathsf T}}{\longrightarrow}\mathbb Z^N
 \overset{D^{\mathsf T}}{\longrightarrow}\mathbb Z^k
 \longrightarrow0.
$$

这里最后一个映射满射也可直接由 $[D\ S]^{\mathsf T}$ 的整数逆看出。
在环面上，$D^{\mathsf T}:T^N\to T^k$ 的核正好是
$A^{\mathsf T}T^{m+1}$，没有额外有限分支。
因此 $\chi$ 完整标记相位商，而不只给局部坐标。

概率方程的全部实解为 $p^0+\ker_{\mathbb R}A=p^0+Dq$，
且非负约束在正域恰给 $\mathcal Q_b$。相位商不作用于概率，
所以商空间是所列乘积。固定矩层上 $dp=D\,dq$，于是

$$
\sum_s d\theta_s\wedge dp_s
 =\sum_j d(D^{\mathsf T}\theta)_j\wedge dq_j.
$$

右式只依商坐标并且非退化，因此给出所述约化辛形式。

证毕。

若只假定实仿射满秩，局部辛公式仍成立。
若整数权差不生成全部 $\mathbb Z^m$，名义占位环面具有有限无效核；
要把作用表述为自由主环面作用，应先采用有效环面。
使用完整整数关系格的基时，相位商本身仍可由上述关系角完整标记；
不能用非本原关系生成元代替完整关系格的基。
本定理也只覆盖全正部分；零振幅处哪些角塌缩需要另行分析。

<a id="thm-general-metric"></a>

**定理 2.3（一般关系空间的商度量与最短相位提升）。**
在定理 [2.2](#thm-general-symplectic)的条件下，令

$$
P_p=\operatorname{diag}(p_s),\qquad
 G(p)=D^{\mathsf T}P_p^{-1}D .
$$

对 $k>0$，$G$ 正定。若 FS 度量取

$$
g_{\rm FS}=\frac12\sum_s\frac{dp_s^2}{p_s}
 +2\left(\sum_s p_s\,d\theta_s^2-
       \left(\sum_s p_s\,d\theta_s\right)^2\right),
$$

则关系商的度量为

$$
g_{\rm rel}=\frac12\,dq^{\mathsf T}G\,dq
             +2\,d\chi^{\mathsf T}G^{-1}d\chi.
$$

指定角速度 $u=\dot\chi$，并固定共同相位规范
$\sum_s p_s\dot\theta_s=0$ 后，唯一最小速度提升为

$$
\dot\theta_{\min}=P_p^{-1}DG^{-1}u.
$$

若换整数关系基 $D'=DM$，其中 $M\in GL(k,\mathbb Z)$，则
$q'=M^{-1}q$、$\chi'=M^{\mathsf T}\chi$，
辛形式和度量都保持不变。

**证明。**

对非零 $u$，
$u^{\mathsf T}Gu=(Du)^{\mathsf T}P_p^{-1}(Du)>0$，
因为 $D$ 满列秩且所有 $p_s>0$。
径向部分由 $dp=D\,dq$ 立即给出第一项。

固定角速度约束 $D^{\mathsf T}v=u$。
任意相位速度可以减去共同角速度而不改变此约束或相位方差，
所以先规范化为 $p^{\mathsf T}v=0$。
候选 $`v_*=P_p^{-1}DG^{-1}u`$ 满足

$$
D^{\mathsf T}v_*=u,\qquad
 p^{\mathsf T}v_*={\bf1}^{\mathsf T}DG^{-1}u=0.
$$

对任意另一个规范化可行速度 $`v_*+z`$，有 $D^{\mathsf T}z=0$，故

$$
z^{\mathsf T}P_pv_*
 =z^{\mathsf T}DG^{-1}u=0.
$$

于是其相位方差为

$$
(v_*+z)^{\mathsf T}P_p(v_*+z)
 =u^{\mathsf T}G^{-1}u+z^{\mathsf T}P_pz.
$$

第二项非负，且仅 $z=0$ 时为零。这证明唯一最小性和相位商度量；
FS 原度量没有径向--相位交叉项，故商中也没有。
最后 $G'=M^{\mathsf T}GM$，代入坐标变换直接消去 $M$，
给出两形式与度量的基不变性。

证毕。

<a id="thm-hidden-21"></a>

**定理 2.4（五模式中的经典隐维与完整量子隐维）。**
对五模式 $\Sigma=(0,1,2,3,13)$，令
$N_x,N_y,N_z$ 为相应占位函数的对角算符。当前可见效果空间为

$$
W_{\rm vis}=\operatorname{span}_{\mathbb R}\{I,N_x,N_y,N_z\}.
$$

在全部 $5\times5$ Hermitian 矩阵中，

$$
W_{\rm vis}^{\perp}
 =\mathbb R\,\operatorname{diag}(1,-1,0,-1,1)
 \ \mathbin{\oplus^\perp}\ 
 \{X=X^\dagger:\operatorname{diag}X=0\}.
$$

其真实维数为 $1+20=21$。
限制到对角概率模型，隐藏差方向才只有一维。
在全正纯态域，每个非空的固定三个均值纤维为五维；
再商去占位 $T^3$ 后才得到二维关系空间。

**证明。**

四个可见对角算符线性无关：依次在空模式、两个端模式和中模式评价，
即能确定四个系数。每个 Hermitian 矩阵唯一正交分解成对角部分和零对角部分。
后者与所有可见算符正交，且每个无序模式对有独立的实部和虚部，
所以其维数为 $2\binom52=20$。
在五维对角空间中，四个独立读出方程的核是一维；
所列向量与 $1,x,y,z$ 均正交，故正是该核。

纯态射影空间 $\mathbb{CP}^4$ 的实维数为八。
在全正域中概率均值映射微分秩为三，
所以固定均值局部维数为 $8-3=5$。
全正振幅上的有效占位相位作用自由，商后维数为 $5-3=2$。

证毕。

必须按任务解释这个相位商。例如

$$
\psi=\frac{(1,1,1,1,1)}{\sqrt5},\qquad
 \psi'=\frac{(1,-1,1,1,-1)}{\sqrt5}
$$

由 $t_X=\pi$ 的占位相位变换相连，具有相同的 $p,X,Y,Z,\chi$。
但在允许保留相位参考并测量
$O=|0\rangle\langle1|+|1\rangle\langle0|$ 的任务中，
期望分别为 $2/5$ 和 $-2/5$。
所以占位相位可以是指定不变量问题中的规范方向，
却不能在任意扩展操作菜单中都当作物理不可区分方向。
全未来是否真的不可区分，由后文的 $W_\infty$ 决定。

<a id="sec-geometry"></a>

## 3. 五模式的代数、概率纤维与射影完成

本章固定同一个五模式来源，先建立函数代数和概率投影，再在明确增加的复振幅模型上建立射影几何。五模式、概率反演、辛完成及水平度量的既有来源为仓库基础卷、辛完成卷和相位运输卷[1](#ref-repo-found)、[2](#ref-repo-sp)、[3](#ref-repo-hol)。下文给出自足的普通数学证明；这些证明不自动构成 Lean 认证，也不把经典向量丛和辛约化理论改称本项目的独创结果。主丛过渡函数与面积斜率的对应，是本稿在这些固定前提下明确推导的结论。

<a id="def-geom-five"></a>

**定义 3.1（五模式及其两种次序）。**
令

$$
\Sigma=(0,1,2,3,13)
=(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]).
$$

物理位串按低端、中位、高端排列，即 $(x,z,y)$；代数坐标始终按 $(x,y,z)$ 排列。五模式的评价为

$$
\begin{array}{c|c|c}
 s&\text{物理位串 }(x,z,y)&v_s=(x_s,y_s,z_s)\\ \hline
 0&000&(0,0,0)\\
 1&100&(1,0,0)\\
 2&010&(0,0,1)\\
 3&001&(0,1,0)\\
 13&101&(1,1,0)
\end{array}
$$

因此合法性是 $x,y,z\in\{0,1\}$ 及 $xz=yz=0$，没有 $xy=0$ 这一限制。模式 $0$ 是空占位事件；在后续 Hilbert 模型中 $|0\rangle$ 是范数为一的基向量，不是零向量。所有概率和振幅的分量均按 $\Sigma$ 的上述次序排列。

<a id="thm-geom-algebra"></a>

**定理 3.2（完整函数代数与唯一二阶关系系数）。**
评价映射给出实代数同构

$$
\frac{\mathbb R[x,y,z]}{(x^2-x,y^2-y,z^2-z,xz,yz)}
\simeq \mathbb R^\Sigma.
$$

每个 $f:\Sigma\to\mathbb R$ 有唯一展开

$$
f=c_0+c_xx+c_yy+c_zz+J_fxy,
$$

其中

$$
\begin{split}
c_0&=f_0,\qquad c_x=f_1-f_0,\qquad c_y=f_3-f_0,\\
c_z&=f_2-f_0,\qquad
J_f=f_{13}-f_1-f_3+f_0.
\end{split}
$$

五个单事件指示函数是

$$
e_0=1-x-y-z+xy,\quad e_1=x-xy,\quad e_2=z,
\quad e_3=y-xy,\quad e_{13}=xy.
$$

它们满足 $e_se_t=\delta_{st}e_s$ 和 $\sum_s e_s=1$。

**证明。**

幂等关系将每个变量的幂降为零或一；包含 $xz$ 或 $yz$ 的项消失。因此商代数由 $1,x,y,z,xy$ 张成。在模式 $0,1,3,2$ 上依次评价一个线性组合，分别确定其常数、$x$、$y$、$z$ 系数；在模式 $13$ 上再确定 $xy$ 系数。这证明五个余类线性无关，并给出所列系数公式。评价保持加法和乘法，且每个五点函数均有此展开，故为代数同构，其核恰为所列理想。将五个指示式逐点评价，得到标准坐标函数，因而有正交幂等和分解单位恒等式。

证毕。

<a id="thm-geom-fiber"></a>

**定理 3.3（概率金字塔、完整兼容纤维及宽度）。**
在概率单纯形

$$
\Delta^4=\{p\in\mathbb R^5:p_s\ge0,\ \sum_s p_s=1\}
$$

上定义占位投影

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2.
$$

其像为金字塔

$$
\mathcal P=\{(X,Y,Z):X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
$$

给定 $b=(X,Y,Z)\in\mathcal P$，令 $r=1-Z$、$\kappa=p_{13}$，则其全部兼容概率为

<a id="eq-geom-probability"></a>

$$
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),\tag{3.1}
$$

其中

<a id="eq-geom-width"></a>

$$
\kappa_-:=\max(0,X+Y-r)\le\kappa\le\kappa_+:=\min(X,Y),
\quad
w(b):=\kappa_+-\kappa_-=\min\{X,Y,r-X,r-Y\}.\tag{3.2}
$$

归一化概率超平面上的投影核为

$$
\mathbb R\nu,\qquad \nu=(1,-1,0,-1,1)^{\mathsf T}.
$$

对定理 [3.2](#thm-geom-algebra) 中的任意函数，

$$
\mathbb E_{p_\kappa}f
=c_0+c_xX+c_yY+c_zZ+J_f\kappa,
\qquad \frac{d}{d\kappa}\mathbb E_{p_\kappa}f=J_f.
$$

**证明。**

每个模式的占位满足金字塔的五条线性不等式，故每个概率混合也满足它们。反向固定满足这些不等式的 $b$，先令 $p_{13}=\kappa$，三个占位方程及总质量方程依次唯一给出式 [(3.1)](#eq-geom-probability)。五项非负恰好等价于式 [(3.2)](#eq-geom-width) 中的区间限制。因为 $0\le X,Y\le r$，有 $X+Y-r\le X,Y$，所以区间非空；这同时证明整个不等式域均为像。

若两个归一化实向量具有相同占位，令其末分量之差为 $t$，则占位方程强制第一端和第三端分量之差均为 $-t$、中模式之差为零，总质量方程再强制空模式之差为 $t$。故核恰为 $\mathbb R\nu$。

为验证宽度公式，可先设 $X\le Y$。若 $X+Y\le r$，则宽度为 $X$，且 $X\le Y,r-X,r-Y$；若 $X+Y\ge r$，则宽度为 $r-Y$，且 $r-Y\le X,Y,r-X$。交换 $X,Y$ 给另外两种情形。因此得到四项最小值。最后，对函数的唯一展开取期望，并使用 $\mathbb E(xy)=\kappa$，即得期望及导数公式。

证毕。

区间纤维本身不是向量空间。在线性表示上，核线 $\mathbb R\nu$ 是固定的；在正概率域上，它组成平凡的垂直切线丛。非负性将每条仿射核直线截为区间，并在 $w=0$ 的侧面上将区间压成一点。因此不能仅由“兼容纤维”这一名称推断存在固定秩向量丛。

<a id="def-geom-coherent"></a>

**定义 3.4（另供的相干完成及几何规范）。**
另供 Hilbert 空间 $\mathcal H=\mathbb C^5$ 及标号正交基 $(|s\rangle)_{s\in\Sigma}$。归一化振幅写为

$$
\psi_s=\sqrt{p_s}\,e^{-i\theta_s},\qquad
\sum_s|\psi_s|^2=1,
$$

并将相差共同相位的向量识别为射线 $[\psi]\in\mathbb{CP}^4$。其 tautological 复线丛定义为

$$
\mathcal L_{\mathrm{taut}}
=\{([\psi],v):v\in\mathbb C\psi\}
\longrightarrow\mathbb{CP}^4,
$$

Hermitian 结构由 $\mathcal H$ 限制得到。

Fubini--Study 辛形式 $\omega_{\rm FS}$ 的尺度取每条复射影直线的面积为 $2\pi$，Hamilton 约定取 $\iota_{X_H}\omega=dH$。在正概率相位图中写

$$
\lambda=\sum_s p_s\,d\theta_s,
\qquad
\omega_{\rm FS}=-d\lambda=\sum_s d\theta_s\wedge dp_s,
$$

且相容度量为

<a id="eq-geom-fullmetric"></a>

$$
g_{\rm FS}=\frac12\sum_s\frac{dp_s^2}{p_s}
+2\left(\sum_s p_s\,d\theta_s^2-
\Bigl(\sum_s p_s\,d\theta_s\Bigr)^2\right).\tag{3.3}
$$

这些复振幅、相位和尺度是模型的附加结构，不由经典概率本身推出。

<a id="thm-geom-moment"></a>

**定理 3.5（整周期相位坐标、矩映射及 tautological 曲率）。**
在全正概率图上定义

$$
\vartheta_X=\theta_1-\theta_0,\quad
\vartheta_Y=\theta_3-\theta_0,\quad
\vartheta_Z=\theta_2-\theta_0,\quad
\chi=\nu^{\mathsf T}\theta
=\theta_0-\theta_1-\theta_3+\theta_{13}.
$$

这些角及共同角 $\theta_0$ 给出整个周期环面的整数可逆坐标变换。因此模去共同相位后，

<a id="eq-geom-symplectic"></a>

$$
\omega_{\rm FS}
=d\vartheta_X\wedge dX+d\vartheta_Y\wedge dY
+d\vartheta_Z\wedge dZ+d\chi\wedge d\kappa.\tag{3.4}
$$

相位作用

$$
\theta_s\longmapsto\theta_s+x_st_X+y_st_Y+z_st_Z,
\qquad t\in T^3=(\mathbb R/2\pi\mathbb Z)^3,
$$

是有效 Hamilton 作用，其矩映射为 $\mu([\psi])=(X,Y,Z)$，像恰为 $\mathcal P$。

对 $\mathcal L_{\rm taut}$ 的正交投影连接 $\nabla=P\,d$，局部 unitary connection form 为 $A=-i\lambda$，曲率及第一 Chern 类为

$$
F=i\omega_{\rm FS},\qquad
c_1(\mathcal L_{\rm taut})
=\left[\frac{iF}{2\pi}\right]
=-\left[\frac{\omega_{\rm FS}}{2\pi}\right].
$$

特别地，$\lambda$ 不能成为整个 $\mathbb{CP}^4$ 上的全局一形式。

**证明。**

逆变换为

$$
\theta_1=\theta_0+\vartheta_X,\quad
\theta_3=\theta_0+\vartheta_Y,\quad
\theta_2=\theta_0+\vartheta_Z,\quad
\theta_{13}=\theta_0+\vartheta_X+\vartheta_Y+\chi.
$$

正逆变换的矩阵均为整数，所以在所有角模 $2\pi$ 的意义下互逆，不留下额外有限覆盖。将逆式及概率反演代入 $\lambda$，得到

$$
\lambda=d\theta_0+X\,d\vartheta_X+Y\,d\vartheta_Y
+Z\,d\vartheta_Z+\kappa\,d\chi.
$$

取 $-d$ 即得式 [(3.4)](#eq-geom-symplectic)。三个作用场分别为 $\partial_{\vartheta_X},\partial_{\vartheta_Y},\partial_{\vartheta_Z}$，与该式收缩得到 $dX,dY,dZ$，故 $\mu$ 为矩映射。若群元在全部射线上恒等，模式 $0$ 固定共同相位，而分别与模式 $1,3,2$ 的叠加强制 $t_X,t_Y,t_Z$ 全部为零模 $2\pi$，故作用有效。像的结论来自定理 [3.3](#thm-geom-fiber)，因为任意概率律都可以取非负平方根振幅实现。

对局部归一化代表，直接微分给

$$
\langle\psi,d\psi\rangle
=\frac12\sum_s dp_s-i\sum_s p_s\,d\theta_s=-i\lambda.
$$

这正是 $\nabla=P\,d$ 的局部连接形式。因此 $F=dA=-i\,d\lambda=i\omega_{\rm FS}$。采用 $c_1=iF/(2\pi)$ 的规范，即得 Chern 类公式。上述曲率和 Chern 规范使用标准 Hermitian 线丛构造[11](#ref-hatcher)、[12](#ref-cannas)，也可由两图过渡函数直接验证。

只保留任意两个模式得到一条复射影直线，其内部相对坐标满足 $\omega=d\theta\wedge dp$，面积为 $2\pi$。若有全局 $\lambda$ 且 $\omega=-d\lambda$，Stokes 定理会使该闭曲面上的积分为零，矛盾。局部势的不存在全局版本，不妨碍曲率二形式本身全局良定。

证毕。

<a id="sec-geometry-reduction"></a>

## 4. 固定均值的辛约化、度量与边界

<a id="thm-geom-reduction"></a>

**定理 4.1（正则关系球面与自由主环面丛）。**
固定

<a id="eq-geom-regular"></a>

$$
0<Z<1,\qquad 0<X,Y<r:=1-Z,\qquad
X\ne Y,\qquad X+Y\ne r.\tag{4.1}
$$

则 $b=(X,Y,Z)$ 是 $\mu$ 的正则值，$T^3$ 在 $P_b:=\mu^{-1}(b)$ 上自由作用。因此

$$
P_b\longrightarrow S_b:=P_b/T^3
$$

是光滑主 $T^3$ 丛，$S_b$ 是拓扑为 $S^2$ 的紧致光滑辛曲面。正概率部分及其约化形式为

$$
S_b^{\circ}\simeq(\kappa_-,\kappa_+)\times S^1,\qquad
\omega_{\rm red}=d\chi\wedge d\kappa,\qquad
\operatorname{Area}_\omega(S_b)=2\pi w(b).
$$

**证明。**

在全正部分，定理 [3.5](#thm-geom-moment) 的整数相位坐标将三个占位角完整除去，只留下 $\kappa$ 和 $\chi\bmod2\pi$。限制到固定矩层时，$dX=dY=dZ=0$，故二形式为 $d\chi\wedge d\kappa$。

还须检查闭层端点的自由性。下端在 $X+Y<r$ 时仅 $p_{13}=0$，在 $X+Y>r$ 时仅 $p_0=0$；上端在 $X<Y$ 时仅 $p_1=0$，在 $Y<X$ 时仅 $p_3=0$。条件 [(4.1)](#eq-geom-regular) 排除了双零，因此端点的其余三个底角和中模式均正。

令 $W$ 为五行四列整数矩阵，其第 $s$ 行是 $(1,x_s,y_s,z_s)$，按模式 $0,1,2,3,13$ 排列。直接作整数行消元得到

$$
\begin{array}{c|rrrr}
\text{删除的行 }s&0&1&3&13\\ \hline
\det W_{\Sigma\setminus\{s\}}&-1&-1&-1&-1.
\end{array}
$$

例如保留模式 $0$ 时，用它从其余行减去第一列后，剩下的是由标准坐标及其一次和构成的 $3\times3$ 矩阵，行列式为 $-1$；删除模式 $0$ 时，改用模式 $1$ 消去第一列，同样得到 $-1$。因而这四个子系统均为整可逆。一个群元固定相应射线，就要求其共同相位和三个占位相位满足该整数系统的零同余；整可逆性强制全部为零模 $2\pi$。内部包含任一个这样的四模式子系统，也自由。

由 $\iota_{X_j}\omega=d\mu_j$ 和 $\omega$ 非退化，自由作用的三个独立无穷小作用场对应三个独立微分 $d\mu_j$。故 $b$ 是正则值。紧环面作用是适当作用，因而其自由商为光滑流形并给主丛；将矩映射平移为 $\mu-b$ 后应用辛约化定理，得到唯一的约化辛形式[12](#ref-cannas)。维数为 $8-3-3=2$，其中第一次减三是固定矩层，第二次减三是除去环面轨道。

在每个端点，剩余四个非零振幅的共同相位及占位相位可由上述整可逆系统全部消去，故每个端点的相位圆恰缩为一点。圆柱的两端各压成一点得到 $S^2$。在单零端点，将消失模式的振幅作为复坐标，其模方为到端点的 $\kappa$ 距离，其余模方是该模方的正仿射函数，故封口为光滑圆盘。这也直接验证了商的两极没有有限残余稳定子。最后，在内部积分 $d\chi\wedge d\kappa$ 的正面积密度，得到 $2\pi(\kappa_+-\kappa_-)$；两极为零面积集合。

证毕。

<a id="thm-geom-metric"></a>

**定理 4.2（关系度量与最短相位提升）。**
在 $0<Z<1$、$0<X,Y<r$ 的固定均值正支撑纤维内部，定义

$$
I(\kappa)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}},
\qquad
a_s(\kappa)=\frac{\nu_s}{p_s I(\kappa)}.
$$

由式 [(3.3)](#eq-geom-fullmetric) 对占位相位作用取 Riemannian 商，得到

<a id="eq-geom-reducedmetric"></a>

$$
g_{\rm red}=\frac I2\,d\kappa^2+\frac2I\,d\chi^2.\tag{4.2}
$$

在给定实关系速度 $u$ 及共同相位规范 $p^{\mathsf T}v=0$ 下，约束 $\nu^{\mathsf T}v=u$ 的唯一最小二次相位速度为 $v=a(\kappa)u$，其代价为 $u^2/I$。

此外，

$$
\tau=\log\frac{p_0p_{13}}{p_1p_3},\qquad
\frac{d\tau}{d\kappa}=I>0,\qquad
\zeta=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}
=e^{\tau/2-i\chi}
$$

在正纤维上给出复坐标 $\zeta\in\mathbb C^{\times}$。该坐标不定义零振幅的相位。

**证明。**

概率方向满足 $dp=\nu\,d\kappa$，故式 [(3.3)](#eq-geom-fullmetric) 的概率部分为 $I\,d\kappa^2/2$。对相位方向，先减去共同相位使 $p^{\mathsf T}v=0$。有

$$
\nu^{\mathsf T}a=1,\qquad p^{\mathsf T}a=0,\qquad
\sum_s p_sa_s^2=\frac1I.
$$

任意其他可行速度可写为 $v=au+z$，其中 $\nu^{\mathsf T}z=p^{\mathsf T}z=0$。于是

$$
\sum_s p_sv_s^2
=\frac{u^2}{I}+\sum_s p_sz_s^2,
$$

因为交叉项为 $2u\nu^{\mathsf T}z/I=0$。全正性使等号只在 $z=0$ 时成立。另一方面，$\nu$ 的湮灭空间由 $1,x,y,z$ 四个独立函数张成，所以这项最小化恰好去掉完整的共同相位和三个占位相位方向。度量中的相位系数乘二，给 $2\,d\chi^2/I$，且概率与相位部分没有交叉项。这证明式 [(4.2)](#eq-geom-reducedmetric)。

对数求导使用 $p'=\nu$，得到 $\tau'=\sum_{s\ne2}1/p_s=I$。在下端 $p_0p_{13}$ 趋零而 $p_1p_3$ 有正极限；在上端情况相反，所以 $\tau$ 从 $-\infty$ 严格增加到 $+\infty$。相位的整周期结果来自定理 [3.5](#thm-geom-moment)，因此 $e^{\tau/2-i\chi}$ 将圆柱双射且光滑地参数化为 $\mathbb C^{\times}$。更具体地，置 $\eta=\tau/2$，则

$$
g_{\rm red}=\frac2I(d\eta^2+d\chi^2),\qquad
\omega_{\rm red}=\frac2I\,d\chi\wedge d\eta.
$$

故 $\eta-i\chi$ 的复方向与给定度量及方向相容，$\zeta=e^{\eta-i\chi}$ 是相应复结构下的坐标。若某个底角振幅为零，应改用齐次乘积 $[\psi_0\psi_{13}:\psi_1\psi_3]$ 或实际支撑图；不得取 $\arg0$。

证毕。

式 [(4.2)](#eq-geom-reducedmetric) 是商度量的逐点水平最小值，并不声称存在满足 $d\theta=a(\kappa)d\chi$ 的可积截面。实际上，由 $\nu^{\mathsf T}a=1$、$p^{\mathsf T}a=0$ 微分得到 $p^{\mathsf T}a'=-1$，故 $a'$ 不为零；指定水平提升具有曲率。这一动态结论和下节主丛的拓扑非平凡性需要分别处理。

<a id="thm-geom-curvature-boundary"></a>

**定理 4.3（正 Gaussian 曲率及单零、双零端点）。**
令 $b_0(\kappa)=2/I(\kappa)$；这里 $b_0$ 是标量度量系数，不是可见均值 $b$。关系度量的 Gaussian 曲率为

$$
K=-\frac12 b_0''
=\frac{I''}{I^2}-\frac{2(I')^2}{I^3}
=\frac2{I^3}
\sum_{\substack{i<j\\i,j\in\{0,1,3,13\}}}
\frac{(p_i-\nu_i\nu_jp_j)^2}{p_i^3p_j^3}>0.
$$

在非退化闭纤维的任一端点，设有 $\ell\in\{1,2\}$ 个底角概率消失，$t>0$ 是 $\kappa$ 到端点的距离。其径向距离 $\rho(t)$ 和相位圆周长 $L(t)$ 满足

$$
\rho(t)=\sqrt{2\ell t}+O(t^{3/2}),\qquad
L(t)=2\pi\sqrt{\frac{2t}{\ell}}+O(t^{3/2}).
$$

因此该端的锥角为 $2\pi/\ell$。下端双零恰在 $X+Y=r$，上端双零恰在 $X=Y$。两端的距离有限，度量完备化各加入一点；当两端均单零时封口光滑，双零时为角 $\pi$ 的锥点。

**证明。**

写 $g=b_0^{-1}d\kappa^2+b_0d\chi^2$，令径向弧长坐标满足 $du=d\kappa/\sqrt{b_0}$，并令 $f(u)=\sqrt{b_0(\kappa(u))}$。于是 $g=du^2+f(u)^2d\chi^2$。由该对角度量的 Christoffel 符号 $\Gamma^u_{\chi\chi}=-ff'$、$\Gamma^\chi_{u\chi}=f'/f$，直接得到 $K=-f''/f$。链式法则给 $df/du=b_0'/2$、$d^2f/du^2=b_0''\sqrt{b_0}/2$，故 $K=-b_0''/2$。

因为每个底角满足 $p_s'=\nu_s$ 且 $\nu_s^2=1$，

$$
I'=-\sum_{s\ne2}\frac{\nu_s}{p_s^2},\qquad
I''=2\sum_{s\ne2}\frac1{p_s^3}.
$$

求导 $b_0=2/I$ 给曲率的第二式。将分子展开成无序对，得到

$$
\frac{I^3K}{2}
=\left(\sum_i\frac1{p_i}\right)
\left(\sum_j\frac1{p_j^3}\right)
-\left(\sum_i\frac{\nu_i}{p_i^2}\right)^2
=\sum_{i<j}\frac{(p_i-\nu_i\nu_jp_j)^2}{p_i^3p_j^3}.
$$

同指标项抵消。由于有正、负两类 $\nu_i$，存在异号对，其分子为 $(p_i+p_j)^2>0$，所以曲率严格为正。

端点处每个消失的概率恰等于 $t$，其余底角概率有正极限，因而 $I=\ell/t+O(1)$。积分径向线元及计算圆周长给

$$
\rho(t)=\int_0^t\sqrt{I(s)/2}\,ds,\qquad
L(t)=2\pi\sqrt{2/I(t)},
$$

由上述渐近式得到结论。相位圆直径趋零、径向距离有限，所以每端只加入一个完备化点；两端间的正径向距离使它们不同。单零时，以上系数在径向平方的光滑展开给通常的极坐标封口；亦可直接使用定理 [4.1](#thm-geom-reduction) 的消失振幅复坐标。双零时 $L/\rho\to\pi$，故不能是普通光滑圆盘的无锥角极点。概率反演逐项给出双零条件：下端 $p_0=p_{13}=0$ 恰在 $X+Y=r$；上端 $p_1=p_3=0$ 恰在 $X=Y$。

证毕。

这里的曲率是关系概率--相位曲面的内在 Gaussian 曲率。它不等于相位运输连接的向量值曲率，也不是物理时空曲率。拓扑球面、特定商度量、某种物理空间模型是三个不同层次的断言。

<a id="sec-geometry-chern"></a>

## 5. 主环面丛的过渡函数、Chern 类与面积斜率

<a id="thm-geom-chern"></a>

**定理 5.1（四区域过渡向量及关联线丛的 Chern 数）。**
在条件 [(4.1)](#eq-geom-regular) 下，赋予 $S_b$ 方向 $d\chi\wedge d\kappa$，并将定理 [3.5](#thm-geom-moment) 中的相位作用视作右 $T^3$ 作用。主丛 $P_b\to S_b$ 的一组两图过渡函数为

$$
t(\chi)=c(b)\chi\pmod{2\pi},
$$

其中

<a id="eq-geom-chern-table"></a>

$$
\begin{array}{c|c|c}
\text{区域条件}&\text{两端消失模式 }(\sigma_-,\sigma_+)&c(b)\\ \hline
X+Y<r, X<Y&(13,1)&(-1,0,0)\\
X+Y<r, Y<X&(13,3)&(0,-1,0)\\
X+Y>r, X<Y&(0,1)&(0,1,1)\\
X+Y>r, Y<X&(0,3)&(1,0,1)
\end{array}\tag{5.1}
$$

每个 $c(b)$ 是非零原始整数向量，故该主丛无全局截面，且

<a id="eq-geom-area-slope"></a>

$$
c(b)=-\nabla_{(X,Y,Z)}w(b)
=-\frac1{2\pi}\nabla_{(X,Y,Z)}\operatorname{Area}_\omega(S_b).\tag{5.2}
$$

对任意 $q\in\mathbb Z^3$，用字符 $\rho_q(t)=e^{-iq\cdot t}$ 定义 Hermitian 关联线丛

$$
E_q=P_b\times_{\rho_q}\mathbb C,\qquad
(p\cdot t,z)\sim(p,e^{-iq\cdot t}z).
$$

若第一 Chern 形式采用 $c_1=iF/(2\pi)$，则

$$
\int_{S_b}c_1(E_q)=q\cdot c(b).
$$

**证明。**

因为 $p_2=Z>0$，每条射线可以唯一选择中模式振幅 $\psi_2=\sqrt Z>0$ 的归一化代表。在这个规范下，相位群作用于其余模式的相位增量为

$$
\Delta\theta_s=x_st_X+y_st_Y-t_Z,\qquad s\ne2,
$$

中模式相位增量为零。

下端消失模式 $\sigma_-$ 的 $\nu$ 系数为 $+1$；上端消失模式 $\sigma_+$ 的系数为 $-1$。在除去上极的图中选择相位

$$
\theta^-=\chi e_{\sigma_-};
$$

在除去下极的图中选择

$$
\theta^+=-\chi e_{\sigma_+}.
$$

两者均满足 $\nu^{\mathsf T}\theta=\chi$。其模长统一取式 [(3.1)](#eq-geom-probability) 的正平方根。

这些确为延伸至各极的光滑截面。下端的唯一消失振幅是

$$
z_-=\sqrt{\kappa-\kappa_-}\,e^{-i\chi},
$$

上端的唯一消失振幅是

$$
z_+=\sqrt{\kappa_+-\kappa}\,e^{i\chi}.
$$

由其余四个非零模式的整可逆相位系统，可以在邻域唯一固定这些相位；矩层上的其余模长是 $|z_\pm|^2$ 的正仿射函数的平方根，因而光滑。因此 $z_\pm$ 给出实际商盘坐标和光滑截面。直接计算极坐标面积可知，两盘的复方向均与 $d\chi\wedge d\kappa$ 一致。

在交叠圆柱上，记 $s_+=s_-\cdot t(\chi)$，并写 $t(\chi)=c\chi$。相位差为

$$
\theta^+-\theta^-=-\chi(e_{\sigma_-}+e_{\sigma_+}).
$$

按模式 $0,1,3,13$，求解以下四个整数方程：

$$
\begin{split}
-c_Z&=\Delta\theta_0/\chi,\qquad
c_X-c_Z=\Delta\theta_1/\chi,\\
c_Y-c_Z&=\Delta\theta_3/\chi,\qquad
c_X+c_Y-c_Z=\Delta\theta_{13}/\chi.
\end{split}
$$

例如当 $(\sigma_-,\sigma_+)=(13,1)$ 时，右端依次为 $0,-1,0,-1$，解为 $(-1,0,0)$；其余三种分别给式 [(5.1)](#eq-geom-chern-table) 中的向量。它们均为非零原始整数向量。

若存在全局截面，它与 $s_-$、$s_+$ 的差在相应两盘上分别是光滑 $T^3$ 值函数。每个盘上的函数限制到边界后都零伦，三个圆周分量的绕数均为零；其差不能抵消过渡环 $t(\chi)$ 的非零绕数向量 $c$。矛盾。这是主丛非平凡性的直接过渡函数证明，不从某一具体连接的非零曲率推断拓扑。

关联线丛的局部单位框架满足

$$
e_+=e_- e^{-i(q\cdot c)\chi}.
$$

取任意 unitary connection，并按 $\nabla e_\pm=e_\pm A_\pm$ 记其局部 $i\mathbb R$ 值连接形式，则

$$
A_+-A_-=-i(q\cdot c)d\chi.
$$

由定向 $d\chi\wedge d\kappa$，下盘的正边界方向是 $-\chi$，上盘是 $+\chi$。对两盘分别应用 Stokes 定理，得到

$$
\int_{S_b}F
=\int_{0}^{2\pi}(A_+-A_-)
=-2\pi i(q\cdot c).
$$

故 $\int c_1=q\cdot c$。这与标准线丛的 clutching/Chern 对应一致[11](#ref-hatcher)；这里已明确字符、方向和连接符号。若改用共轭字符或反转球面方向，整体符号相反。

最后，四个区域中的宽度依次是 $X,Y,1-Y-Z,1-X-Z$，其梯度的负值正好为表中的四个向量。由定理 [4.1](#thm-geom-reduction) 的面积式得到式 [(5.2)](#eq-geom-area-slope)。

证毕。

式 [(5.2)](#eq-geom-area-slope) 将同一模型的四个量接起来：概率投影遗漏的区间宽度、约化关系球面的辛面积、面积对可见均值的斜率，以及相位框架主丛的整数拓扑类。它是本五模式上的明确推论，不作一般分类定理或历史优先权主张。两条墙上的斜率变化对应支撑双零和正则性条件的失效，不能未经额外物理建模解释为物理相变。

还须区分两个底空间。正可见域

$$
\mathcal B=\{(X,Y,Z):0<Z<1, 0<X,Y<1-Z\}
$$

是凸开集，其概率核线丛是平凡丛 $\mathcal B\times\mathbb R\nu$。定理 [5.1](#thm-geom-chern) 的非平凡主丛却以固定 $b$ 后的关系球面 $S_b$ 为底。关联线丛 $E_q$ 也不等于把 $\mathcal L_{\rm taut}$ 不加条件地直接下降到该商：下降必须声明具体的等变结构和字符。

<a id="prop-geom-prequantization"></a>

**命题 5.2（约化面积与预量子线丛的整数条件）。**
在正则关系球面 $S_b$ 上，给定实尺度 $s>0$。存在 Hermitian 复线丛及 unitary connection，曲率恰为

$$
F=-is\omega_{\rm red},
$$

当且仅当 $sw(b)\in\mathbb Z$。此时第一 Chern 数为 $sw(b)$。

特别地，在条件 [(4.1)](#eq-geom-regular) 下 $0<w(b)<1/2$，所以尺度 $s=1$ 不可能给出该曲率的线丛。辛面积除以 $2\pi$ 是连续实数，不能直接视作 Chern 整数。

**证明。**

若存在这样的连接，Chern--Weil 公式和面积式给

$$
\int_{S_b}c_1
=\frac{i}{2\pi}\int_{S_b}F
=\frac{s}{2\pi}\int_{S_b}\omega_{\rm red}=sw(b).
$$

第一 Chern 类的积分性可由任意两盘间的 $U(1)$ 过渡函数绕数直接证明[11](#ref-hatcher)，故 $sw(b)$ 必为整数。

反向设 $n=sw(b)\in\mathbb Z$。在上下两图之间以 $e_+=e_-e^{-in\chi}$ 粘合复线丛，并设置

$$
A_-=is(\kappa-\kappa_-)d\chi,\qquad
A_+=is(\kappa-\kappa_+)d\chi.
$$

其差为 $-isw\,d\chi=-in\,d\chi$，正好符合过渡函数的连接变换律。下端 $t=\kappa-\kappa_-$ 时，$t\,d\chi=-\operatorname{Im}(\overline z_-dz_-)$ 光滑；上端同理，所以两个连接形式真正延伸至极点。直接求导得

$$
dA_\pm=is\,d\kappa\wedge d\chi=-is\omega_{\rm red}.
$$

这构造了所需连接，充分性成立。最后由 $w\le r/2<1/2$ 及非退化性知 $0<w<1/2$；正则条件实际排除了达到 $r/2$ 的对称点。

证毕。

上述命题讨论指定曲率在约化球面上的实现。它与整个 $\mathbb{CP}^4$ 上存在整数 Chern 类的 tautological 线丛并不矛盾：若要求原空间的线丛及连接下降后保留指定曲率 $-is\omega_{\rm red}$，须另外核对等变提升、连接对群作用的下降条件，以及 $sw$ 的整数条件。单独一个自由作用下的等变线丛可以下降，这不意味着其连接也自动具有这里规定的曲率。本稿不由面积公式单独宣称“量子化与约化交换”。

<a id="thm-geom-sector"></a>

**定理 5.3（整数对称占位扇区与面积计数）。**
另供对称张量载体 $\operatorname{Sym}^m(\mathbb C^5)$，其中 $m\ge0$ 为整数。其标准占位基由非负整数

$$
(n_0,n_1,n_2,n_3,n_{13}),\qquad \sum_s n_s=m
$$

标记。固定整数荷

$$
W=n_2,\qquad U=n_1+n_{13},\qquad V=n_3+n_{13},
$$

并假设 $0\le W\le m$、$R=m-W$、$0\le U,V\le R$。则固定荷扇区的完整基为

$$
|k\rangle=|R-U-V+k, U-k, W, V-k, k\rangle,
$$

其中

$$
k_-:=\max(0,U+V-R)\le k\le k_+:=\min(U,V).
$$

其维数为 $D=k_+-k_-+1$。若 $m>0$ 并令

$$
X=U/m,\qquad Y=V/m,\qquad Z=W/m,
$$

则对包括退化边界在内的全部这些整数荷都有

$$
D=1+mw(b).
$$

若还满足正则条件 [(4.1)](#eq-geom-regular)，则进一步有

$$
D=1+\frac{m\operatorname{Area}_\omega(S_b)}{2\pi}.
$$

**证明。**

在标准对称占位基中，给定 $n_{13}=k$ 后，三个固定荷方程唯一给出 $n_1=U-k$、$n_3=V-k$、$n_2=W$；总粒子数再给出 $n_0=R-U-V+k$。这五个整数均非负，恰好等价于 $k_-\le k\le k_+$。由于 $U,V\le R$，下界不超过上界，故基非空。不同 $k$ 对应不同的正交占位基向量，因此维数是区间整数个数 $k_+-k_-+1$。

当 $m>0$ 时，乘以 $m$ 保持最大值、最小值及次序，故

$$
m\kappa_-=\max(0,U+V-R)=k_-,\qquad
m\kappa_+=\min(U,V)=k_+.
$$

于是 $D=1+m(\kappa_+-\kappa_-)=1+mw$。正则时再使用定理 [4.1](#thm-geom-reduction) 的光滑球面积公式。$m=0$ 时固定荷全部为零，只有唯一真空占位向量，故 $D=1$；此时不定义除以 $m$ 的归一化均值。

证毕。

该计数的对象是明确增加的对称张量载体及其固定荷子空间。它不计数原生有序窗口历史，不识别其接缝守卫，也不保证一次实验取得 $\log D$ 比特。相应概率格和整数核与基础卷、辛完成卷的固定载体结果一致[1](#ref-repo-found)、[2](#ref-repo-sp)；将此载体接到实际制备、控制和读出时，仍需声明接口和资源。

<a id="sec-bundle-calculus"></a>

## 6. 向量丛的粘合、运算与连接

本章补足后续量子输运所需的固定秩向量丛运算。底空间均为 Hausdorff、第二可数、仿紧光滑流形；丛和映射均光滑。以下是经典丛论及连接论的明确接口[11](#ref-hatcher)、[12](#ref-cannas)，不从“兼容纤维”这一名称推断这些假设。

<a id="def-bc-cocycle"></a>

**定义 6.1（酉过渡余循环与关联表示）。**
给定开覆盖 $(U_i)$，秩 $d$ 的酉余循环是映射

$$
g_{ij}:U_i\cap U_j\to U(d),\qquad
g_{ii}=I,\quad g_{ji}=g_{ij}^{-1},\quad
g_{ij}g_{jk}=g_{ik}.
$$

约定局部列标架满足 $e_j=e_i g_{ij}$，故向量坐标满足 $v_i=g_{ij}v_j$。对光滑酉表示
$\rho:U(d)\to U(r)$，其关联丛使用过渡 $\rho(g_{ij})$。等价地，若 $P$ 是酉标架主丛，则

$$
E_\rho=P\times_\rho\mathbb C^r,\qquad
(p\cdot u,v)\sim(p,\rho(u)v).
$$

局部连接写为 $\nabla(e_i v)=e_i(dv+A_i v)$，其中
$A_i\in\Omega^1(U_i;\mathfrak u(d))$。矩阵值形式的乘积同时使用矩阵乘法和外积。

<a id="thm-bc-gluing"></a>

**定理 6.2（余循环粘合与 Hermitian 丛）。**
每个酉余循环定义秩 $d$ 的 Hermitian 向量丛；反向，每个此类丛在单位正交局部标架中产生酉余循环。换标架 $e_i'=e_i h_i$ 时，

$$
g_{ij}'=h_i^{-1}g_{ij}h_j.
$$

这些规范等价余循环给出酉同构的丛；给定同一覆盖上的局部平凡化，任意酉丛同构也有这种形式。每个 Hermitian 丛存在保持度量的连接，且 $E_\rho$ 是秩 $r$ 的 Hermitian 丛。

**证明。**

在不交并 $\coprod_i(U_i\times\mathbb C^d)$ 中规定
$(x,v,j)\sim(x,g_{ij}(x)v,i)$。单位、逆元及余循环条件恰保证这是等价关系。对 $x\in U_i$，公式

$$
[(x,v,j)]\longmapsto (x,g_{ij}(x)v)
$$

给出投影逆像上的局部平凡化；余循环保证它不依赖代表。这些局部图的转换线性且光滑，因此逐纤维的向量运算良定。它们也说明每个投影逆像为开集。不同底点可由底空间的不交邻域分离；相同底点上的不同向量在一个产品图中分离，故总空间 Hausdorff。利用可数局部有限加细取得可数图册。酉性使局部标准内积在交叠上一致，故得到 Hermitian 度量。

反向选择单位正交标架，基变换必为酉矩阵；在三重交叠上连续换基给余循环条件。代入 $e_i'=e_i h_i$ 得到所列规范公式，它也逐图构造相应丛同构。任意丛同构在局部图中是酉矩阵函数，反向给同一关系。

取从属于平凡化覆盖的光滑单位分解 $(\varphi_i)$，在每张单位标架图上取平凡连接 $\nabla_i^0$。表达式 $\nabla=\sum_i\varphi_i\nabla_i^0$ 由局部有限性和支撑条件定义全局连接；$\sum_i\varphi_i=1$ 保证 Leibniz 法则，度量相容性对该仿射组合保持。最后，$\rho$ 保持乘法和单位性，所以 $\rho(g_{ij})$ 再次满足全部粘合条件。

证毕。

<a id="thm-bc-operations"></a>

**定理 6.3（基本丛运算、诱导连接与曲率）。**
设 $E,G$ 的过渡为 $g,h$、局部连接形式为 $A,B$、曲率为 $F,G_0$，并令 $f:N\to M$ 光滑。直和、张量、复线性对偶、端同态和拉回丛的过渡依次为

$$
g\oplus h,\qquad g\otimes h,\qquad
g^{-\mathsf T},\qquad (T\mapsto gTg^{-1}),\qquad g\circ f.
$$

它们的诱导连接形式及曲率为

$$
\begin{array}{c|c|c}
\text{丛}&\text{连接形式或协变导数}&\text{曲率}\\ \hline
E\oplus G&A\oplus B&F\oplus G_0\\
E\otimes G&A\otimes I+I\otimes B&F\otimes I+I\otimes G_0\\
E^*&-A^{\mathsf T}&-F^{\mathsf T}\\
\operatorname{End}E&\nabla T=dT+AT-TA&T\mapsto FT-TF\\
f^*E&f^*A&f^*F
\end{array}
$$

若 $`\rho_*`$ 是 $\rho$ 在单位元处的导数，则关联连接和曲率是 $`\rho_*(A)`$、$`\rho_*(F)`$。

特别地，$U(d)$ 在无迹 Hermitian 矩阵上的共轭表示

$$
T\longmapsto uTu^\dagger,\qquad
\operatorname{Herm}_0(d)=\{T=T^\dagger:\operatorname{Tr}T=0\}
$$

给出实秩 $d^2-1$ 的关联丛，内积为 $\operatorname{Tr}(ST)$。它是实表示，不能把该秩当作复维数。

**证明。**

直和及张量的过渡由分别换基得到。对偶评价必须保持
$\ell(v)$ 不变，所以复线性对偶过渡是 $g^{-\mathsf T}$；这不同于另取反线性对偶。保持端同态的作用给 $T_i=g_{ij}T_jg_{ij}^{-1}$。拉回只是将原过渡与 $f$ 复合。

在直和上分别微分，在张量上要求
$\nabla(s\otimes t)=(\nabla s)\otimes t+s\otimes\nabla t$，
即得前两行。张量连接平方时，两个不同因子上的一阶项因外积反对称而抵消。对恒等式
$d(\ell(s))=(\nabla\ell)(s)+\ell(\nabla s)$ 求值，得到对偶连接 $-A^{\mathsf T}$；再求平方得到 $-F^{\mathsf T}$。对
$\nabla(Ts)=(\nabla T)s+T\nabla s$ 使用 Leibniz 法则得到端同态公式，再次微分得 $[F,T]$。外微分与拉回交换，给最后一行。

$`\rho_*`$ 线性且保持 Lie 括号，故将
$F=dA+\frac12[A\wedge A]$ 送到
$`d\rho_*(A)+\frac12[\rho_*(A)\wedge\rho_*(A)]`$，这证明关联曲率公式，而无须假定 $`\rho_*`$ 保持任意矩阵乘法。最后，酉共轭保持自伴性、迹和 $\operatorname{Tr}(ST)$；无迹 Hermitian 矩阵的实维数为 $d^2-1$，故该实关联丛和所列度量良定。

证毕。

<a id="thm-bc-curvature"></a>

**定理 6.4（规范变换、Bianchi 恒等式及第一 Chern 形式）。**
在定义 [6.1](#def-bc-cocycle) 的标架规范下，

$$
A_j=g_{ij}^{-1}A_i g_{ij}+g_{ij}^{-1}dg_{ij},
\qquad F_i=dA_i+A_i\wedge A_i,
\qquad F_j=g_{ij}^{-1}F_i g_{ij}.
$$

曲率满足 Bianchi 恒等式

$$
dF+A\wedge F-F\wedge A=0.
$$

行列式线丛的连接和曲率分别为
$\operatorname{Tr}A$、$\operatorname{Tr}F$。全局实二形式

$$
c_1(\nabla)=\frac{i}{2\pi}\operatorname{Tr}F
$$

闭合，其 de Rham 上同调类与 Hermitian 连接的选择无关。对任意闭定向光滑曲面 $\Sigma$ 及光滑映射 $f:\Sigma\to M$，

$$
\int_\Sigma f^*c_1(\nabla)\in\mathbb Z.
$$

这里仅证明第一 Chern 形式及其曲面整数配对，不声称已经重证全部高阶 Chern--Weil 理论。

**证明。**

在 $\nabla e_j=\nabla(e_i g_{ij})$ 中应用 Leibniz 法则，并用 $e_j=e_i g_{ij}$，即得连接变换。连接平方消去对截面的一阶导数项，给 $F=dA+A\wedge A$；$\nabla^2$ 的张量性给曲率共轭变换。展开
$d(A\wedge A)=dA\wedge A-A\wedge dA$，
代入 $dF+A\wedge F-F\wedge A$，各项逐项抵消，得到 Bianchi 恒等式。

对局部楔积标架 $e_1\wedge\cdots\wedge e_d$ 微分时，只有各对角项能保留全部基向量，故连接形式为 $\operatorname{Tr}A$。矩阵迹对交换子为零，而
$\operatorname{Tr}(A\wedge A)=0$，所以其曲率为
$d\operatorname{Tr}A=\operatorname{Tr}F$。
因此 $c_1(\nabla)$ 全局良定且闭；unitary 连接的曲率取值于反 Hermitian 矩阵，故该二形式为实值。若换连接为 $A'$，其差按共轭变换，所以
$a=\operatorname{Tr}(A'-A)$ 是全局一形式，并且

$$
\operatorname{Tr}(F'-F)=da.
$$

于是两个第一 Chern 形式之差为恰当形式。

最后在拉回的行列式线丛上证明整数性。取曲面的有限光滑三角剖分，使每个闭三角形落在一张平凡化图内。先在顶点选单位向量，再沿每条边用 $U(1)$ 的路径连通性延拓，得到整个一维骨架上的连续、逐边光滑单位截面 $s$。在每个定向三角形 $\sigma$ 内选单位框架 $e_\sigma$，在其边界写
$s=e_\sigma g_\sigma$，其中
$g_\sigma:\partial\sigma\to U(1)$ 为闭环。若 $A_s$ 表示沿骨架的连接形式，则

$$
A_s=A_\sigma+g_\sigma^{-1}dg_\sigma,\qquad
\int_\sigma F
=\int_{\partial\sigma}A_s-2\pi i\,\deg(g_\sigma).
$$

相邻三角形在公共边上的方向相反，且使用同一个 $s$，所以求和后全部 $A_s$ 边积分抵消。因此

$$
\int_\Sigma F=-2\pi i\sum_\sigma\deg(g_\sigma),\qquad
\frac{i}{2\pi}\int_\Sigma F=\sum_\sigma\deg(g_\sigma)\in\mathbb Z.
$$

这同时说明整数来自过渡函数的绕数，不来自某条局部连接系数的取整。行列式曲率等于原丛的迹曲率，故得到定理中的公式。

证毕。

这些操作说明，量子态、观测算子和观察者框架可以处在不同但关联的丛中：态在复向量丛中，混合态的无迹变化在 $\operatorname{Herm}_0$ 实关联丛中，门和线性观测运输在 $\operatorname{End}$ 或相应 Hom 丛中。普通密度矩阵集合仍受正性和迹一约束；它不是整个实关联向量空间。是否存在由特定 Hamiltonian 本征空间给出的 Berry 连接，还须额外提供固定秩谱投影及光滑性假设[13](#ref-simon)。

<a id="sec-transport"></a>

## 7. 向量丛输运、预测相容与控制成本

本章给出从读出兼容集合到向量丛、再到门序列预测的严格桥梁。
背景采用固定秩 Hermitian 向量丛的标准定义
[11](#ref-hatcher)、[13](#ref-simon)、[14](#ref-wilczek)；与项目相连接的对象是固定快照中的相位输运、
回路及读出结构[3](#ref-repo-hol)。
本章的证明只使用明确列出的数学假设，不把几何表示本身当作物理定律的推导。

### 7.1. Hermitian 丛与读出核

<a id="def-transport-data"></a>

**定义 7.1（输运--读出数据）。**
设 $M$ 为光滑、仿紧流形，$\pi:\mathcal H\to M$ 为秩 $d\geq 2$
的复 Hermitian 向量丛。在局部酉标架下，过渡函数
$g_{\alpha\beta}:U_\alpha\cap U_\beta\to U(d)$ 满足
$g_{\alpha\beta}g_{\beta\gamma}g_{\gamma\alpha}=I$。
度量相容联络 $\nabla$ 的局部矩阵 $A_\alpha$ 为反 Hermitian
矩阵值一形式，并满足

$$
A_\beta=g_{\alpha\beta}^{-1}A_\alpha g_{\alpha\beta}
              +g_{\alpha\beta}^{-1}dg_{\alpha\beta},
 \qquad
 F_\alpha=dA_\alpha+A_\alpha\wedge A_\alpha.
$$

每条分段光滑路径 $\gamma:b\to c$ 给出酉平行输运
$U_\gamma:\mathcal H_b\to\mathcal H_c$。

定义实向量丛

$$
\mathcal V=\operatorname{Herm}_0(\mathcal H),\qquad
 \mathcal V_b=\{X=X^\dagger:\operatorname{Tr}X=0\},
 \qquad
 \langle X,Y\rangle=\operatorname{Tr}(XY).
$$

其秩为 $d^2-1$，诱导联络记为 $D$；局部表达为
$DX=dX+[A,X]$，平行输运为

$$
T_\gamma(X)=U_\gamma XU_\gamma^\dagger.
$$

读出为光滑实线性丛映射
$L:\mathcal V\to M\times\mathbb R^k$。
记 $K_b=\ker L_b$。对密度矩阵 $\rho$，实际的仿射读出为
$L_b(\rho-I/d)$，已知的常数读出可以另行附加。

这里的 $\mathcal V$ 是实的算符丛，不是复的态振幅丛。
固定读出对应的合法状态集合

$$
\mathcal C_{b,y}
 =\{\rho\geq0:\operatorname{Tr}\rho=1,\
                 L_b(\rho-I/d)=y\}
$$

一般是仿射空间与正半定锥的截面。
因此，兼容集合 $\mathcal C_{b,y}$ 本身通常不是向量空间；
其不可辨差方向才由 $K_b$ 描述。

<a id="thm-kernel-bundle"></a>

**定理 7.2（恒秩读出的核丛与正合列）。**
若 $\operatorname{rank}L_b=r$ 在 $M$ 上恒定，则
$K=\coprod_bK_b$ 是秩 $d^2-1-r$ 的光滑实向量子丛，
$\mathcal R=\operatorname{im}L$ 是秩 $r$ 的光滑子丛，且

$$
0\longrightarrow K\longrightarrow\mathcal V
   \overset{L}\longrightarrow\mathcal R\longrightarrow0
 \quad\text{及}\quad
 \mathcal V/K\simeq\mathcal R
$$

成立。若 $Q$ 是到 $K$ 的正交投影，$P=I-Q$，
则 $\mathcal V=K\oplus K^\perp$，并且
$L|_{K^\perp}:K^\perp\to\mathcal R$ 是丛同构。

**证明。**

在任一点的局部平凡化中，选取 $L$ 矩阵的一个非零
$r\times r$ 子式。缩小邻域后该子式仍可逆。
按对应的列分成枢轴变量和自由变量，再按相应的行求解；
核向量的枢轴坐标是自由坐标的光滑线性函数。
于是得到 $d^2-1-r$ 个光滑线性独立的核截面。
同一子式也给出像的局部标架，故核与像均为光滑子丛。

纤维上的第一同构定理给出 $\mathcal V_b/K_b\simeq\mathcal R_b$；
上述局部标架保证这些同构光滑地拼接。
在 Hermitian 丛诱导的实内积下，核的正交投影光滑，
从而得到正交直和。$L|_{K^\perp}$ 在每个纤维上既单射又满射；
用局部矩阵求逆即得光滑逆映射。

证毕。

若秩改变，以上定理只能分别用于恒秩区域。
把不同秩区域合并后，不能继续沿用固定秩向量丛的结论。

### 7.2. 预测何时能够下降到读出

<a id="thm-single-path-descent"></a>

**定理 7.3（单路径下降与信息秩限制）。**
固定路径 $\gamma:b\to c$。以下两项等价：

$$
\exists\,\overline T_\gamma:\operatorname{im}L_b
                  \to\operatorname{im}L_c,\qquad
 \overline T_\gamma L_b=L_cT_\gamma,
 \tag{D1}
$$

其中 $\overline T_\gamma$ 为实线性映射；以及

$$
T_\gamma K_b\subseteq K_c.
 \tag{D2}
$$

满足条件时，$\overline T_\gamma$ 唯一。
若两端读出秩相同，则 (D2) 等价于
$T_\gamma K_b=K_c$。

即使允许预测器只在合法态读出上定义、且不预先要求线性，
如果它对所有输入密度矩阵都精确满足上述预测任务，
仍然必须有 (D2)。
此外，对任意可逆 $T_\gamma$，

$$
\text{(D1)}\quad\Longrightarrow\quad
 \operatorname{rank}L_c\leq\operatorname{rank}L_b.
 \tag{D3}
$$

**证明。**

若 (D1) 成立，$X\in K_b$ 蕴含
$L_cT_\gamma X=\overline T_\gamma0=0$，故 (D2) 成立。
反过来，定义

$$
\overline T_\gamma(L_bX)=L_cT_\gamma X.
$$

若 $L_bX=L_bY$，则 $X-Y\in K_b$，由 (D2) 得到右侧相等，
所以定义良好。线性与唯一性立即成立。
相同秩使两端核等维，而 $T_\gamma$ 可逆，
故核包含等价于核相等。

为验证合法态版本的必要性，取任意 $X\in K_b$。
选足够小的 $\epsilon>0$，使
$\rho_\pm=I/d\pm\epsilon X$ 均为正半定。
它们具有相同初始读出。如果同一预测器在所有态上精确，
则其未来读出也相同；两者之差给出
$2\epsilon L_cT_\gamma X=0$。
因此 (D2) 仍成立。

最后，可逆性及 (D2) 给出
$\dim K_b\leq\dim K_c$；两端 $\mathcal V$ 等维，
应用秩--零化度公式即得 (D3)。

证毕。

(D3) 限制的是从旧摘要进行的、对所有状态均正确的确定性预测。
新增实际测量、读取原来未纳入摘要的记忆、限制状态类或加入先验，
会改变该任务的输入或量词。仅增加编码长度或门序列长度，
不构成绕过 (D3) 的理由。

<a id="thm-parallel-kernel"></a>

**定理 7.4（全路径闭合、平行核与端点独立性）。**
在定理 [7.2](#thm-kernel-bundle) 的恒秩假设下，以下条件等价：

1. 对所有分段光滑路径 $\gamma:b\to c$，读出预测均可下降；

2. $T_\gamma K_b=K_c$ 对所有这些路径成立；

3. $D\Gamma(K)\subseteq\Omega^1(M;K)$；

4. $DQ=0$。

此时商丛带良定义的度量联络

$$
\overline D[X]=[DX].
$$

在 $M$ 的每个路径连通分支上，商平行输运只依赖路径起终点，
当且仅当商联络的所有闭路 holonomy 均为恒等。

若 $\mathcal F=D^2$，以上条件蕴含
$[\mathcal F,Q]=0$，但此曲率条件一般不足以推出 $DQ=0$。

**证明。**

前两项由定理 [7.3](#thm-single-path-descent) 及恒秩条件等价。
局部选择适应 $K\oplus K^\perp$ 的正交标架。
条件 $D\Gamma(K)\subseteq\Omega^1(M;K)$ 使联络矩阵的一个
非对角块为零；度量相容性使另一个非对角块也为零，
因而联络矩阵与 $Q$ 交换。这恰好是 $DQ=0$。
相反，$DQ=0$ 立即给出 $D(QX)=QDX$，故保持 $K$。

在适应标架下，平行输运微分方程分成两个独立的对角块，
所以第三项蕴含第二项。
若第二项成立，则对任意曲线 $\gamma$，

$$
T_{\gamma|[0,t]}^{-1}\,Q_{\gamma(t)}\,
 T_{\gamma|[0,t]}=Q_{\gamma(0)}.
$$

对 $t$ 求导得到 $D_{\dot\gamma}Q=0$；
所有切向量均可由曲线实现，故第四项成立。

若用 $X+Y$ 代替 $X$，其中 $Y$ 为核截面，则
$D(X+Y)-DX=DY$ 仍在核中。因此 $\overline D$ 与代表无关。
若商闭路输运恒等，两条同起终点路径的商输运之差可由其中一条
接上另一条反向路径表达，所以两者相等。反向结论取常值路径比较即可。

最后，对 $DQ=0$ 再施一次协变导数，得到
$0=D^2Q=[\mathcal F,Q]$。不足性可在平凡平面丛上看出：
取 $D=d$，并令 $K_x$ 为方向角随 $x$ 改变的一维子空间。
这时 $\mathcal F=0$，但 $DQ=dQ\neq0$。

证毕。

此定理使用全部分段光滑路径及反向路径。
若允许的门只形成有向路径类，应直接使用单路径下降条件；
不能在没有可逆路径许可时套用闭路群的等价表述。

还须区分两个命题：$K$ 平行只保证指定门路径的预测闭合；
商 holonomy 平凡才进一步消除可见的路径记忆。
对一个给定根点子空间 $K_0$，存在经过它的平行子丛，
等价于根点的全 holonomy 群保持 $K_0$。
充分性可通过 $K_b=T_\gamma K_0$ 构造：
holonomy 保持性保证该定义不依赖所选路径。
对一个已经指定的读出核丛，仍须验证它与此构造的子丛一致。

<a id="ex-flat-monodromy"></a>

**命题 7.5（反例：平坦、平凡底丛仍可泄漏隐藏方向）。**
取 $M=S^1$，$\mathcal H=M\times\mathbb C^2$，
并令

$$
A=\frac{i}{8}\sigma_y\,d\theta,\qquad \nabla=d+A.
$$

这里 $d\theta$ 是圆上的全局角一形式。
曲率为零，但绕一圈的平行输运为

$$
U=\exp(-i\pi\sigma_y/4),\qquad
 U\sigma_zU^\dagger=\sigma_x.
$$

取

$$
L(X)=\bigl(\operatorname{Tr}(\sigma_xX),
           \operatorname{Tr}(\sigma_yX)\bigr),
 \qquad K=\mathbb R\sigma_z.
$$

则 $\rho_\pm=(I\pm\sigma_z)/2$ 初始读出均为 $(0,0)$，
绕圈后的读出分别为 $(1,0)$ 和 $(-1,0)$。

**证明。**

一维基底上的二形式为零，故 $F=dA+A\wedge A=0$。
平行输运方程为 $\dot U=-A(\dot\gamma)U$，
积分一圈得到所示指数矩阵。Pauli 矩阵乘法直接给出
$U\sigma_zU^\dagger=\sigma_x$。
利用 $\operatorname{Tr}(\sigma_i\sigma_j)=2\delta_{ij}$，
即可算得初末读出。于是 $T_\gamma K\not\subseteq K$，
由定理 [7.3](#thm-single-path-descent)，商预测不闭合。

证毕。

该例同时区分拓扑平凡、曲率为零和 holonomy 平凡。
一般有限图上的固定秩复向量丛也可平凡化：
先在顶点选择标架，再利用 $U(d)$ 的道路连通性沿每条边延拓。
然而，指定的边输运仍可具有非平凡闭路乘积。
从图上的闭路乘积谈二维曲率，必须再给出填充面或二维胞腔结构。

### 7.3. FIB 五模的最小相位输运

本节沿用模式顺序 $\Sigma=(0,1,2,3,13)$，设

$$
\nu=(1,-1,0,-1,1),\qquad r=1-Z,
$$

并固定

$$
0<Z<1,\quad 0<X,Y<r,\quad
 L_0=\max(0,X+Y-r),\quad U_0=\min(X,Y).
$$

在开区间 $L_0<\kappa<U_0$ 内定义

$$
p(\kappa)=(r-X-Y+\kappa,\ X-\kappa,\ Z,\
                         Y-\kappa,\ \kappa),\qquad
 \psi_s=\sqrt{p_s}\,e^{-i\theta_s}.
$$

所有 $p_s$ 均正，且 $p'_s=\nu_s$。
固定中间分量相位 $\theta_2=0$，令
$\chi=\nu^{\mathsf T}\theta$。相位变量按模 $2\pi$ 理解；
微分与矩形计算先在一个实值提升的局部相位图中进行。

<a id="thm-minimal-phase"></a>

**定理 7.6（最小相位提升、曲率与水平截面的不存在）。**
记

$$
I(\kappa)=\sum_s\frac{\nu_s^2}{p_s(\kappa)},\qquad
 a_s(\kappa)=\frac{\nu_s}{p_s(\kappa)I(\kappa)}.
$$

在固定 $\kappa$、固定 $\theta_2=0$ 的相位切空间中，
对任意给定 $\dot\chi=u$，二次相位方差代价

$$
q_p(v,v)=\sum_s p_sv_s^2-\left(\sum_s p_sv_s\right)^2,
 \qquad v_2=0,\quad \nu^{\mathsf T}v=u,
$$

具有唯一最小值 $u^2/I$，由 $v_s=a_su$ 达到。
在前章辛面积为 $2\pi$ 的 Fubini--Study 度量归一化下，
相位速度平方为 $2q_p$，故其最小值是 $2u^2/I$。

在局部坐标 $(\kappa,\chi)$ 上，规定最小相位水平提升为

$$
H_\kappa=\partial_\kappa,\qquad
 H_\chi=\sum_s a_s(\kappa)\partial_{\theta_s}.
$$

令 $\mathfrak t=\{v\in\mathbb R^5:\nu^{\mathsf T}v=0,\ v_2=0\}$。
相应的 $\mathfrak t$ 值联络形式及曲率为

$$
\beta_s=d\theta_s-a_s\,d\chi,\qquad
 F^\beta_s=d\beta_s=-a_s'(\kappa)\,d\kappa\wedge d\chi.
$$

其中中间分量恒为零；其余分量给出三维相位环面的联络。
该曲率在每个内部点都非零。因此，任何非空开矩形上
都不存在同时沿两个基方向水平的 $C^2$ 截面。

**证明。**

先注意 $\sum_s\nu_s=0$、$\nu_2=0$，
所以 $\nu^{\mathsf T}a=1$、$a_2=0$ 且 $\sum_sp_sa_s=0$。
若 $q_p(v,v)=0$，所有 $v_s$ 必相等；
由 $p_2>0$ 与 $v_2=0$ 得到 $v=0$，
故 $q_p$ 在所用相位切空间上正定。

令 $m=\sum_sp_sv_s$。带约束的驻点方程对 $s\neq2$ 为
$p_s(v_s-m)=\lambda\nu_s$。
把这些方程求和得到 $m=(1-Z)m$，
故 $m=0$，再由 $\nu^{\mathsf T}v=u$ 得到
$\lambda=u/I$。因此驻点为 $v=au$；
正定二次型保证它是唯一极小点。
代回得 $q_p(au,au)=u^2/I$。

因为 $\nu^{\mathsf T}a=1$，
$\nu^{\mathsf T}\beta=d\chi-d\chi=0$；
而在竖直方向 $\nu^{\mathsf T}v=0$ 上，$\beta(v)=v$。
故 $\beta$ 确为相位平移主丛的局部联络形式。
结构群为阿贝尔环面，其曲率就是 $d\beta$，
从而得到所列公式。

为证明非零，微分恒等式 $\sum_sp_sa_s=0$：

$$
0=\sum_s\nu_sa_s+\sum_sp_sa_s'
   =1+\sum_sp_sa_s'.
$$

所以 $a'(\kappa)$ 不可能为零。
若存在水平截面 $\theta=\theta(\kappa,\chi)$，
则必须有 $\partial_\kappa\theta_s=0$ 和
$\partial_\chi\theta_s=a_s(\kappa)$。
交换混合偏导会给出 $a_s'=0$ 对所有 $s$ 成立，矛盾。

证毕。

这里的无水平截面是相对于所指定联络的局部不可积性。
它不表示该局部主丛在拓扑上非平凡：
开矩形上的底丛可以平凡，而联络曲率仍不为零。

<a id="thm-rectangle-holonomy"></a>

**定理 7.7（矩形相位 holonomy 与有参考的干涉读出）。**
取内部参数 $\kappa_0<\kappa_1$，并在局部相位提升中依次走

$$
(\kappa_0,\chi_0)\to(\kappa_0,\chi_0+\eta)
 \to(\kappa_1,\chi_0+\eta)
 \to(\kappa_1,\chi_0)\to(\kappa_0,\chi_0).
$$

按定理 [7.6](#thm-minimal-phase) 水平提升后，端点相位增量恰为

$$
h_s=\eta\bigl(a_s(\kappa_0)-a_s(\kappa_1)\bigr).
 \tag{R1}
$$

它满足 $h_2=0$、$\nu^{\mathsf T}h=0$，
所以闭路保持全部 $p_s$ 和约化相位 $\chi$。

若 $\eta\neq0$ 充分小，则 $h$ 在相位环面中非零。
在保留固定五模相位参考、允许二模相干读出的实验模型中，
存在算符范数为 $1$ 的 Hermitian 读出区分闭路前后状态。
具体地，对某一对满足 $h_s-h_t\notin2\pi\mathbb Z$ 的模式，
可选择

$$
O_{st}(\alpha)=e^{i\alpha}|s\rangle\langle t|
                 +e^{-i\alpha}|t\rangle\langle s|
$$

使两态期望值之差的绝对值等于

$$
4\sqrt{p_sp_t}\,
       \left|\sin\frac{h_s-h_t}{2}\right|>0.
 \tag{R2}
$$

**证明。**

沿两条 $\kappa$ 边有 $d\theta=0$；
沿两条 $\chi$ 边分别积分
$a(\kappa_0)\,d\chi$ 和 $a(\kappa_1)\,d\chi$，
即得 (R1)。$h_2=0$ 与 $\nu^{\mathsf T}h=0$ 来自
$a_2=0$、$\nu^{\mathsf T}a=1$。

还需验证 $a(\kappa_0)\neq a(\kappa_1)$。
若相等，则对 $\nu_s\neq0$ 的四个模式，
$p_s(\kappa_0)I(\kappa_0)=p_s(\kappa_1)I(\kappa_1)$，
故四个概率向量成比例。它们的总和均为 $r>0$，
比例只能为 $1$，进而 $\kappa_0=\kappa_1$，矛盾。
取足够小的非零 $\eta$，可避免非零 $h$ 落入周期格点。
由于 $h_2=0$ 且 $p_2>0$，总能找到所需模式对。

记 $\Delta=\theta_s-\theta_t$、$\delta=h_s-h_t$。
闭路前后对 $O_{st}(\alpha)$ 的期望值分别为
$2\sqrt{p_sp_t}\cos(\alpha+\Delta)$ 和
$2\sqrt{p_sp_t}\cos(\alpha+\Delta+\delta)$。
取 $\alpha=\pi/2-\Delta-\delta/2$ 即得 (R2)。
该算符在所选二维子空间的本征值为 $\pm1$，
在其正交补上为零，故算符范数为 $1$。

证毕。

(R2) 使用相位参考，其算符通常不下降为 $T^3$ 商空间上的函数。
若把整个 $T^3$ 当作不可观测的纯规范冗余，
就不能同时把这种非不变二模读出列为允许的实验。
因此，(R1) 是主丛输运结论；(R2) 是附加参考装置后的操作性结论。

### 7.4. 双控制模型与精确成本下界

<a id="def-heisenberg-control"></a>

**定义 7.8（Heisenberg 双控制模型）。**
在 $\mathbb R^3$ 坐标 $(x,y,z)$ 上定义

$$
\mathsf P=\partial_x,\qquad
 \mathsf Q=\partial_y+x\partial_z.
$$

允许绝对连续轨迹满足

$$
\dot x=u,\qquad \dot y=v,\qquad \dot z=xv,
 \qquad
 \ell=\int_0^T\sqrt{u(t)^2+v(t)^2}\,dt.
$$

控制 $u,v$ 可取正负值。该模型用来表示两个可控方向的
非交换耦合；要将具体项目的双墙局部系统识别为此模型，
还需要提供坐标变换或受控近似误差。

<a id="thm-heisenberg-cost"></a>

**定理 7.9（括号位移、等周成本与达到等号的圆）。**
上述模型满足
$[\mathsf P,\mathsf Q]=\partial_z$。
若轨迹从 $(0,0,0)$ 出发，平面投影闭合，
终点为 $(0,0,\tau)$，则

$$
\tau=\oint x\,dy,\qquad
 \ell^2\geq4\pi|\tau|.
 \tag{H1}
$$

在整个 $\mathbb R^3$ 模型中，这一下界可达到：
$\tau\neq0$ 时取半径 $R=\sqrt{|\tau|/\pi}$ 的有向圆，
其平面投影经过原点；$\tau=0$ 时取常值轨迹。

若进一步规定
$\sqrt{u^2+v^2}\leq v_{\max}>0$，则

$$
T\geq\frac{\sqrt{4\pi|\tau|}}{v_{\max}}.
 \tag{H2}
$$

采用常速圆可以达到 (H2)。

**证明。**

对任意光滑函数 $f$，

$$
[\mathsf P,\mathsf Q]f
 =\partial_x(\partial_yf+x\partial_zf)
  -(\partial_y+x\partial_z)\partial_xf
 =\partial_zf.
$$

对轨迹积分 $\dot z=x\dot y$，即得面积表达式。

若 $\ell=0$，结论显然。否则将闭合平面曲线按弧长
$s\in[0,\ell]$ 参数化，记为 $r(s)=(x(s),y(s))$；
平移曲线使其均值为零不改变 $\oint x\,dy$。
由分部积分及闭合性，

$$
\tau=\frac12\int_0^\ell(xy'-yx')\,ds.
$$

Cauchy--Schwarz 不等式与周期 Wirtinger 不等式给出

$$
|\tau|
 \leq\frac12
       \left(\int_0^\ell|r|^2ds\right)^{1/2}
       \left(\int_0^\ell|r'|^2ds\right)^{1/2}
 \leq\frac{\ell}{4\pi}\int_0^\ell|r'|^2ds
 =\frac{\ell^2}{4\pi}.
$$

所用 Wirtinger 不等式可直接由零均值周期函数的 Fourier 展开证明：
每个非零频率 $n$ 的导数平方权重至少为
$(2\pi/\ell)^2$，再应用 Parseval 恒等式即可。
弧长曲线属于周期 $H^1$，故该论证适用；
零速度区间可以删除，不影响长度或面积。

令 $\varepsilon=\operatorname{sgn}\tau$，取

$$
x(t)=R(\cos t-1),\qquad
 y(t)=\varepsilon R\sin t,\qquad 0\leq t\leq2\pi.
$$

其长度为 $2\pi R$，且
$\int_0^{2\pi}x(t)y'(t)\,dt=\varepsilon\pi R^2=\tau$，
故达到 (H1)。最后
$\ell\leq v_{\max}T$ 给出 (H2)；
将圆重新参数化为速度 $v_{\max}$ 即达到等号。

证毕。

这个等号结论以完整平面、双向控制以及指定长度代价为前提。
在有限局部图域中，圆必须完全留在该图域内；
额外漂移、单向门、曲率修正或控制代价改变，
都需要重新验证下界与可达性。
控制几何的标准背景见 [17](#ref-jean)。
长度下界也不自动成为门数、比特复杂度或物理时间下界；
(H2) 展示了加入明确速度标定后才可得到的时间结论。

### 7.5. 近似预测的误差累积

<a id="thm-finite-step-leakage"></a>

**定理 7.10（明确收缩假设下的有限步泄漏界）。**
设 $V_0,\dots,V_N$ 为有限维实 Hilbert 空间，
$T_j:V_j\to V_{j+1}$ 满足 $\|T_j\|\leq1$。
设 $P_j$ 为正交投影，$Q_j=I-P_j$，并假设

$$
\|P_{j+1}T_jQ_j\|\leq\epsilon_j
 \qquad(0\leq j<N).
$$

给定 $\|x_0\|\leq M_0$，定义真实演化及只保留可见部分的预测为

$$
x_{j+1}=T_jx_j,\qquad
 \widehat z_0=P_0x_0,\qquad
 \widehat z_{j+1}=P_{j+1}T_j\widehat z_j.
$$

则

$$
\|P_Nx_N-\widehat z_N\|
       \leq M_0\sum_{j=0}^{N-1}\epsilon_j.
 \tag{E1}
$$

特别地，若 $\epsilon_j\leq\epsilon$，则误差至多
$M_0N\epsilon$。
若最终标量读出为 $\langle O,P_Nx_N\rangle$，还可得到

$$
|\langle O,P_Nx_N-\widehat z_N\rangle|
 \leq\|O\|M_0\sum_j\epsilon_j.
 \tag{E2}
$$

**证明。**

由收缩性，$\|x_j\|\leq M_0$。
令 $e_j=P_jx_j-\widehat z_j$，则 $e_0=0$，并且

$$
e_{j+1}
 =P_{j+1}T_jP_j e_j
      +P_{j+1}T_jQ_jx_j.
$$

这里 $P_je_j=e_j$。正交投影与 $T_j$ 均为收缩，
所以
$\|e_{j+1}\|\leq\|e_j\|+\epsilon_jM_0$。
归纳求和即得 (E1)，再用 Cauchy--Schwarz 得到 (E2)。

证毕。

在 Hilbert--Schmidt 范数下，酉共轭是等距映射，
因而满足本定理的收缩假设。
一般 CPTP 映射则不能未经验证就代入。
例如四维系统上的通道

$$
\Phi(X)=\operatorname{Tr}_B(X)\otimes|0\rangle\langle0|
$$

作用于 $X=A\otimes I_2/2$，其中 $A$ 是非零无迹 Hermitian
二阶矩阵，会把 Hilbert--Schmidt 范数放大 $\sqrt2$ 倍。
通道与 Stinespring 表示的背景见 [15](#ref-watrous)。
如改用迹范数，还须同时验证所采用的摘要投影在该范数下收缩；
不能只更换范数名称而保留未核对的投影假设。

### 7.6. 三种联络及理论接口

本章涉及三个不同的联络对象，需要分别指定。

1. **量子本征态的 Berry 联络。**
   对光滑恒秩谱投影 $P_{\rm eig}$，
   本征子丛上的投影联络为 $P_{\rm eig}d$。
   它连接谱空间、绝热输运及 Berry/Wilczek--Zee holonomy
   [13](#ref-simon)、[14](#ref-wilczek)。

2. **固定读出层的最小相位联络。**
   定理 [7.6](#thm-minimal-phase) 的 $\beta$ 是五模相位
   $T^3$ 主丛上，由指定相位代价选出的联络；
   它的曲率由 $a'(\kappa)$ 决定。

3. **可见或隐藏算符子丛的投影联络。**
   恒秩核丛总可赋予 $Q D$，可见子丛总可赋予 $P D$。
   这些投影联络的存在，不意味着原始门输运保持该子丛；
   后一命题仍须由 $DQ=0$ 核验。

三种联络可以在额外构造下建立关系，但它们的基底、纤维、
结构群和可观察含义均须写明。
本章已经证明的接口是：

$$
\text{恒秩线性读出}
 \ \Longrightarrow\ \text{隐藏核丛}
 \ \Longrightarrow\
 \left[
 \begin{array}{c}
 \text{指定路径预测闭合}\\
 \Longleftrightarrow\ \text{输运保持隐藏核}
 \end{array}
 \right],
$$

以及在全路径条件下的 $DQ=0$ 判据、在额外商 holonomy 条件下的
端点独立性、在明确控制代价下的面积成本下界。
这些结论为项目中的读出、门序列和观察者记忆提供可检验的接口，
而不是以同一词语替代原本不同的数学对象。

<a id="sec-observer"></a>

## 8. 输出解析仪器、预测观察者与受约束量子控制

本章把三种对象放在同一个严格接口中：实际发生的动作和输出记录、由全部允许未来决定的预测商，以及保持 FIB 合法域的量子控制。量子概率规则和可调用的控制菜单均作为显式输入；静态展开只给出协议的等价表示，不另行证明一种物理本体论。本章的有限维闭包论证与仓库的输出解析仪器文稿相接[5](#ref-repo-instrument)。所引两项 Lean 源结果的范围是给定单一 Heisenberg 迭代的全未来统计充分性和最小线性摘要[9](#ref-repo-lean-future)、[10](#ref-repo-lean-minimal)；下面对多动作、多输出和光滑参数族的综合按本章证明承担结论，不将其称为已经整体完成的 Lean 形式化。

### 8.1. 仪器、历史与有限静态展开

<a id="obs-def-instrument"></a>

**定义 8.1（有限仪器与有序历史）。**
固定有限维复 Hilbert 空间 $H\simeq\mathbb C^d$、有限动作集 $A$ 和有限输出集 $O$。记

$$
V=\operatorname{Herm}(H),\qquad
 V_0=\{X\in V:\operatorname{Tr}X=0\},\qquad
 \langle X,Y\rangle=\operatorname{Tr}(XY).
$$

量子态集为 $\mathcal D(H)=\{\rho\in V:\rho\ge0,\operatorname{Tr}\rho=1\}$。动作 $a$ 的仪器是完全正映射族 $\{\Phi_{a,o}\}_{o\in O}$，满足 $\sum_o\Phi_{a,o}$ 保迹。这里完全正映射定义在整个矩阵代数上，并限制到 $V$；仪器的标准操作解释见[15](#ref-watrous)。

对时间顺序写出的历史

$$
h=((a_1,o_1),\ldots,(a_m,o_m)),
$$

定义

$$
\Phi_h=\Phi_{a_m,o_m}\circ\cdots\circ\Phi_{a_1,o_1},
 \qquad \Phi_{\varnothing}=\operatorname{id}.
$$

输入 $\rho$ 时，历史概率为 $p_\rho(h)=\operatorname{Tr}\Phi_h(\rho)$；若该概率严格正，历史后的条件态为

$$
\rho_h=\frac{\Phi_h(\rho)}{p_\rho(h)}.
$$

对末端效果 $0\le G\le I$，联合事件概率为

$$
p_\rho(h,G)=\operatorname{Tr}[G\Phi_h(\rho)]
 =\operatorname{Tr}[\Phi_h^*(G)\rho].
$$

控制策略只能依据已经取得的动作--输出前缀选择下一动作或停止；它不得依据未读出的输入态选择动作。若系统含保留的环境、仪器内部记忆或观察者记忆，$H$ 必须包含使这些更新确为所声明仪器的联合载体；不能未经证明把有记忆的联合演化替换成系统边缘上的独立通道。

经典 $N$ 态模型是这一接口的对角限制：矩阵

$$
M_{a,o}(s,t)=\Pr(o,t\mid s,a)
$$

具有非负条目，且 $\sum_oM_{a,o}$ 行随机。对行概率向量 $p$ 和列效果 $g$，有

$$
p(h,g)=pM_{a_1,o_1}\cdots M_{a_m,o_m}g.
$$

<a id="obs-thm-unrolling"></a>

**定理 8.2（有限协议的静态展开等价）。**
固定定义[8.1](#obs-def-instrument)的仪器。任何具有共同有限深度上界 $T$、确定性终止的反馈协议，都有一棵有限静态历史树，逐输入保持所有叶记录概率以及叶后的未归一化量子态。反过来，任何有限有根树，若每个非叶节点选择一个允许动作、出边分别携带该动作的全部输出分支，便定义一个具有这些统计的合法有限反馈协议。

这里的树是同一协议的数学表示；树上未实际到达的分支不成为观察者已经取得的记录。

**证明。**

从根的空历史出发。若策略在前缀 $h$ 停止，就将 $h$ 记为叶；否则策略指定动作 $a(h)$，为每个 $o\in O$ 添加孩子 $h(a(h),o)$，出边标记为 $\Phi_{a(h),o}$。深度不超过 $T$，输出集有限，故树有限。保留零概率边也合法，它们不需要从未知输入中预先辨认并删除。

对树深归纳。根的未归一化态是 $\rho$。若节点 $h$ 的未归一化态为 $\Phi_h(\rho)$，则孩子的态恰为

$$
\Phi_{a(h),o}(\Phi_h(\rho))
 =\Phi_{h(a(h),o)}(\rho).
$$

其迹就是原协议产生该完整前缀的概率。各孩子迹之和等于父节点迹，因为分支总映射保迹。有限终止使所有叶概率之和为一；在叶后再应用任何已声明效果，联合概率仍由同一迹公式给出。这证明全部所述统计相同。

反向从根执行树中指定动作，取得实际输出后沿相应边前进，在叶停止。每个节点的动作只依赖已取得前缀，因而合法；同一归纳给出相同状态和概率。若另允许输入无关的经典随机种子，可先固定种子作上述展开，再对种子积分。连续种子不必对应一棵有限分支的总树，但所得协议分布仍是这些有限树分布的混合。

证毕。

### 8.2. 全未来效果、最小预测商与常秩丛

<a id="obs-def-closure"></a>

**定义 8.3（输出解析的未来效果闭包）。**
固定有限末端效果族 $\mathcal G\subset V$，其中 $I\in\mathcal G$。定义实线性空间

$$
W_0=\operatorname{span}_{\mathbb R}\mathcal G,
 \qquad
 W_{n+1}=W_n+
 \sum_{a\in A,o\in O}\Phi_{a,o}^*(W_n),
 \qquad
 W_\infty=\bigcup_{n\ge0}W_n.
$$

定义全未来隐方向空间 $N=W_\infty^\perp$。由于 $I\in W_\infty$，有 $N\subseteq V_0$。两态称为未来等价，若

$$
\rho\sim\sigma
 \quad\Longleftrightarrow\quad
 p_\rho(h,G)=p_\sigma(h,G)
 \quad\text{对所有有限历史 }h\text{ 和 }G\in\mathcal G.
$$

本定义保留每个实际输出分支；只保留平均通道 $\sum_o\Phi_{a,o}$ 定义的是另一个通常较弱的观察问题。

<a id="obs-thm-predictive"></a>

**定理 8.4（有限稳定化、全未来等价与最小仿射摘要）。**
令 $r_0=\dim W_0$、$r=\dim W_\infty$。则：

1. 对每个 $n$，

   $$
   W_n=\operatorname{span}_{\mathbb R}
    \{\Phi_h^*(G):|h|\le n,\ G\in\mathcal G\}.
   $$

   且 $W_\infty=W_{d^2-r_0}$。

2. 对任意 $\rho,\sigma\in\mathcal D(H)$，

   $$
   \rho\sim\sigma\quad\Longleftrightarrow\quad \rho-\sigma\in N.
   $$

   此条件也保证任意共同的有限反馈策略有相同的完整输出记录律。

3. 令 $W^0=W_\infty\cap V_0$，以 $\pi:V_0\to W^0$ 表示正交投影。摘要

   $$
   q(\rho)=\pi(\rho-I/d)
   $$

   未来充分，且其物理可达像的仿射维数为 $r-1$。

4. 若某仿射摘要 $s(\rho)=L(\rho-I/d)+b$，其中 $L:V_0\to\mathbb R^k$ 线性，并对全部密度态满足

   $$
   s(\rho)=s(\sigma)\Longrightarrow\rho\sim\sigma,
   $$

   则存在唯一满射线性映射 $F:\operatorname{ran}L\to W^0$，使 $\pi=F\circ L$。特别地，

   $$
   \operatorname{rank}L\ge r-1.
   $$

**证明。**

第一项的词表示对 $n$ 归纳。$n=0$ 时即定义。给一个词效果再作用 $`\Phi_{a,o}^*`$，对应在该历史之前插入动作--输出对 $(a,o)$；所有增加一位的历史都以此方式得到。因此递推恰好张成长度不超过 $n+1$ 的全部词效果。

若某级 $W_{n+1}=W_n$，定义立即给 $`\Phi_{a,o}^*W_n\subseteq W_n`$，对每个分支都成立；于是所有后续级仍等于 $W_n$。若尚未稳定，每级维数至少增加一。由于 $\dim_{\mathbb R}V=d^2$，从维数 $r_0$ 开始，至多 $d^2-r_0$ 次增加便达到稳定。这证明所给统一词长界。

第二项由迹对偶直接得到：全部词概率差为零，当且仅当 $\rho-\sigma$ 与每个词效果正交，当且仅当与它们的线性张成 $W_\infty$ 正交。对固定反馈策略，每个具体输出前缀确定相同动作序列；其概率是上述某个词概率。逐个前缀的概率相同，故整个记录律相同。策略可以在共同前缀处停止，结论仍成立。

因 $I\in W_\infty$，有正交分解

$$
W_\infty=\mathbb R I\mathbin{\oplus^{\perp}}W^0,
 \qquad \dim W^0=r-1.
$$

对迹零差 $X$，$\pi X=0$ 等价于 $X\in N$。这既证明 $q$ 充分，也证明其坐标没有遗漏任何本模型能分辨的方向。$\mathcal D(H)-I/d$ 在 $V_0$ 内含零的开邻域：若 $\|X\|_{\rm op}<1/d$，则 $I/d+X$ 正定。正交投影把这个邻域映到 $W^0$ 中零的一个邻域，故物理摘要像的仿射包络就是 $W^0$，维数为 $r-1$。

最后取 $X\in\ker L$。选择足够小的 $\varepsilon>0$，使 $\rho_\pm=I/d\pm\varepsilon X$ 都是密度态。其摘要相同，所以由假设和第二项，$2\varepsilon X\in N$，从而 $\pi X=0$。因此 $\ker L\subseteq\ker\pi$。定义

$$
F(LX)=\pi X.
$$

若 $LX=LY$，则 $X-Y\in\ker L\subseteq\ker\pi$，故定义与代表元无关。它线性，且对 $Y\in W^0$ 有 $F(LY)=Y$，故满射。任何满足 $\pi=F\circ L$ 的映射都在每个 $LX$ 上被强制为这个值，故唯一。满射给出秩下界。

这里使用了全部密度态含相对开集的事实。若来源只允许一个较小子集，最后的必要性和维数下界须在其实际仿射包络内重新核对。

证毕。

<a id="obs-prop-average"></a>

**命题 8.5（平均更新闭合不足以保持输出未来）。**
即使平均更新保持当前效果空间，也不能推出该空间对完整输出记录未来充分。这个失败已经发生在两个经典状态、一个动作和两个输出上。

**证明。**

取状态 $\{0,1\}$，令

$$
M_0=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
 M_1=\begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
 \mathcal B=\operatorname{span}\{(1,1)^{\mathsf T}\}.
$$

平均更新 $M_0+M_1=I_2$ 保持 $\mathcal B$。当前常数读口不能区分 $p=(1,0)$ 与 $q=(0,1)$，且任意次平均更新后仍不能区分。然而

$$
pM_0\mathbf1=1,\qquad qM_0\mathbf1=0.
$$

实际一次输出就区分这两个来源。原因是 $M_0\mathbf1=(1,0)^{\mathsf T}\notin\mathcal B$；两个分支之和隐藏了分支各自携带的信息。

同一例的量子实现是 $\Phi_o(\rho)=|o\rangle\langle o|\rho|o\rangle\langle o|$。平均 Heisenberg 通道保持 $\operatorname{span}\{I\}$，但单个分支将 $I$ 送到 $|o\rangle\langle o|$。因此问题不是经典模型独有的记号现象。

证毕。

<a id="obs-thm-bundle"></a>

**定理 8.6（常秩预测子丛与正概率后验下降）。**
令 $B$ 为光滑流形，$H,A,O$ 固定。假设每个仪器分支 $\Phi_{a,o,\lambda}$ 的矩阵系数及有限末端效果 $G_{j,\lambda}$ 都光滑依赖 $\lambda\in B$，且末端族始终含 $I$。在每个参数上按定义[8.3](#obs-def-closure)构造 $W_{\infty,\lambda}$。

若其维数在某开域 $U\subseteq B$ 恒为 $r$，则

$$
\mathcal W=\coprod_{\lambda\in U}W_{\infty,\lambda},\qquad
 \mathcal N=\coprod_{\lambda\in U}W_{\infty,\lambda}^{\perp}
$$

分别是平凡实向量丛 $U\times V$ 的光滑秩 $r$ 和 $d^2-r$ 子丛。商丛 $(U\times V)/\mathcal N$ 是线性预测丛；其中物理态像的迹一仿射包络具有秩 $r-1$。

每个参数处、每个输出分支在商上诱导良定义的线性更新。对该分支概率严格正的物理商态，归一化后验更新也良定义。令 $P_\lambda$ 为到 $W_{\infty,\lambda}$ 的正交投影，则

$$
\nabla s=P\,ds,
 \qquad
 F_\nabla=P(dP\wedge dP)P
$$

给出 $\mathcal W$ 上一个度量相容联络及其曲率。该数学联络的物理可实现性不包含在这些假设中。

**证明。**

因为初始效果空间至少含 $I$，定理[8.4](#obs-thm-predictive)给统一上界

$$
W_{\infty,\lambda}=W_{d^2-1,\lambda}.
$$

有限动作、输出、末端族及有限词长使右侧由有限多个光滑词效果张成。将这些效果在固定的 $V$ 正交基中排成列矩阵 $C(\lambda)$。它在 $U$ 上秩恒为 $r$。在任意 $\lambda_0$ 选择一个非零的 $r$ 阶子式；该子式在某邻域仍非零，对应的 $r$ 列在那里构成光滑局部标架。因此 $\mathcal W$ 是光滑子丛。

若局部标架矩阵为 $C_0$，正交投影为

$$
P=C_0(C_0^{\mathsf T}C_0)^{-1}C_0^{\mathsf T}.
$$

故 $P$ 光滑；$I-P$ 的像给光滑正交补子丛 $\mathcal N$。不同局部公式都等于唯一正交投影，所以可以拼接。商丛由正交投影与 $\mathcal W$ 同构。恒等矩阵属于每个纤维，$\mathcal N\subseteq U\times V_0$；减去固定 $I/d$ 后，迹一物理态像的仿射包络与 $\mathcal W\cap(U\times V_0)$ 同构，秩为 $r-1$。

固定参数，若 $X\in N$、$E\in W_\infty$，则

$$
\operatorname{Tr}[\Phi_{a,o}(X)E]
 =\operatorname{Tr}[X\Phi_{a,o}^*(E)]=0,
$$

因为闭包已对每个 $`\Phi_{a,o}^*`$ 不变。因此 $\Phi_{a,o}N\subseteq N$，商映射

$$
\overline\Phi_{a,o}([X])=[\Phi_{a,o}(X)]
$$

良定义。迹也在商上良定义，因为 $N$ 中元素迹零。若 $[\rho]=[\sigma]$，它们对该分支有同一个概率

$$
p=\operatorname{Tr}\Phi_{a,o}(\rho)
   =\operatorname{Tr}\Phi_{a,o}(\sigma).
$$

当 $p>0$ 时，后验差为 $\Phi_{a,o}(\rho-\sigma)/p\in N$，所以归一化后验仍属同一商类；当 $p=0$ 时，该事件在该输入上不发生，本定理不定义条件后验。

对 $\mathcal W$ 的截面 $s$ 有 $Ps=s$。$\nabla s=Pds$ 满足 Leibniz 规则，并且对任意截面 $s,t$，

$$
d\langle s,t\rangle
 =\langle Pds,t\rangle+\langle s,Pdt\rangle,
$$

故度量相容。微分 $P^2=P$ 得 $PdPP=0$。于是

$$
\nabla^2s=P\,dP\wedge ds
 =P\,dP\wedge dP\,s
 =P(dP\wedge dP)Ps,
$$

即所给曲率公式。构造只用统计效果空间和 Hilbert--Schmidt 度量；没有给出沿参数路径驱动实际系统的 Hamiltonian，因而不能把该投影联络的平行运输直接宣告为可调用量子门。

证毕。

<a id="obs-prop-growth"></a>

**命题 8.7（菜单增长的预测正合列）。**
在同一 $H$ 上，扩张动作--输出菜单或末端效果族而保留旧菜单，产生 $W_{\rm old}\subseteq W_{\rm new}$。令 $N_i=W_i^\perp\subseteq V_0$，$Q_i=V_0/N_i$。则有短正合列

$$
0\longrightarrow N_{\rm old}/N_{\rm new}
 \longrightarrow Q_{\rm new}
 \longrightarrow Q_{\rm old}\longrightarrow0,
$$

且

$$
\dim Q_i=\dim W_i-1,
 \qquad
 \dim\ker(Q_{\rm new}\to Q_{\rm old})
 =\dim W_{\rm new}-\dim W_{\rm old}.
$$

若这些空间属于定理[8.6](#obs-thm-bundle)中的共同光滑恒秩域，则该序列是光滑向量丛的短正合列。

**证明。**

旧菜单的每个历史仍是新菜单历史，故旧词效果张成空间包含于新空间。正交补反向包含，$N_{\rm new}\subseteq N_{\rm old}$。定义中间到右端的映射为 $[X]_{N_{\rm new}}\mapsto[X]_{N_{\rm old}}$；它良定义且满射。其核恰为 $X\in N_{\rm old}$ 的那些类，即 $N_{\rm old}/N_{\rm new}$。左端嵌入由同一个代表元给出且单射，故正合。

$\dim V_0=d^2-1$、$\dim N_i=d^2-\dim W_i$，相减即得维数公式。光滑常秩时，包含、商和正交投影在局部标架中都是光滑线性映射，上述逐纤维正合关系给丛的正合列。

因此新增预测维数恰好计数此前隐藏、现在可见的独立线性方向。这个数不是自动的 Shannon 信息增量，也不是量子 Hilbert 维数。跨越秩变化的位置时须保留分层或滤过描述，不能将秩增长解释为同一个固定秩丛内的酉旋转。

证毕。

### 8.3. 可观测性与量子压缩的区别

<a id="obs-thm-orbit"></a>

**定理 8.8（全酉探针轨道与不可压缩性的独立性）。**
设 $d\ge2$，$P$ 是秩 $k$ 的正交投影，$1\le k<d$。若实际菜单允许任意 $U\in U(d)$ 后测量二值效果 $P$，则效果族

$$
\{U^\dagger P U:U\in U(d)\}
$$

实线性张成整个 $V$，从而其统计区分全部密度态。

反过来，预测效果空间维数小于 $d^2$，并不保证能用一个共同 CPTP 通道删除其隐藏方向。具体地，在量子位上取

$$
W=\operatorname{span}_{\mathbb R}\{I,X,Z\}.
$$

虽然 $W^\perp=\mathbb R Y$ 非零，任何对全部输入精确保留 $X,Z$ 期望的 CPTP 通道都必为恒等通道。因此该读出商不能由一个非平凡的统一 CPTP 遗忘操作实现。

**证明。**

先证明轨道张成。若 $D\in V$ 与所有 $U^\dagger P U$ 正交，将 $D$ 对角化，特征值记为 $\lambda_1,\ldots,\lambda_d$。轨道恰包含所有秩 $k$ 正交投影，特别地包含每个由 $k$ 个该特征向量张成的子空间的投影。因此对每个大小为 $k$ 的指标集合 $J$，

$$
\sum_{j\in J}\lambda_j=0.
$$

给定 $i\ne j$，可在其余 $d-2$ 个指标中选择大小 $k-1$ 的集合 $T$。比较 $T\cup\{i\}$ 与 $T\cup\{j\}$，得 $\lambda_i=\lambda_j$。全部特征值相等，再由一个 $k$ 项和为零得全部为零。因此正交补为零，轨道张成 $V$。概率分离由迹对偶得到。这里任意酉的可调用性是本命题的假设，不由探针的存在提供。

再证明量子位例。设 $\mathcal T(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^\dagger$ 是该 CPTP 通道。保留 $Z$ 期望使输入 $|0\rangle\langle0|$ 的输出具有 $Z$ 期望一，只能仍为 $|0\rangle\langle0|$；同理 $|1\rangle\langle1|$ 被固定。正半定秩一输出的 Kraus 求和迫使每个向量 $K_\alpha|0\rangle$ 平行于 $|0\rangle$，每个 $K_\alpha|1\rangle$ 平行于 $|1\rangle$。故

$$
K_\alpha=\operatorname{diag}(a_\alpha,b_\alpha).
$$

保留 $X$ 期望又使 $|+\rangle\langle+|$ 被固定。同样的秩一理由给 $K_\alpha|+\rangle$ 平行于 $|+\rangle$，所以 $a_\alpha=b_\alpha$。于是每个 $K_\alpha=a_\alpha I$，保迹条件给 $\sum_\alpha|a_\alpha|^2=1$，从而 $\mathcal T=\operatorname{id}$。

若再要求通过较小 Hilbert 空间编码再解码，则恒等通道还强制载体维数不减。事实上，若 $\mathcal D\circ\mathcal E=\operatorname{id}_d$ 且中间维数为 $q$，组合 Kraus 算子 $D_\beta E_\alpha$ 每个秩至多 $q$。恒等通道的任意 Kraus 算子必为恒等矩阵的标量倍数：它须把每个纯态射线送回自身，再比较基向量及其两两和即可得标量性。至少一个组合 Kraus 算子非零，因而秩为 $d$，所以 $q\ge d$。这说明线性预测坐标的减少与物理量子存储压缩是不同的定理问题。

证毕。

### 8.4. 五模式基础门、张量接缝与精确逻辑控制

以下结论将具体受约束门的合同写出；它们对应仓库 $\Omega$ 卷的五模式、交替编码和保码端点控制章节[4](#ref-repo-omega)。所有控制角均是已供应的理想实参数；其取得、数字表示与物理实现成本不从矩阵等式中产生。这里的连续实参数脉冲菜单与前面有限动作集的仪器合同不同。定理[8.6](#obs-thm-bundle)使用有限动作和有限词长取得有限列的光滑矩阵；若要对完整连续菜单使用该丛结论，须另外给出适用的光滑生成族及常秩论证，不能把连续参数标签当成已经列出的有限动作。

<a id="obs-prop-pxp"></a>

**命题 8.9（合法 PXP 控制与跨窗张量守卫）。**
在三物理位空间中取

$$
\Sigma_F=\{000,100,010,001,101\},\qquad
 H_F=\operatorname{span}_{\mathbb C}\{|s\rangle:s\in\Sigma_F\}.
$$

令 $P_j^0=|0\rangle\langle0|_j$，并令 $X_j$ 翻转第 $j$ 位。则

$$
G_1=X_1P_2^0,\qquad
 G_2=P_1^0X_2P_3^0,\qquad
 G_3=P_2^0X_3
$$

均保持 $H_F$，并与其正交投影交换。故限制 $H_j=G_j|_{H_F}$ 的指数 $e^{-itH_j}$ 对全部合法相干输入都无非法域泄漏。

两个直接相邻三位窗口的合法联合空间维数是 $21$，因而不能直接等同于 $H_F\otimes H_F$ 的 $25$ 维空间。在两块之间插入并初始化一个零分隔位，则映射

$$
|s\rangle\otimes|t\rangle\longmapsto|s\,0\,t\rangle
$$

是到合法七位空间的等距嵌入。一般地，$m$ 个三位块以 $m-1$ 个零分隔，给 $H_F^{\otimes m}$ 到合法长度 $4m-1$ 空间的等距嵌入。

**证明。**

合法词的条件是没有相邻 $11$。$G_1$ 仅在中位为零时翻转第一位，故不会制造第一、二位的 $11$；$G_3$ 同理。$G_2$ 仅在两端均为零时翻转中位，因此也保持合法性。每个 $G_j$ 是 Hermitian，所以保持子空间也保持其正交补，等价于与其正交投影交换。幂级数或有限维谱分解于是给出指数的保持性；不需要预先测量相邻位。

在两个各自合法的三位字拼接时，唯一新增的非法条件是左块末位和右块首位同时为一。左块末位为一的选择是 $001,101$，右块首位为一的选择是 $100,101$，恰有四对。因此合法拼接数是 $5\cdot5-4=21$。插入零后，接缝两侧不可能形成 $11$；不同块基向量的像仍是不同的正交计算基向量，所以给等距嵌入。逐接缝应用同一论证即得 $m$ 块结论。此嵌入所用的已知零是编码资源，不是从未知输入免费取得的测量结果。

证毕。

<a id="obs-prop-phase"></a>

**命题 8.10（混合差分的纠缠相位判据）。**
固定编码

$$
\iota:\mathbb C^2\otimes\mathbb C^2\longrightarrow H_F,
 \qquad \iota|ab\rangle=|a0b\rangle,
 \qquad \mathcal C=\operatorname{ran}\iota.
$$

对实函数 $f:\Sigma_F\to\mathbb R$，定义

$$
J_f=f(101)-f(100)-f(001)+f(000).
$$

若实际另行供应相位门 $U_{\theta,f}|ab\rangle=e^{i\theta f(a0b)}|ab\rangle$，则它是两个单逻辑位酉门的张量积，当且仅当

$$
\theta J_f=0\pmod{2\pi}.
$$

若此条件不成立，它将 $|++\rangle$ 变为 Schmidt 秩二的态。特别地，物理固定门

$$
S_\star=\exp\!\left(\frac{i\pi}{2}n_1n_3\right),
 \qquad n_j=I-P_j^0,
$$

在编码上的限制是 $S=\operatorname{diag}(1,1,1,i)$，且 $S^2=CZ$。

**证明。**

记 $f_{ab}=f(a0b)$。四点上的函数唯一写成

$$
f_{ab}=f_{00}+(f_{10}-f_{00})a+(f_{01}-f_{00})b+J_fab.
$$

前面三项产生整体相位和单体对角相位；剩下的非局部因子是 $\operatorname{diag}(1,1,1,e^{i\theta J_f})$。若 $\theta J_f$ 为 $2\pi$ 整数倍，剩余因子为恒等，故可分。

反过来，$U_{\theta,f}|++\rangle$ 的 $2\times2$ 系数矩阵为 $\frac12(e^{i\theta f_{ab}})_{a,b}$，其行列式为

$$
\frac{e^{i\theta(f_{01}+f_{10})}}4
 \bigl(e^{i\theta J_f}-1\bigr).
$$

两比特纯态可分当且仅当这个系数矩阵秩一，即行列式为零。若 $U_{\theta,f}$ 是单体门张量积，它必须把乘积态 $|++\rangle$ 送为乘积态，所以该行列式必须为零。由此得到充要条件及 Schmidt 秩结论。最后 $n_1n_3$ 在 $|a0b\rangle$ 上的本征值为 $ab$，直接给 $S$ 与 $S^2$。

特别地，$J_f\ne0$ 并不单独保证纠缠：例如 $f(a0b)=4ab$、$\theta=\pi/2$ 时相位门为恒等。读出函数的存在也不供应相应相位门；本命题明确以其可调用性为前提。

证毕。

<a id="obs-thm-universal"></a>

**定理 8.11（每个前缀保码的精确双逻辑位通道）。**
在命题[8.10](#obs-prop-phase)的固定编码上，假设独立提供任意实参数端点脉冲

$$
R_1(t)=e^{-itH_1},\qquad R_3(t)=e^{-itH_3},
$$

以及同址可重复调用的固定门 $S_\star$。除此之外不需要调用中位控制 $H_2$。则对每个 $U\in U(4)$，存在一个与未知输入无关的有限字 $W$ 和实数 $\gamma$，使

$$
W\iota=e^{i\gamma}\iota U.
$$

每个原语前缀及脉冲中途都保持 $\mathcal C$，并固定 $\mathbb C|010\rangle$。因此对任意有限维被动参考 $R$ 和任意 $\rho\in\mathcal D(\mathbb C^4\otimes R)$，该字实现与 $U\otimes I_R$ 完全相同的编码通道。

**证明。**

在编码中中位始终为零，所以

$$
\iota^\dagger R_1(t)\iota=e^{-itX\otimes I},\qquad
 \iota^\dagger R_3(t)\iota=e^{-itI\otimes X}.
$$

两个生成元在 $|010\rangle$ 上为零，固定相位在该态上也为一。因此这些原语对于所有参数和脉冲中间时刻都保码并固定辅助方向；有限组合保留这些性质。

以下矩阵字按右因子先作用。令 $X_1=X\otimes I$、$X_2=I\otimes X$。由于 $R_3(\pi/2)$ 在码上为 $-iX_2$、$R_3(-\pi/2)$ 为 $iX_2$，有

$$
R_3(-\pi/2)S_\star R_3(\pi/2)S_\star
 \ \longmapsto\ X_2SX_2S
 =D_1:=\operatorname{diag}(1,1,i,i).
$$

交换两端同样得到 $D_2=\operatorname{diag}(1,i,1,i)$。每个 $D_j$ 是相应逻辑位上的单体相位 $\operatorname{diag}(1,i)$。$S_\star^{-1}=S_\star^3$，所以这些字的逆也可用有限字实现。

单体矩阵 $D=\operatorname{diag}(1,i)$ 满足 $DXD^\dagger=Y$；共轭端点脉冲便得到任意角度的单体 $Y$ 旋转。为明确其充分性，任意 $V\in SU(2)$ 可唯一写为

$$
V=a_0I-i(a_xX+a_yY+a_zZ),\qquad
 a_0^2+a_x^2+a_y^2+a_z^2=1,
$$

其中各系数为实数。直接相乘给

$$
\begin{aligned}
e^{-i\alpha X}e^{-i\beta Y}e^{-i\eta X}
 ={}&\cos\beta\cos(\alpha+\eta)I\\
 &-i\bigl(\cos\beta\sin(\alpha+\eta)X
 +\sin\beta\cos(\alpha-\eta)Y
 +\sin\beta\sin(\alpha-\eta)Z\bigr).
\end{aligned}
$$

选择 $\cos\beta=\sqrt{a_0^2+a_x^2}$、$\sin\beta=\sqrt{a_y^2+a_z^2}$，再选 $\alpha+\eta$ 和 $\alpha-\eta$ 为相应二维向量的极角，即得到 $V$；长度为零的二维向量可任取极角。因此任意单逻辑位 $SU(2)$ 门均可精确有限实现。

由命题[8.10](#obs-prop-phase)取得 $CZ=S^2$。令 $H_2^{\rm Had}=2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$，则 $iH_2^{\rm Had}\in SU(2)$，而

$$
(I\otimes iH_2^{\rm Had})CZ(I\otimes(iH_2^{\rm Had})^\dagger)=CNOT.
$$

标准局部门加 CNOT 的精确有限分解也给出相同的通用性结论[16](#ref-barenco)。这里再给出一个只需有限维逆函数定理的精确达到证明，避免把 Lie 代数生成仅解释为稠密逼近。

直接共轭计算给

$$
CZ(X\otimes I)CZ=X\otimes Z,
$$

因此已经取得连续一参数群 $\exp(-itX\otimes Z)$。用两端的单体 $SU(2)$ 共轭，可以将 $X$ 和 $Z$ 分别送到任意 Pauli 轴，从而取得全部九个群

$$
\exp(-it\sigma_a\otimes\sigma_b),\qquad
 a,b\in\{x,y,z\},\quad t\in\mathbb R.
$$

加上六个单体 Pauli 一参数群，得到十五个无迹 Hermitian 矩阵 $B_1,\ldots,B_{15}$。Pauli 矩阵的迹正交关系使这些矩阵线性独立；无迹 Hermitian 四阶矩阵空间维数为 $4^2-1=15$，所以 $-iB_j$ 构成 $\mathfrak{su}(4)$ 的实基。

考察光滑乘积映射

$$
F:\mathbb R^{15}\longrightarrow SU(4),\qquad
 F(t_1,\ldots,t_{15})=e^{-it_{15}B_{15}}\cdots e^{-it_1B_1}.
$$

在零点的导数是 $v\mapsto-i\sum_jv_jB_j$，为切空间同构。逆函数定理给出：$F$ 的像包含恒等矩阵的一个开邻域。由这些一参数群的有限乘积组成的子群因而是 $SU(4)$ 的开子群；其每个陪集也开，故它同时为闭集。

$SU(4)$ 连通可以直接看出：对任意 $V\in SU(4)$，谱分解写成 $V=Q\operatorname{diag}(e^{i\theta_j})Q^\dagger$。行列式条件使 $\sum_j\theta_j$ 为 $2\pi$ 整数倍；从其中一个角减去该整数倍，可保持全部本征值而使角和为零。于是 $V=e^{iH}$，其中 $H$ 无迹 Hermitian，路径 $t\mapsto e^{itH}$ 全在 $SU(4)$ 中连接 $I$ 与 $V$。所以包含单位邻域的上述子群就是全部 $SU(4)$。这证明每个 $SU(4)$ 元素都有实际有限字，而不仅属于字集合的闭包。

最后任意 $U\in U(4)$ 都可乘一个标量 $e^{i\gamma}$ 变成行列式一的矩阵，故已得有限字实现 $e^{i\gamma}U$。所有共轭、逆和乘积均使用同一保码原语；逆由反向实参数脉冲以及 $S_\star^{-1}=S_\star^3$ 实现。

全部构件来自已证明保码的原语，故每个原语前缀和脉冲中途保码。对参考系统张量恒等后仍有 $W\iota\otimes I_R=e^{i\gamma}(\iota U\otimes I_R)$；密度态共轭使标量消去，得到完全相同的联合通道。

该结论是编码上的通道通用性。由于所有字固定 $|010\rangle$，它并未给出任意五维酉算子，也未给出逻辑子空间相对辅助方向的任意标量相位。上述精确有限存在性与实际参数、总持续时间和数字编译的成本仍是不同问题。

证毕。

### 8.5. 一般精确目标的脉冲维数下界

<a id="obs-thm-pulse"></a>

**定理 8.12（一般全链精确目标不能由少量实参数脉冲覆盖）。**
令 $\ell\ge3$，$\mathcal K_\ell$ 是长度 $\ell$、无相邻 $11$ 的合法链空间。其维数为 $d=F_{\ell+2}$，约定 $F_0=0,F_1=1$。提供独立控制

$$
H_j=\left.P_{j-1}^0X_jP_{j+1}^0\right|_{\mathcal K_\ell},
 \qquad P_0^0=P_{\ell+1}^0=I,
$$

的任意实参数脉冲 $P_j(t)=e^{-itH_j}$，及固定门 $S_\star=\exp(i\pi n_1n_3/2)$。令 $c([U])$ 为精确实现射影酉通道 $[U]\in PU(d)$ 所需的最少可调脉冲数；任意有限次固定门调用不计入此成本，不可达时取 $\infty$。则 Haar 几乎处处有

$$
c([U])\ge d^2-1=F_{\ell+2}^2-1.
$$

若另有该菜单的全部射影酉精确有限可达性，则几乎处处进一步有 $d^2-1\le c([U])<\infty$。

**证明。**

合法字按末位为零或一分解，计数满足 $d_0=1,d_1=2$、$d_\ell=d_{\ell-1}+d_{\ell-2}$，所以 $d_\ell=F_{\ell+2}$。每个 $H_j$ 是互不相交的二态交换块和零块之直和，故谱含于 $\{-1,0,1\}$，从而 $P_j(t+2\pi)=P_j(t)$。另有 $S_\star^4=I$。

固定脉冲数 $m$。合并相邻固定门后，每个相应字可写为

$$
S_\star^{a_0}P_{j_1}(t_1)S_\star^{a_1}\cdots
 P_{j_m}(t_m)S_\star^{a_m},
 \qquad a_i\in\{0,1,2,3\},\quad 1\le j_i\le\ell.
$$

离散模板数至多 $4^{m+1}\ell^m$。每个模板给光滑映射

$$
f:\mathbb T^m\longrightarrow PU(d),
$$

目标 Lie 群的实维数是 $D=d^2-1$。

当 $m<D$ 时，其像 Haar 零测。为直接证明，给紧流形 $\mathbb T^m$ 与 $PU(d)$ 选 Riemann 度量；$f$ 的微分在紧域上有界，故 $f$ 为 Lipschitz。对充分小的 $\delta$，域可由至多 $C\delta^{-m}$ 个半径 $\delta$ 的球覆盖，其像可由同样数量、半径至多 $C'\delta$ 的目标球覆盖。目标小球体积一致地至多 $C''\delta^D$，所以像的体积外测度至多

$$
C'''\delta^{D-m}\longrightarrow0.
$$

取 $m=0,\ldots,D-1$ 的所有有限模板之并，仍为零测。这正是所有可用少于 $D$ 个可调脉冲精确实现的通道集合。补集上的成本至少 $D$，包括成本为 $\infty$ 的情形；若另已证明全部可达，则可去掉无穷可能性。

因此一般全链精确目标的脉冲下界随链长为 $\Theta(\varphi^{2\ell})$。本定理的目标空间是全部 $PU(d)$；一般目标的完整矩阵描述本身具有 $d^2$ 级别的大小。它既不是 SAT 的时间下界，也不是固定误差近似综合的下界，更不排除某些简洁描述的特殊门族具有短实现。它只说明把每个实参数原语记为一个内生 tick，并不能使所有目标相对于链长自动具有多项式长度。

证毕。

这些结果给出本章的精确观察者接口：实际记录由逐输出仪器产生，预测状态由全词效果空间确定，光滑恒秩部分构成向量丛，扩张菜单产生预测商的正合关系，FIB 约束门在声明编码与控制权限下执行逻辑运算。有限可达性、可观察性、物理存储、一般目标综合成本分别由不同命题承担；其中任一项都不替代另外几项。

<a id="sec-endogenous"></a>

## 9. 内生观察者：记忆、反馈与等距实现

预测商给出“足够记住什么”，但尚未给出一台具有内部记忆的观察者。
本章把有限反馈规则实现为联合系统中的明确动力学。
标准量子仪器允许有限 Kraus 表示[15](#ref-watrous)；下面的证明直接使用所供给的 Kraus 矩阵。

<a id="def-internal-observer"></a>

**定义 9.1（有限内部观察者）。**
一个有限内部观察者由有限记忆集合 $\mathsf M$、
动作选择 $a:\mathsf M\to A$ 和记忆更新
$\delta:\mathsf M\times O\to\mathsf M$ 组成。
其初始记忆是给定分布或给定基态，动作由当前实际记忆决定。
对每个动作--输出给定矩阵 $K_{a,o,\alpha}$，满足

$$
\Phi_{a,o}(\rho)=\sum_\alpha K_{a,o,\alpha}\rho K_{a,o,\alpha}^\dagger,
 \qquad \sum_{o,\alpha}K_{a,o,\alpha}^\dagger K_{a,o,\alpha}=I.
$$

对指定有限时域，记忆可以存储整个实际历史前缀，
也可以存储经过证明足够的较小记录。
若策略还依赖步数，便把步数寄存器并入 $\mathsf M$。

<a id="thm-observer-isometry"></a>

**定理 9.2（有限反馈的内生等距实现）。**
令 $H_{\mathsf M}$ 有正交基 $|m\rangle$。另取环境空间，
其正交基包含所有实际使用的 $|m,o,\alpha\rangle$。
定义

$$
V(|m\rangle\otimes\psi)
 =\sum_{o,\alpha}
 |\delta(m,o)\rangle\otimes K_{a(m),o,\alpha}\psi
       \otimes|m,o,\alpha\rangle .
$$

则 $V:H_{\mathsf M}\otimes H\to H_{\mathsf M}\otimes H\otimes E$
是等距映射，且可通过有限辅助空间上的酉门、随后按需读取或舍弃环境来实现。
对输入记忆基态 $m$，输出指针的 $o$ 分布、
系统条件更新和新记忆分别恰为原仪器、$\Phi_{a(m),o}$ 和 $\delta(m,o)$。
有限多步迭代重现全部反馈历史概率。

**证明。**

若 $m\ne n$，输出环境的第一标签不同，各项内积均为零。
若记忆相同，则对任意 $\psi,\varphi$，

$$
\langle V(m,\psi),V(m,\varphi)\rangle
 =\sum_{o,\alpha}
 \langle\psi,K_{a(m),o,\alpha}^{\dagger}K_{a(m),o,\alpha}\varphi\rangle
 =\langle\psi,\varphi\rangle.
$$

故 $V^\dagger V=I$。
将输入空间识别为大空间中
$H_{\mathsf M}\otimes H\otimes|e_0\rangle$ 的子空间。
等距映射把它的任一正交基送到一组正交向量；
将输入与输出这两组向量各自补全为大空间正交基，并逐一对应，
得到实现 $V$ 的酉算符。

对记忆基态输入，读取环境中 $o$ 指针并迹掉其余标签，
得到未归一化系统--记忆态

$$
|\delta(m,o)\rangle\langle\delta(m,o)|
 \otimes \Phi_{a(m),o}(\rho).
$$

其迹是原分支概率，除以非零迹得到原条件态。
各步使用明确供给的新环境寄存器，按步数归纳即得到任意有限历史的同一分支复合。

证毕。

这个构造说明观察者可以在同一联合动力学内实现。
旧记忆在更新时进入环境标签，有限终止历史可通过有限资源表示。
它不证明给定观察者拥有无限记录，也不把环境复位的成本消去。
若初始记忆有量子相干，上述等距扩张仍良定义，
但舍弃标签后的行为不再是“免费保留全部记忆相干”的额外承诺。

<a id="prop-no-free-label"></a>

**命题 9.3（无扰标签提取的精确限制）。**
设 $V$ 是固定等距映射，并对一族归一化纯态满足

$$
V|\psi\rangle=|\psi\rangle\otimes|r_\psi\rangle .
$$

若 $\langle\psi,\varphi\rangle\ne0$，则
$|r_\psi\rangle=|r_\varphi\rangle$。
如果允许的输入是整个纯态空间，则所有 $r_\psi$ 相同。
因而同一个固定等距过程不能保持所有输入态不变，
同时把它们不同的状态标签写入内部记录。

**证明。**

保持内积给出

$$
\langle\psi,\varphi\rangle
 =\langle\psi,\varphi\rangle\langle r_\psi,r_\varphi\rangle.
$$

左侧非零时，后一个内积必须为一；归一化使两记录向量相等。
任意两个正交态均与它们的归一化和非正交，
因此通过这一个中间态也得到记录相等。
非正交态的情形已经直接证明，所以整个纯态空间上记录恒定。

证毕。

这正是本理论把反馈建立在实际输出而非未知输入标签上的原因。
下章的双拷贝读出明确要求来源可独立重复制备；
不会由一个未知输入自动供给第二份。

<a id="sec-learning"></a>

## 10. 关系学习：不变量、可测损失与稳定性

本章沿用几何章的 $b=(X,Y,Z)$、$r=1-Z$、$\nu$、
$\kappa$、$\chi$ 与正概率域。仓库辛完成卷与白盒学习卷已讨论
均值训练和关系不变量[2](#ref-repo-sp)、[6](#ref-repo-learning)。
这里给出精确可微版本以及两拷贝读出与局部稳定性证明。
以下“梯度流”首先是参数优化动力学；
是否由某个物理仪器逐步实现，仍是另一个操作合同。

<a id="thm-gradient-invariant"></a>

**定理 10.1（只用占位均值的自然梯度保留隐关系）。**
定义

$$
\tau(p)=\log\frac{p_0p_{13}}{p_1p_3},
 \qquad
 \zeta(\psi)=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}
             =e^{\tau/2-i\chi}.
$$

设 $\ell(X,Y,Z)$ 光滑，
$L(p)=\ell(X(p),Y(p),Z(p))$。
在概率单纯形上采用 Fisher 度量
$g_F(u,v)=\sum_su_sv_s/p_s$。
其负梯度流保持 $\tau$。
更具体地，令

$$
a_s=\ell_Xx_s+\ell_Yy_s+\ell_Zz_s,\qquad
 \bar a=\sum_sp_sa_s.
$$

则流方程及其保持不变量的指数更新分别为

$$
\dot p_s=-p_s(a_s-\bar a),\qquad
 p_s^+=\frac{p_s e^{-\epsilon a_s}}
                  {\sum_t p_t e^{-\epsilon a_t}}.
$$

指数更新中各 $a_s$ 在该一步开始处取值，$\epsilon$ 为任意有限实数。

在射影空间上，同一均值损失的负 FS 梯度

$$
\dot\psi=-(K-\langle K\rangle)\psi,\qquad
 K=\ell_XN_x+\ell_YN_y+\ell_ZN_z
$$

保持完整复关系 $\zeta$。规范化虚时间一步
$\psi^+=e^{-\epsilon K}\psi/\|e^{-\epsilon K}\psi\|$
也精确保留它。

**证明。**

对任意满足 $\sum_su_s=0$ 的概率切向量，
$dL(u)=\sum_sa_su_s$。向量 $p_s(a_s-\bar a)$ 的分量和为零，
且与 $u$ 的 Fisher 内积为 $\sum_s(a_s-\bar a)u_s=dL(u)$，
所以它正是梯度。
由仿射关系

$$
\sum_s\nu_s=0,\qquad
 \sum_s\nu_sx_s=\sum_s\nu_sy_s=\sum_s\nu_sz_s=0
$$

得到

$$
\frac{d\tau}{dt}=\sum_s\nu_s\frac{\dot p_s}{p_s}
 =-\sum_s\nu_sa_s+\bar a\sum_s\nu_s=0.
$$

指数更新取对数后，新增项只有 $-\epsilon a_s$ 和公共归一化常数；
它们与 $\nu$ 的收缩也为零，所以有限步同样保持 $\tau$。

在归一化射影水平切空间上，当前尺度的 FS 度量为
$2\operatorname{Re}\langle\cdot,\cdot\rangle$，
而均值损失的微分为
$2\operatorname{Re}\langle\,\cdot\,,K\psi\rangle$。
减去径向分量即给出所列梯度。
在所有分量非零的局部图中，

$$
\frac{d}{dt}\log\zeta
 =\sum_s\nu_s\frac{\dot\psi_s}{\psi_s}
 =-\sum_s\nu_s(a_s-\bar a)=0.
$$

对有限步则有
$\zeta(\psi^+)=e^{-\epsilon\sum_s\nu_sa_s}\zeta(\psi)=\zeta(\psi)$；
共同归一化因子消去。

证毕。

本定理陈述的是明确度量与更新规则下的不变量。
在本文规范下，FS 流诱导的概率速度是 Fisher 负梯度速度的两倍；
两条概率轨迹只差这个时间尺度，相同的有限步参数并不代表同一步算法。
改用任意欧氏参数化、带噪估计或额外正则项时，必须重算更新；
“损失只看均值”本身并不对所有可能优化器保证上述守恒。
守恒也不意味着 Fisher 或 FS 的 Riemann 曲率为零。

<a id="thm-relation-loss"></a>

**定理 10.2（关系损失的两拷贝测量与局部稳定）。**
令

$$
h(\psi)=|\psi_0\psi_{13}-\psi_1\psi_3|^2,
\quad
 |\Omega\rangle=
 \frac{|0,13\rangle+|13,0\rangle-|1,3\rangle-|3,1\rangle}{2}.
$$

若来源可独立制备两份相同纯态 $\rho=|\psi\rangle\langle\psi|$，
则 $|\Omega\rangle$ 归一化，且

$$
h(\psi)=\operatorname{Tr}\bigl[|\Omega\rangle\langle\Omega|
                                  (\rho\otimes\rho)\bigr].
$$

因此 $h$ 是这个明确双拷贝二元测量的成功概率。

固定 $0<Z<1$、$0<X,Y<r$。在关系商正域中，

$$
h=A(\kappa)^2+B(\kappa)^2-2A(\kappa)B(\kappa)\cos\chi,
\quad
 A=\sqrt{p_0p_{13}},\quad B=\sqrt{p_1p_3}.
$$

它唯一的零点为
$`\kappa_*={XY}/{r}`$、$\chi=0\bmod2\pi$。
记

$$
I_*=\left.\left(\frac1{p_0}+\frac1{p_1}
                        +\frac1{p_3}+\frac1{p_{13}}\right)\right|_{\kappa_*}.
$$

在 $`u=\kappa-\kappa_*`$ 和 $\chi$ 的局部实坐标中，

$$
h=\frac r2\left(\frac{I_*}{2}u^2+
                         \frac2{I_*}\chi^2\right)
       +O\bigl((|u|+|\chi|)^3\bigr).
$$

负关系商梯度流

$$
\dot\kappa=-\frac2I\,\partial_\kappa h,\qquad
 \dot\chi=-\frac I2\,\partial_\chi h
$$

使 $h$ 单调不增，其零点局部指数稳定，线性化为 $-rI_2$。
精确地，对任意 $0<\gamma<r$，存在足够小邻域，
其中初值满足
$\|(u(t),\chi(t))\|\le e^{-\gamma t}\|(u(0),\chi(0))\|$。

**证明。**

$\Omega$ 的四个基向量互相正交，故范数为一。
直接计算
$\langle\Omega|\psi\otimes\psi\rangle
=\psi_0\psi_{13}-\psi_1\psi_3$，得到测量公式。
代入相位表达得到 $h$ 的余弦形式。

正域中 $A,B>0$，所以 $h=(A-B)^2+2AB(1-\cos\chi)$
恰在 $A=B$ 且 $\chi=0\bmod2\pi$ 时为零。
概率反演给出

$$
A^2-B^2
 =\kappa(r-X-Y+\kappa)-(X-\kappa)(Y-\kappa)
 =r\kappa-XY.
$$

于是唯一零点为所列值，且它严格位于兼容区间内部。
在该点写 $`A=B=b_*>0`$，则

$$
b_*^2=\frac{XY(r-X)(r-Y)}{r^2},
 \qquad I_*=\frac r{b_*^2}.
$$

由 $A-B=(ru)/(A+B)$ 得
$`(A-B)^2=r^2u^2/(4b_*^2)+O(u^3)`$；
又有 $`2AB(1-\cos\chi)=b_*^2\chi^2+O((|u|+|\chi|)^3)`$。
代入 $`I_*`$ 即得二次展开。

流是所列正定商度量下的负梯度，所以

$$
\dot h=-\frac2I(\partial_\kappa h)^2
        -\frac I2(\partial_\chi h)^2\le0.
$$

在零点，Hessian 恰为 $r$ 乘以度量矩阵，
故向量场线性化为 $-rI_2$。
写 $z=(u,\chi)$，则 $\dot z=-rz+R(z)$，
其中 $|R(z)|\le(r-\gamma)|z|$ 在充分小闭球内成立。
所以 $\frac d{dt}|z|^2\le-2\gamma|z|^2$。
球面上的向内性保证解留在该球中，积分不等式给出所述指数界。

证毕。

<a id="prop-hamilton-loss"></a>

**命题 10.3（同一关系能量的 Hamilton 流与相位门）。**
在 $\omega_{\rm red}=d\chi\wedge d\kappa$ 和
$\iota_{X_h}\omega_{\rm red}=dh$ 的规范下，

$$
\dot\kappa=-\partial_\chi h,\qquad
 \dot\chi=\partial_\kappa h.
$$

它保持 $h$，在上述零点的线性化特征值为 $\pm ir$。
所以正能量的轨道不可能沿这个守恒流渐近收敛到 $h=0$。
另一方面，联合占位相位门
$e^{-i\alpha N_xN_y}$ 精确作用为

$$
(p,\chi)\longmapsto(p,\chi+\alpha),
$$

其关系商切向量的范数平方为 $2/I>0$。
它能改变 $\zeta$ 的相位，却不会改变只依赖 $X,Y,Z$ 的即时损失。

**证明。**

把 $X_h=\dot\kappa\partial_\kappa+\dot\chi\partial_\chi$
代入辛形式，得到
$\iota_{X_h}\omega=\dot\chi\,d\kappa-\dot\kappa\,d\chi$，
由此得方程。$dh(X_h)=\omega(X_h,X_h)=0$。
使用前一定理的 Hessian，线性矩阵为

$$
\begin{pmatrix}
 0&-2r/I_*\\ rI_*/2&0
 \end{pmatrix},
$$

平方等于 $-r^2I_2$，故特征值为 $\pm ir$。
该门只对模式 $13$ 乘以 $e^{-i\alpha}$，所以
$\theta_{13}$ 增加 $\alpha$，其余相位与全部概率不变；
再代入商度量即得范数。

证毕。

此处的 Hamilton 流是关系商上的辛流。
函数 $h$ 对纯态振幅为四次式；
其可用两拷贝测量的事实，并不自动把这个流实现为固定单拷贝线性 Hamiltonian 的演化。

<a id="prop-closure-penalty"></a>

**命题 10.4（闭包残差作为可核验的学习约束）。**
对固定有限仪器，设 $P_\eta$ 是一个光滑恒秩的
Hilbert--Schmidt 正交投影族，且 $\mathcal G\subseteq\operatorname{ran}P_\eta$。
定义

$$
\mathcal E(\eta)=
 \sum_{a,o}\|(I-P_\eta)\Phi_{a,o}^*P_\eta\|_{\rm HS}^2.
$$

则 $\mathcal E(\eta)=0$ 当且仅当
$\operatorname{ran}P_\eta$ 对每个输出分支的 Heisenberg 映射不变。
此时 $W_\infty\subseteq\operatorname{ran}P_\eta$，
从而相应效果摘要对全部允许未来充分。
因此

$$
J(\eta)=L_{\rm future}(\eta)+\lambda\mathcal E(\eta)
                        +\beta\,\operatorname{Cost}(\eta),
 \qquad \lambda,\beta\ge0,
$$

是一个明确可定义的预测学习目标；仅从此定义不推出它的全局可优化性。

**证明。**

有限个非负平方之和为零，当且仅当每项为零。
算符 $`(I-P)\Phi^*P=0`$ 恰等价于
$`\Phi^*(\operatorname{ran}P)\subseteq\operatorname{ran}P`$。
又因该像空间含初始效果族，对词长归纳可知它含所有未来词效果，
于是包含 $W_\infty$。全未来充分性随即由
定理 [8.4](#obs-thm-predictive)的正交补表征得到。
最后一式只是为已给的未来损失和成本函数组合出目标，并不附加未证明的优化结论。

证毕。

<a id="sec-hierarchy"></a>

## 11. 合法长链的高阶关系层级

五模式是长度三的无相邻占位链。以下结果把它推广到任意有限链，
并给出“更多关系”究竟增加什么坐标的精确答案。
这一 Möbius 层级与仓库辛完成卷的合法链结构相对应[2](#ref-repo-sp)。

<a id="def-legal-chain"></a>

**定义 11.1（合法子集、矩与关系相位）。**
令

$$
\Gamma_n=\{I\subseteq\{1,\ldots,n\}:
       \text{$I$ 不含两个相邻整数}\},\qquad n\ge1.
$$

来源的模式为 $I\in\Gamma_n$，概率为 $p_I$，相位为 $\theta_I$。
对每个合法子集 $T\in\Gamma_n$，定义

$$
\mu_T=\sum_{\substack{I\in\Gamma_n\\I\supseteq T}}p_I,
 \qquad
 \Phi_T=\sum_{I\subseteq T}(-1)^{|T|-|I|}\theta_I\pmod{2\pi}.
$$

其中 $\mu_\varnothing=1$，$\Phi_\varnothing=\theta_\varnothing$。
$\mu_T$ 是所有 $T$ 中位置同时占位的概率。
非合法 $T$ 的占位矩恒为零，所以不作为独立坐标。

<a id="thm-mobius"></a>

**定理 11.2（完整 Möbius 反演与关系辛坐标）。**
上述矩变换和相位变换均整数可逆，逆公式为

$$
p_I=\sum_{\substack{T\in\Gamma_n\\T\supseteq I}}
          (-1)^{|T|-|I|}\mu_T,\qquad
 \theta_I=\sum_{T\subseteq I}\Phi_T\pmod{2\pi}.
$$

在全正振幅域有

$$
\sum_I p_I\,d\theta_I=\sum_{T\in\Gamma_n}\mu_T\,d\Phi_T,
 \qquad
 \omega_{\rm FS}
 =\sum_{\substack{T\in\Gamma_n\\T\ne\varnothing}}
                  d\Phi_T\wedge d\mu_T .
$$

固定所有 $1\le|T|\le q$ 的均值，并商去其对应的相位作用，
其中 $0\le q\le\lceil n/2\rceil$。
只要该固定矩域含一个全正概率，其正域关系商实维数为

$$
2D_{n,q},\qquad
 D_{n,q}=\sum_{k=q+1}^{\lceil n/2\rceil}
                       \binom{n-k+1}{k},
$$

每个 $|T|>q$ 的合法子集贡献一对 $(\mu_T,\Phi_T)$。

**证明。**

合法子集族向下封闭，因此若 $I\subseteq J$ 且 $J$ 合法，
区间中的每个 $T$ 都合法。代入矩定义，

$$
\sum_{T\supseteq I}(-1)^{|T|-|I|}\mu_T
 =\sum_{J\supseteq I}p_J
       \sum_{I\subseteq T\subseteq J}(-1)^{|T|-|I|}.
$$

内层和为 $(1-1)^{|J\setminus I|}$，仅 $J=I$ 时为一，
故得到 $p_I$。相位逆式的证明相同。
这些矩阵按集合大小排序后都是对角线为一的整数三角矩阵，
因而在整数格上可逆，并在相位环面上不存在额外周期覆盖。

将 $\theta_I$ 的逆式代入一形式并交换有限求和次序，

$$
\sum_Ip_I\sum_{T\subseteq I}d\Phi_T
 =\sum_T\left(\sum_{I\supseteq T}p_I\right)d\Phi_T
 =\sum_T\mu_Td\Phi_T.
$$

取负外微分并除去共同相位，得到辛形式。
由于整数变换可逆，全正射影域的全部非空矩与关系角
是一套独立坐标。固定低阶矩、除去其相位后，剩下的坐标
恰是所有高阶对；正概率不等式只将其概率部分截成一个非空开凸域，
不会改变局部维数。

最后计数大小为 $k$ 的合法子集。
若 $1\le i_1<\cdots<i_k\le n$ 且 $i_{j+1}\ge i_j+2$，
令 $j_a=i_a-(a-1)$，便得到
$1\le j_1<\cdots<j_k\le n-k+1$，且逆变换唯一。
所以该层有 $\binom{n-k+1}{k}$ 个模式。
把高于 $q$ 的各层相加，得所述维数。

证毕。

特别地，$|\Gamma_n|=F_{n+2}$。
当 $n=3,q=1$ 时，唯一高阶合法子集为 $\{1,3\}$，
其矩与相位正是 $\kappa$ 和 $\chi$。
当 $n=9,q=2$ 时，模式数为 $89$，
非空一、二阶均值共有 $9+28=37$ 个，
剩余高阶关系为 $35+15+1=51$ 对，关系商实维数为 $102$。
这些是指定读出菜单的状态关系维数，不是物理空间维数。
全链上每个高阶占位矩对应对角投影；
其独立读出或相位驱动是否可实现，仍须逐项供给操作菜单。

<a id="sec-quantization"></a>

## 12. 几何量子化与整数荷扇区的一个精确接合

本节不援引一般的“量子化与约化交换”作为结论。
它在本模型的正则球面上，用两张复坐标图直接建立一个可证明的对应。

<a id="thm-polynomial-quantization"></a>

**定理 12.1（多项式量子化与占位基的对应）。**
在正则关系球面上，以
$z=\zeta=e^{\tau/2-i\chi}$ 为有限复坐标。
给定 $s>0$ 且 $n=sw(b)\in\mathbb Z$。
两图 $z$ 与 $w=1/z$ 上，以

$$
e_\infty=e_0 z^n
$$

为框架过渡定义复线丛 $\mathcal O(n)$。
它存在 Hermitian 度量，使 Chern 连接曲率为
$-is\omega_{\rm red}$，其全局全纯截面空间恰为

$$
H^0(S_b,\mathcal O(n))
 \simeq\{f(z):f\text{ 是次数不超过 }n\text{ 的复多项式}\}.
$$

因此该空间的复维数为 $n+1$。

若采用定理 [5.3](#thm-geom-sector)的整数对称载体，
令 $s=m$ 且 $n=k_+-k_-=mw$，
则固定荷扇区与上述截面空间存在保持下述明确指定圆表示的酉同构。
具体地，将占位基 $|k_-+j\rangle$ 对应到归一化单项式 $z^j$。
在截面空间上规定圆表示，使占位门 $e^{-it\widehat n_{13}}$ 对应

$$
f(z)\longmapsto e^{-itk_-}f(e^{-it}z).
$$

**证明。**

几何章已证明 $z$ 是正域的复坐标。
在下极 $z$ 为消失振幅坐标乘以一个处处正的光滑径向因子；
在上极 $1/z$ 有同样性质。
故它们给球面的两张复图，形成 $\mathbb{CP}^1$。
在交叠环上 $z/|z|=e^{-i\chi}$，
所以过渡的单位相位为 $e^{-in\chi}$，
与 Chern 数 $n$ 的符号规范一致。

以下显式构造所需 Hermitian 度量。
写 $u=\log|z|=\tau/2$，则 $\kappa$ 是 $u$ 的光滑严格增函数。
在有限图设置

$$
H_0(u)=
 \exp\left[-2s\int_{u_0}^{u}
                          (\kappa(v)-\kappa_-)\,dv\right],
 \qquad \|e_0\|^2=H_0.
$$

下极附近 $\kappa-\kappa_-$ 是 $|z|^2$ 的光滑函数且一阶非退化，
所以 $H_0$ 光滑延伸为正数。
上极时
$\frac{d}{du}\log H_0\to-2s(\kappa_+-\kappa_-)=-2n$，
且余项为 $|z|^{-2}$ 的光滑函数。
于是
$H_\infty=|z|^{2n}H_0$
在上极也光滑正定，正好符合框架过渡的度量变换律。

在全纯框架下 Chern 连接的一形式为 $\partial\log H_0$；
换成单位框架后为
$\frac12(\partial-\bar\partial)\log H_0$。
由于 $z=e^{u-i\chi}$，若 $f=f(u)$，

$$
\frac12(\partial-\bar\partial)f=-\frac i2 f'(u)\,d\chi.
$$

因此本度量给出
$A_0=is(\kappa-\kappa_-)d\chi$。
求导得 $F=-is\omega_{\rm red}$，与前述预量子构造相同。

一个全局全纯截面写作 $e_0 f_0(z)=e_\infty f_\infty(w)$，
所以

$$
f_\infty(w)=w^n f_0(1/w).
$$

两函数在各自有限复平面全纯。上式在 $w=0$ 全纯，
说明整个函数 $f_0$ 在无穷远至多有 $n$ 阶极点。
也可直接用 Cauchy 估计：上式在小圆盘有界，
使 $|f_0(z)|\le C|z|^n$ 对大 $|z|$ 成立，
故所有高于 $n$ 阶的 Taylor 系数为零。
反之每个次数不超过 $n$ 的多项式都满足上式并在无穷远光滑全纯。
因此单项式 $1,z,\ldots,z^n$ 构成完整基。

以 Hermitian 度量及 $\omega_{\rm red}$ 的正面积元定义截面的 $L^2$ 内积。
球面紧致使积分有限，正度量使内积正定。
由于度量和面积均对 $\chi$ 旋转不变，
不同单项式的内积含非零 Fourier 频率，故为零。
把它们分别归一化，再与正交占位基逐一对应，得到酉同构。
两边圆作用在第 $j$ 个基向量上的本征值都是
$e^{-it(k_-+j)}$，所以该同构保持所列圆作用。

证毕。

这个结论把相同整数区间同时解释为对称占位基和球面全纯截面基。
圆表示按所列函数复合约定定义；
若要求它等于某个覆盖指定底空间旋转的预量子丛提升，
还须说明截面的拉回或推出方向及字符，不能省略该约定。
它的适用载体是已增加的 $\operatorname{Sym}^m(\mathbb C^5)$ 与固定荷扇区。
一般端点门会改变这些荷，因此不能据此将所有五模式门都宣称为同一固定球面上的算符。
扩展这种对应，需要为改变矩层的门另外构造扇区间映射。

<a id="sec-arithmetic"></a>

## 13. 原生替换算术与量子门之间的形式边界

项目同时处理原生有序对象与有限载体计算[7](#ref-repo-native)。
下述最小模型明确指出：同一个 Fibonacci 递推可以出现在不同数学层，
但它本身没有给出酉编码。

<a id="def-tree"></a>

**定义 13.1（有序树替换与计数影像）。**
令 $\mathfrak T$ 为由叶符号 $\alpha,\beta$
和有序二叉构造 $\langle T,U\rangle$ 生成的自由代数。
定义替换同态

$$
\rho(\alpha)=\beta,\qquad
 \rho(\beta)=\langle\beta,\alpha\rangle,\qquad
 \rho(\langle T,U\rangle)=\langle\rho(T),\rho(U)\rangle.
$$

令 $c(T)=(n_\alpha(T),n_\beta(T))^{\mathsf T}$ 为叶计数。

<a id="thm-arithmetic"></a>

**定理 13.2（替换矩阵、遗忘性与正定酉化障碍）。**
对所有树有

$$
c(\rho(T))=Mc(T),\qquad
 M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

计数映射 $c$ 不单射。矩阵 $M$ 的本征值为
$\varphi=(1+\sqrt5)/2$ 和 $-\varphi^{-1}$，
不存在正定 Hermitian 矩阵 $G$ 使 $M^\dagger GM=G$。
更强地，不存在到有限维 Hilbert 空间的单射线性映射 $J$
和酉算符 $U$ 满足 $JM=UJ$。

若 $J_0=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$，则
$M^{\mathsf T}J_0M=-J_0$，$M^2$ 保持 $J_0$。
这种二维反辛或辛性质不推翻前述酉化障碍。

**证明。**

在叶 $\alpha,\beta$ 上，替换后的计数分别为 $(0,1)^{\mathsf T}$
和 $(1,1)^{\mathsf T}$，恰是 $M$ 的两列。
树的计数对二叉构造相加，所以结构归纳给出所有树上的公式。
$\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$
在自由有序代数中不同，却都有计数 $(1,1)$，证明非单射。

特征多项式为 $\lambda^2-\lambda-1$，根为所列两数。
若 $v$ 是 $\varphi$ 的非零本征向量，而 $M$ 对正定内积等距，
便有 $\|v\|_G=\|Mv\|_G=\varphi\|v\|_G$，与 $\varphi>1$ 矛盾。
若存在 $J,U$，则 $Jv\ne0$，且 $U(Jv)=\varphi Jv$，
同样与酉算符保持范数矛盾。
最后直接相乘给反辛等式，再作用一次得到 $M^2$ 的辛性。

证毕。

所以从原生替换接到量子运算，至少必须声明额外编码、辅助载体、
可逆化、读出与成本。可以研究这样的接口，
但不能仅将增长矩阵重新命名为量子门便完成证明。
矩阵范数障碍也不排除在更大载体上以不同编码实现一个有限截断任务；
那是需要新合同和新正确性证明的模型。

<a id="sec-synthesis"></a>

## 14. 总接合、一个可实现实例与理论闭包

<a id="thm-consistency"></a>

**定理 14.1（有限关系--预测理论的相容实现）。**
前述合同存在同时非空且相容的实例；它不需要把经典兼容核、
主相位丛和预测丛识别成同一个对象。
具体地，五模式模型中取

$$
(X,Y,Z)=\left(\frac15,\frac3{10},\frac1{10}\right),
 \qquad \kappa=\frac1{10},
 \qquad
 p=\left(\frac12,\frac1{10},\frac1{10},\frac15,\frac1{10}\right).
$$

则下列结论同时成立。

1. $r=9/10$，正则兼容区间为 $[0,1/5]$，
   宽度 $w=1/5$，关系球面面积为 $2\pi/5$。
   概率核一维，完整量子当前读出核二十一维。

2. 主 $T^3$ 丛的过渡向量为 $c=(-1,0,0)$。
   字符 $q=(-1,0,0)$ 的关联线丛 Chern 数为一。
   尺度 $s=5$ 允许曲率 $-5i\omega_{\rm red}$ 的预量子连接。

3. 取 $m=10$ 及整数荷 $(U,V,W)=(2,3,1)$，
   对称固定荷基为

   $$
   (n_0,n_1,n_2,n_3,n_{13})
    =(4+k,2-k,1,3-k,k),\qquad k=0,1,2.
   $$

   扇区维数为三，等于 $\dim H^0(S_b,\mathcal O(2))$。

4. 同一单副本五模式载体内，
   编码 $\mathcal C=\operatorname{span}\{000,001,100,101\}$
   在明确初始化代码后，可用已声明的理想独立端点实参数脉冲和固定受控相位实现全部 $U(4)$ 逻辑通道。

5. 对任意选定的有限仪器子菜单，未来等价、最小仿射预测商、
   有限反馈的内部等距实现及菜单扩张正合列都成立。

**证明。**

给定概率的五项正且和为一，代入占位定义得到所列均值。
均值满足 $0<X<Y<r$ 且 $X+Y<r$，所以属于第一正则区域。
概率反演给 $\kappa_-=0,\kappa_+=1/5$，
其余第一、二项直接由几何及隐藏维数定理得到。
整数荷代入 $R=9$ 后，非负占位范围为 $0\le k\le2$，
故三种列出的占位恰是完整基。
$mw=2$，因此多项式量子化定理给三维截面空间。

第四项是在同一 $\mathbb C^5$ 上选取四维代码，
并调用定理 [8.11](#obs-thm-universal)已证明的门合同。
它不要求给定五模式纯态全部位于该代码内；
代码任务的输入须经明定编码准备。
第五项只要求有限维与所选子菜单满足仪器规范，
而这些条件可以具体实现，例如任选有限个上述门，
再接标准计算基测量仪器。闭包与等距实现定理因此适用。
这些不同载体和任务由所列嵌入或商映射相连，
不存在把单副本态等同为十副本对称态的隐含步骤。

证毕。

### 14.1. 何种意义上的“统一”已经证明

本稿的接合不是只在词汇上建立相似关系，而是给出以下可交换接口。
在来源层，函数评价与概率取期望交换；
在几何层，整数关系格同时给概率核和共轭相位角；
在丛层，保持核是门输运下降的充要条件；
在预测层，词效果闭包精确刻画全部允许记录的可区分性；
在操作层，内部等距扩张重现有限反馈协议；
在固定整数荷载体上，单项式基与占位基保持一个明确的圆作用。
其中每条接口都有一个已给出的证明。

最核心的三个公式是

$$
\boxed{\quad
 \text{当前预测可下降}
 \ \Longleftrightarrow\
 T_\gamma\ker L_b\subseteq\ker L_c
 \quad}
$$

$$
\boxed{\quad
 \rho\sim_{\rm future}\sigma
 \ \Longleftrightarrow\
 \rho-\sigma\in W_\infty^\perp
 \quad}
$$

$$
\boxed{\quad
 \text{新增预测维数}
 =\dim W_{\rm new}-\dim W_{\rm old}.
 \quad}
$$

第一式是给定输运与旧读出的相容性，
第二式从全部操作菜单构造最小充分读出，
第三式刻画菜单扩张的精确线性增量。
它们合在一起，给出从“隐藏关系”到“内生可预测信息”的完整有限维机制。

这里的丛与输运接口使用恒秩域；预测商的仿射最小性量化全部密度态，
采用有限仪器菜单。门通道结论以代码初始化和独立可调用的理想实参数端点脉冲为前提；
关系损失的测量要求来源独立制备两份相同纯态，其梯度稳定性是固定正概率关系域内的局部结论。

### 14.2. 不由核心公理决定的扩展

理论的边界也以数学数据表达，而不只以措辞保留。

1. **秩变化与奇异约化。**
   恒秩区域以外应使用分层空间、可构造层或适当奇异商。
   本稿已明确处理五模式端点和两条墙的度量行为，
   但一般参数族的全局奇异分类不是恒秩丛定理的推论。

2. **物理时空。**
   若要把某个关系空间解释为时空，必须给出实际事件映射、
   维数选择、Lorentz 度量或因果结构，以及连接与可观测实验量的对应。
   Hermitian 丛、关系曲率和内部时序本身不唯一确定这些附加数据。

3. **实际控制与误差。**
   理想连续门通用性证明有限字存在，
   脉冲下界刻画一般精确目标的参数数量。
   设备上的可用生成元、幅值、带宽、误差与制备成本仍需测定或另供。
   近似闭包的误差界只在其明确收缩假设下使用。

4. **统计学习的可实现性。**
   有限样本误差、双拷贝制备数量、闭包矩阵条件数、
   全局目标优化及迁移到新菜单的性能需要额外分析。
   局部指数稳定定理不宣称全局学习算法已解决。

5. **原生复杂性。**
   树替换、矩阵计数、连续参数控制和机器运行时间分别有不同输入编码。
   任何复杂性类结论必须固定统一算法、输入大小、精度与资源计费，
   不能由维数匹配或有限表存在性单独得出。

### 14.3. 证明来源与数学适用范围

本稿以固定提交为文本证据，所有数学主张由其前提和所附证明承担。
标准向量丛与量子仪器背景来自经典资料；
仓库已经给出的结构与本稿补出的接合一并列明如下。

| 结论族 | 本稿承担的证明 | 来源或额外范围 |
| --- | --- | --- |
| 五模式、概率纤维、关系度量 | 代数反演、整数相位、曲率与端点 | 基础卷、辛完成卷、相位运输卷 |
| 向量丛与预测下降 | 核丛、平行性、holonomy、反例 | 经典丛理论与本稿的读出接口 |
| 四区域主丛 Chern 对应 | 显式两图过渡、方向、字符与面积斜率 | 在固定模型上完整推导 |
| 预量子与占位量子化 | 整性充要条件、Hermitian 度量、多项式基 | 本稿在固定整数载体上的显式接合 |
| 全未来闭包与最小摘要 | 多动作输出词、有限稳定、合法态上的最小性 | 仓库仪器卷；单一迭代 Lean 结果以外的多分支与光滑族范围 |
| 内生有限观察者 | 保留旧记忆标签的等距构造 | 本稿给出的明确实现 |
| 端点通用门 | 精确局部门、十五生成方向、开子群证明 | 仓库 $\Omega$ 卷与标准量子门理论 |
| 关系学习 | 不变量、两拷贝测量、局部指数稳定 | 仓库学习结构与本稿补全的测量/稳定证明 |
| 高阶关系层级 | 完整 Möbius 反演和维数公式 | 辛完成卷的合法链结构 |

已有的 Lean 文件
`AllFutureStatisticsSufficiency.lean` 与
`MinimalPredictiveSummary.lean`
提供给定线性 Heisenberg 迭代的相应形式结果
[9](#ref-repo-lean-future)、[10](#ref-repo-lean-minimal)。
这两项源结果限于给定单一线性 Heisenberg 迭代；本文的多动作、
多输出、光滑参数族、微分几何和控制结论由各自明示的前提及普通数学证明承担，
不属于整卷证明助手认证。普通数学的“形式理论”与“证明助手已检查的库”是不同的证据范围。

数学依赖分别为：有限集合函数代数与整数核支撑概率和关系坐标；
有限矩阵仪器及词闭包支撑未来统计；合法密度态的相对内点支撑仿射最小性；
恒秩光滑子丛支撑商输运；五模式正则约化和两图过渡支撑 Chern 计算；
门字通用性、两拷贝损失与局部稳定性各自保留其操作和光滑性假设。
这些接口连接不同的载体，并不把它们识别为同一个数学对象。

## 参考文献与固定来源

<a id="ref-repo-found"></a>

**[1]**

trureturing，固定提交
`7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c`。
[AURIC FIB Atom Pyramid: Foundational Formulas and Relations](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
下列同仓库文稿均固定于该提交。

<a id="ref-repo-sp"></a>

**[2]**

trureturing。
[Symplectic Predictive Completion](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md)，
特别是第 35 节的射影完成、约化、度量和合法链层级，以及第 37 节的关系学习结构。

<a id="ref-repo-hol"></a>

**[3]**

trureturing。
[AURIC FIB Atom: Probability, Phase Transport and Holonomy](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)。

<a id="ref-repo-omega"></a>

**[4]**

trureturing。
[AURIC Omega: Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
包括五模式 PXP、跨窗编码、一般脉冲下界和保码端点控制。

<a id="ref-repo-instrument"></a>

**[5]**

trureturing。
[AURIC FIB Atom: Output-Resolved Instrument Closure](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)。

<a id="ref-repo-learning"></a>

**[6]**

trureturing。
[FIB Atom: Machine Learning Whitebox](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md)。

<a id="ref-repo-native"></a>

**[7]**

trureturing。
[FIB Native: Finite Table Complexity Classification](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/FIB_NATIVE_FINITE_TABLE_COMPLEXITY_CLASSIFICATION.md)。

<a id="ref-repo-axes"></a>

**[8]**

trureturing。
[AURIC FIB: Observer-Internal Three-Axis Geometry and Predictive Interface](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。

<a id="ref-repo-lean-future"></a>

**[9]**

trureturing。
[`D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean`](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean)。
该源结果讨论给定单一 Heisenberg 迭代的全未来统计充分性。

<a id="ref-repo-lean-minimal"></a>

**[10]**

trureturing。
[`D5/S3/Quantum/Fibers/MinimalPredictiveSummary.lean`](https://github.com/the-omega-institute/trureturing/blob/7bcb8485ed1daaa7b2a859c57e0ba8ccedc4991c/D5/S3/Quantum/Fibers/MinimalPredictiveSummary.lean)。

<a id="ref-hatcher"></a>

**[11]**

Allen Hatcher。
[*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf)。
作者公开教材，向量丛、clutching 和特征类背景。

<a id="ref-cannas"></a>

**[12]**

Ana Cannas da Silva。
[*Lectures on Symplectic Geometry*](https://people.math.ethz.ch/~acannas/Papers/lsg.pdf)。
作者公开讲义，Hamilton 作用、矩映射和辛约化背景。

<a id="ref-simon"></a>

**[13]**

Barry Simon。
[Holonomy, the Quantum Adiabatic Theorem, and Berry's Phase](https://authors.library.caltech.edu/records/2pepc-k9f58)。
*Physical Review Letters* 51, 2167--2170 (1983)。

<a id="ref-wilczek"></a>

**[14]**

Frank Wilczek and A. Zee。
[Appearance of Gauge Structure in Simple Dynamical Systems](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.52.2111)。
*Physical Review Letters* 52, 2111--2114 (1984)。

<a id="ref-watrous"></a>

**[15]**

John Watrous。
[*The Theory of Quantum Information*](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。
Cambridge University Press, 2018；作者公开版本。

<a id="ref-barenco"></a>

**[16]**

Adriano Barenco et al。
[Elementary Gates for Quantum Computation](https://arxiv.org/abs/quant-ph/9503016)。
*Physical Review A* 52, 3457--3467 (1995)。

<a id="ref-jean"></a>

**[17]**

Frédéric Jean。
[*Control of Nonholonomic Systems and Sub-Riemannian Geometry*](https://arxiv.org/abs/1209.4387)。
arXiv:1209.4387。

## 追加锚（本行以下为增补区）

## 26. 顺序无关比较的最小内核：正的二元群胚函数

用户的直觉可以先写成一句话：任意两个准备都能比较，而且交换比较次序不改变可观测结果。这里必须区分三种“次序无关”。实数读数可以满足

$$
r(a,b)=r(b,a),
$$

但承载干涉的振幅在反向时只应满足共轭关系

$$
\kappa(b,a)=\overline{\kappa(a,b)}.
$$

若连振幅本身也要求严格相等，就只剩实 Hilbert 几何，连续复相位会被删掉。另一个容易混淆的要求是路径独立：它不应写成
$\kappa(a,c)=\kappa(a,b)\kappa(b,c)$，因为一般内积并不乘法可分；正确的三点量是闭合回路的 holonomy。

**定义 26.1（正的二元群胚比较公理）。** 令 $P$ 为准备对象集，$\mathsf{Pair}(P)$ 为其二元群胚：箭头是 $(a,b):a\to b$，反向箭头为 $(b,a)$。一个比较振幅是函数

$$
\kappa:P\times P\longrightarrow\mathbb C
$$

满足以下三条：

1. **单位与反向：** $\kappa(a,a)=1$，且 $\kappa(b,a)=\overline{\kappa(a,b)}$；
2. **有限自比较正性：** 对任意有限序列 $a_1,\ldots,a_n$ 和任意 $z_1,\ldots,z_n\in\mathbb C$，
   $$
   \operatorname{Self}_\kappa(z):=
   \sum_{i,j=1}^{n}\overline{z_i}\,\kappa(a_i,a_j)\,z_j\ge0;
   $$
3. **同一对象相容：** 重复对象或删去重复对象只按同一二次型的限制处理，不产生新的比较值。

第二条是整条公理的核心压缩：它没有先说“存在 Hilbert 空间”，只说任何有限形式叠加的自比较不能为负。它等价于每一张有限比较表都是正半定 Gram 表；因此它仍然承载第 22 章的全部数学内容，只把“正核”改写成内生的自比较约束。

**定理 26.2（比较几何与顺序无关读出）。** 定义 26.1 等价于归一化正定核。于是存在 Hilbert 空间 $H$ 和向量 $\psi_a$，使

$$
\kappa(a,b)=\langle\psi_a,\psi_b\rangle,
\qquad \|\psi_a\|=1,
$$

且由有限张成空间的 GNS/Kolmogorov 构造得到的实现，在循环子空间上酉等价。可观测的两两比较

$$
r(a,b):=|\kappa(a,b)|^2
$$

满足 $r(a,b)=r(b,a)$。三点闭环

$$
\Phi(a,b,c):=\kappa(a,b)\kappa(b,c)\kappa(c,a)
$$

在局部相位变换 $\kappa(a,b)\mapsto\overline{\theta_a}\kappa(a,b)\theta_b$ 下不变；反向闭环给出 $\overline{\Phi}$。因此顺序无关的是概率读出，方向信息保存在可观测的 Bargmann holonomy 中。若强行令 $\kappa(a,b)=\kappa(b,a)$，则所有比较值为实数，候选退化为实 Hilbert 型几何，不能表达一般复量子相位。证毕。

**命题 26.3（三点提升不能代替全局正性）。** 只要求每三个对象的比较表正半定，不足以产生共同几何。取四个对象，令对角元为 $1$，所有不同对象之间的比较为 $-2/5$。任意三阶主子矩阵的特征值为

$$
\frac75,\ \frac75,\ \frac15,
$$

所以每个三点提升都通过；四阶矩阵另有特征值

$$
1+3(-2/5)=-\frac15,
$$

故整体不是正半定。于是“每一对可比”加“每一组三点可拼接”仍会在四点处断裂。全有限的自比较正性不是装饰，而是把局部边数据接成一个整体的必要约束。证毕。

**命题 26.4（严格交换对称也不够）。** 对角为 $1$、非对角为 $-9/10$ 的三阶实对称表满足每一对的数值范围约束，但其最小特征值为 $1+2(-9/10)=-4/5$。因此交换次序无关只给出无向边标记，既不保证共同实现，也不保证量子正性。

**定理 26.5（Born 桥的精确边界）。** 由定义 26.1 单独得到的是纯态比较几何。若另给一个在 $H$ 上闭合的效应系统 $\mathcal E$，并要求事件读数对有限正交分解可加、对连续极限连续，则

$$
p_a(E)=\langle\psi_a,E\psi_a\rangle
$$

给出归一化概率；在有限维 $\dim H\ge3$ 时，Gleason/Busch 桥把所有这样的读数刻画为密度算子迹。这个桥不能从 $r(a,b)$ 的对称性单独推出，因为固定事件菜单下，经典单纯形和不同 Bargmann 相位可以给出同一份实读数。证毕。

**候选 26.6（最简几何图景）。** 量子起源的最小候选不是“所有东西都可交换”，而是：准备对象形成一个二元群胚；每条边有一个反向取共轭的比较振幅；任何有限多边形的自比较非负；可观测边长是模平方，三边闭环的相位是 holonomy。GNS 只是把这张内生的正比较网摊平成 Hilbert 空间，Born 规则则是再给事件效应后的读出定理。

这说明复杂度的真正来源只有一个：边的局部读数必须有一个共同的有限联合约束。删去正性，会得到不能拼成整体的表；删去共轭反向，会丢掉相位；删去事件效应桥，会只有态空间而没有测量概率。下一步可形式化的精确命题是：在有限集上，定义 26.1 的有限自比较正性与所有有限 Gram 表正半定逐项等价，并把命题 26.3 的四点反例作为三点方案的终止判据。

白话说：每两件东西都能握手，交换握手顺序时“相似度”不变；但握手时留下的复数方向，反过来要取共轭，三个人围成一圈还会留下一个相位。只检查每条边或每个三角形，四个人可能仍然无法站在同一张量网里；真正的最简公理是“任何有限人群的合成自比较都不能为负”。它把整张网摊成 Hilbert 空间，却没有假装测量已经出现；测量和 Born 概率仍是另一条明确的桥。

## 27. 再减法：自由关系上的二次自比较律

第 26 节把约束写成二元核。还可以再压缩一次：不把核当作原始数据，只给准备对象的自由复线性包络和一个“自比较”。这样公理只说合成对象的长度如何相加；二元比较由极化自动出现。

**定义 27.1（二次自比较公理）。** 令 $P$ 为准备对象集，令

$$
V_0=\mathbb C^{(P)}
$$

为以 $P$ 为基的有限支撑复向量空间，基向量记为 $e_a$。给一个函数

$$
Q:V_0\longrightarrow[0,\infty)
$$

满足

$$
Q(\lambda v)=|\lambda|^2Q(v),\qquad Q(e_a)=1,
$$

以及平行四边形律

$$
Q(v+w)+Q(v-w)=2Q(v)+2Q(w).
$$

这里没有预设内积、核或 Hilbert 空间；$V_0$ 只表达“可以把有限比较对象形式地合成”。

**定理 27.2（极化重建定理）。** 定义 27.1 唯一决定一个半内积

$$
B(v,w)=\frac14\Bigl(Q(v+w)-Q(v-w)
 +iQ(v+iw)-iQ(v-iw)\Bigr),
$$

使得 $B(v,v)=Q(v)$。它满足共轭对称、第一变量共轭线性、第二变量线性和 Cauchy–Schwarz 不等式。令

$$
N=\{v:Q(v)=0\},\qquad H=\overline{V_0/N},
$$

则 $H$ 是 Hilbert 空间，且

$$
\kappa(a,b):=B(e_a,e_b)
$$

是归一化正定核。

**证明。** 平行四边形律和绝对齐次性是复 Jordan–von Neumann 极化恒等式的代数条件；将 $Q$ 代入上式，逐项相消得到加性、共轭对称性和复齐次性。对任意 $v,w$，多项式 $Q(v+\lambda w)=B(v+\lambda w,v+\lambda w)$ 对所有 $\lambda\in\mathbb C$ 非负，其判别式给出

$$
|B(v,w)|^2\le Q(v)Q(w).
$$

因此 $N$ 是子空间，商空间上的 $B$ 正定，完备化得到 $H$。反向地，任意归一化正定核在有限形式和上定义

$$
Q\!\left(\sum_i z_i e_{a_i}\right)
 =\sum_{i,j}\overline{z_i}\,\kappa(a_i,a_j)z_j,
$$

立即满足定义 27.1。故二次自比较律与第 26 节的全有限正定核在数学内容上等价；它只是把核压缩成一个内生的二次律。证毕。

**命题 27.3（逐条反推必要性）。**

1. 删除平行四边形律，取 $V_0=\mathbb C^2$、$Q(x)=\|x\|_p^2$（$p\ne2$）。它仍非负且满足 $Q(\lambda x)=|\lambda|^2Q(x)$，但
   $$
   Q(1,1)+Q(1,-1)=2^{1+2/p}\ne4=2Q(1,0)+2Q(0,1),
   $$
   所以不存在由 $Q$ 产生的内积几何。
2. 只保留实齐次性而不要求 $Q(iv)=Q(v)$，最多得到实 Hilbert 结构；复相位和 Bargmann holonomy 没有来源。
3. 只在支撑大小不超过三的形式和上要求律，四对象的对角 $1$、非对角 $-2/5$ 表仍通过全部三点检验，却在四点方向 $(1,1,1,1)$ 上给出负自比较。因此全有限闭包不能删去。
4. 删除非负性会留下 Minkowski 型不定二次形，不能解释概率的非负性。

**定理 27.4（从二次律到量子公理的对应）。** 二次自比较公理给出归一化态向量、复内积、Cauchy–Schwarz 和纯态转移量

$$
p(a\to b)=|B(e_a,e_b)|^2.
$$

若再给出同一 $H$ 上的效应系统 $0\le E\le I$、互斥事件的有限可加性和连续性，则

$$
p_a(E)=B([e_a],E[e_a])
$$

是归一化 Born 型读数；在有限维 $\dim H\ge3$ 时，Gleason/Busch 定理把它刻画为 $\operatorname{tr}(\rho E)$。二次律本身不提供事件、时间演化、张量积或状态更新；这些仍是独立桥梁。

**候选 27.5（最简几何结构）。** 先有一座自由复关系空间，$Q$ 是其非负二次锥；零自比较方向被压成同一点，极化把二次锥切成带方向的比较，完备化才显出 Hilbert 空间。交换顺序无关的是 $|B|^2$；复方向和闭环相位属于极化后的比较，而非 $Q$ 的单个实读数。

这轮的“更简洁”是语法压缩而非假设删除：一个二次律替代了显式核表，但自由复线性包络已经把有限合成能力写进模型。若连这层包络也不允许，命题 26.3 说明没有办法从局部两两读数自动得到整体量子几何。

白话说：先不说两件东西的相似度是多少，只规定“把许多准备叠在一起后，自我比较像平方长度，而且满足平行四边形公式”。这一个规则会自己长出内积和正定核；删掉平行四边形就会落入普通的 $p$-范数，删掉复齐次性就只剩实几何，删掉全局范围就会在四个对象处断裂。Born 概率仍要等事件和效应加入后才出现。

## 15. 五态边际均值遗漏的离散转移谱与联合读口

**约定 15.1（同源、校准与记录菜单）。** 沿用定义 3.1 的次序 $\Sigma=(0,1,2,3,13)$，
概率为列向量，转移为非负列随机矩阵。令

$$
O=\begin{pmatrix}1&1&1&1&1\\0&1&0&0&1\\0&0&0&1&1\\0&0&1&0&0\end{pmatrix},
\qquad d=(1,-1,0,-1,1)^{\mathsf T},\qquad \ker O=\mathbb R d.
$$

这是定理 3.3 的质量增广观察；$d$ 是有符号差方向，不是可制备概率。
对候选参数的每次比较，固定同一初始概率 $p$、状态标号、时步和读出校准。
基础菜单 $\Pi_{\rm marg}$ 许可在独立重复的同一 $p$ 制备上选择 $n\ge0$，
执行该候选转移 $n$ 次，再读一个 $r\in\{x,y,z\}$ 的终端二元值，或取得它的精确期望。
种子律不随候选改变且独立于来源抽样；反馈只能用已有记录。每次试验只保留这个单读口结果，
不保留同轨迹的配对时刻或同时占位联合值，也不额外供应其他控制。
精确期望是律层面的理想权限，不是有限样本自动提供的数值。
下面的联合菜单 $\Pi_{\rm lag}$ 则另供同一条经典轨迹上两个相邻时刻的非扰动读出，
并许可保留其联合律或取得所示乘积的精确期望；有限次抽样不等于取得精确期望。
候选比较均采用同一菜单与同一制备，符合[变化优先卷约定 11.1](AURIC_FIB_ATOM_CHANGE_FIRST_RELATIONAL_FIELD_AND_INTEGRABILITY.md)的共同协议合同。

**命题 15.2（相同全部时刻均值而不同的离散隐藏谱）。** 置

$$
P_0=\frac{\mathbf1\mathbf1^{\mathsf T}}5,\qquad
P_d=\frac{dd^{\mathsf T}}4,\qquad
K_\eta=P_0+\eta P_d,\qquad -\frac45\le\eta\le\frac45.
$$

$K_\eta$ 是对称双随机矩阵，均匀律 $c=\mathbf1/5$ 是共同平稳制备。
其特征多项式及全部正整数次幂为

$$
\det(tI-K_\eta)=t^3(t-1)(t-\eta),\qquad
K_\eta^n=P_0+\eta^nP_d\quad(n\ge1),\qquad
OK_\eta^n=OP_0.
$$

所以对每个共同初态 $p$，全部时刻的三均值不依赖 $\eta$；$n\ge1$ 时恒为 $(2/5,2/5,1/5)$。
所有候选在 $\Pi_{\rm marg}$ 下具有相同完整记录律，
但隐藏特征值可为负、为零或为正；$\eta=0$ 时零特征值重数为四。
若在共同平稳制备 $c$ 下增加 $\Pi_{\rm lag}$ 的读口 $h(s)=d_s$，则

$$
\mathbb E_{c,K_\eta}[h(S_t)h(S_{t+1})]=\frac{4\eta}{5},
\qquad \mathbb E_c h=0,\qquad \mathbb E_c h^2=\frac45.
$$

因此这个新增的同轨迹联合期望在律层面精确识别 $\eta$；单次配对样本不作此断言，
该期望也不是基础菜单已经保留的边际均值。

证明。$\mathbf1^{\mathsf T}d=0$、$d^{\mathsf T}d=4$，所以 $P_0,P_d$ 是正交的秩一投影。
$K_\eta$ 的每项为 $1/5+\eta d_id_j/4$；$d_id_j\in\{-1,0,1\}$，
且两种非零符号都出现，故非负性恰要求 $|\eta|\le4/5$。
每行及每列的附加项和为零，故双随机且保持 $c$。
在 $\mathbb R\mathbf1$、$\mathbb R d$ 及其三维共同正交补上的作用分别为 $1,\eta,0$，
得到特征多项式与幂公式；后者只用于 $n\ge1$，不将它误作 $K^0=I$。
$Od=0$ 再给观察公式。$n=0$ 的共同读数是 $Op$，同样不随参数改变。
基础菜单的单次终端读数为 Bernoulli 变量，其参数已由相同的均值确定；
独立重复制备使每个新读数的条件律相同。对反馈记录归纳即得全部有限记录同律，
在柱集生成的无限记录合同上也同律。

平稳制备时相邻状态的联合概率为 $\Pr(S_t=j,S_{t+1}=i)=(K_\eta)_{ij}/5$，
所以配对期望为 $d^{\mathsf T}K_\eta d/5=\eta d^{\mathsf T}d/5=4\eta/5$。
两个单时刻的 $h$ 分布却都来自同一个 $c$，并不随参数改变。
这同时给出基础记录相同而联合目标不同的明确候选对，例如 $\eta=0$ 与 $\eta=-4/5$。证毕。

### 15.3. 已有五态纤维、目标风险与校准的应用

定理 3.2–3.3 给同一初始来源的

$$
p_\kappa=(1-X-Y-Z+\kappa,X-\kappa,Z,Y-\kappa,\kappa),
\quad L=\max(0,X+Y+Z-1)\le\kappa\le U=\min(X,Y),
$$

以及 $\mathbb E_{p_\kappa}f=A_f+J_f\kappa$，其中
$A_f=f_0+(f_1-f_0)X+(f_3-f_0)Y+(f_2-f_0)Z$。
这里的 $J_f=f_{13}-f_1-f_3+f_0=f d$，不是一个另供的动力学本征值。
对校准向量

$$
q_+=(0,2,3,5,7),\qquad q_\times=(1,2,3,5,10),\qquad
q_{\max}=(0,2,3,5,5)
$$

分别有 $J=0,4,-2$。
[基础公式卷命题 7.4](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)的中点半径因此为 $|J_f|(U-L)/2$。
允许预测器另外使用独立种子不会降低这个绝对损失半径：若两个端点目标为 $a,b$，
逐种子有 $|\widehat\mu-a|+|\widehat\mu-b|\ge|a-b|$，取期望后至少一个端点风险不小于半长度；
固定中点同时达到。$X=Y=1/2,Z=0$ 时，$q_\times$ 的期望范围为 $[3.5,5.5]$，最坏风险为 $1$。
这是精确均值权限下对既有 minimax 公式的应用，未把有限样本风险或计算成本等同于它。

若未知校准为 $f=(u,2,3,5,v)$、$(u,v)\in\mathbb R^2$，
且另供已知的同源制备 $p^{(j)}$ 及其精确目标期望，减去已知 $q_+$ 基线得

$$
\mathbb E_{p^{(j)}}f-\mathbb E_{p^{(j)}}q_+
=p^{(j)}_0u+p^{(j)}_{13}(v-7).
$$

因此识别整个校准参数对恰要求行 $(p^{(j)}_0,p^{(j)}_{13})$ 构成的矩阵秩为二：
满列秩给唯一线性逆，秩不足的非零核给相同数据的参数对。
这只是该已知制备合同中的线性代数应用；只知道三个均值不自动知道这两列。

### 15.4. 未来控制的核条件与初始坐标反演

另供一组在同一封闭五态载体上已校准的列随机控制 $K_a$，并许可独立重复同一初态后读取动作前后的精确均值。
[隐藏 seam 卷 Q5–Q6](AURIC_FIB_ATOM_HIDDEN_SEAM_CAUSAL_READOUT_CLOSURE.md)及
[未来商卷 Q8](AURIC_FIB_ATOM_SEAM_BILINEAR_CURVATURE_AND_OUTPUT_FUTURE_QUOTIENT.md)的既有核闭包判据在这里直接应用：
若每个 $OK_a d=0$，则 $K_a d\in\ker O=\mathbb R d$，故任意有限控制词仍把 $d$ 送入此核线。
若这个条件失败，质量守恒给 $\mathbf1^{\mathsf T}K_ad=0$，所以某个 $r\in\{x,y,z\}$ 已有 $rK_ad\ne0$。
固定这一个动作和读口，令初始载体上的拉回效果 $f=rK_a$，则

$$
J_f=rK_ad,\qquad A_f=rK_ap_{\kappa=0},\qquad
\kappa=\frac{rK_ap_\kappa-A_f}{J_f}.
$$

$A_f$ 使用初始 $X,Y,Z$；仿射基点 $p_{\kappa=0}$ 可以是有符号向量。
分母是拉回效果的响应，不是未动作的 $r d$，也不是动作后 $xy$ 的概率。
例如指定 $Ke_0=e_1,Ke_1=e_3,Ke_2=e_2,Ke_3=Ke_{13}=e_0$，则
$Kd=e_1-e_3$、$xK=e_0^{\mathsf T}$，故 $J_{xK}=1$、$A_{xK}=1-X-Y-Z$。
虽然动作后恒有 $p'_{13}=0$，仍由 $X'=p_0=1-X-Y-Z+\kappa$ 恢复初始 $\kappa$。
取初始 $(X,Y,Z,\kappa)=(1/2,1/2,0,1/4)$，其像为 $(1/2,1/4,0,1/4,0)$，
反演确实给 $1/4$。若许可中位翻转 $\tau_2$，它只交换 $0,2$，同理有
$Z'=p_0$，从而 $\kappa=Z'+X+Y+Z-1$。

所以在这些共同载体、共同控制、余维一及全部单步末端均值可读的条件下，
不存在“所有单步盲而首次两步泄露”的情形。
该结论不把平均更新矩阵代替逐输出仪器，也不把边际记录代替联合轨迹。
命题 15.2 的 $K_\eta d=\eta d$ 正属核保持一侧；
新增的 lag 记录是换读出合同，并非在旧边际菜单内发现迟延泄露。

### 15.5. 相干相位与共同无限律的既有接口

相位结论使用命题 8.10 的额外编码 $\mathbb C^2\otimes\mathbb C^2$、$|++\rangle$ 制备及可调用门
$U_f(\tau)|ab\rangle=e^{-i\tau f_{ab}}|ab\rangle$，取该命题的 $\theta=-\tau$。
系数矩阵为 $\frac12\bigl(\begin{smallmatrix}e^{-i\tau f_0}&e^{-i\tau f_3}\\e^{-i\tau f_1}&e^{-i\tau f_{13}}\end{smallmatrix}\bigr)$；
因而可分恰在 $\tau J_f\in2\pi\mathbb Z$。
[相位续卷命题 C-77.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md)的归一化四角谱公式给约化特征值
$(1\pm|\cos(\tau J_f/2)|)/2$，它与该处条件底面矩阵采用同一归一化。
$q_+$ 不产生纠缠，$q_\times$ 在 $\tau=\pi/4$ 给两个特征值 $1/2$，
同时五态占位概率始终是 $(1/4,1/4,0,1/4,1/4)$。
这里需要张量结构、相干制备、相位控制和分辨相位的读口；经典五点标签不供应这些权限。
相同的 $J_f$ 在两种明定模型中分别控制线性目标响应与四角相位，并不把两种操作合同等同。

共同未来律的接口也须另给。固定滤过参考概率 $P$，若 $L_t\ge0$ 为 $\mathcal F_t$ 可测且 $\mathbb E_P L_t=1$，
令 $V_t(A)=\mathbb E_P[\mathbf1_A L_t]$，则前缀相容的条件是
$\mathbb E_P[L_t\mid\mathcal F_s]=L_s$ 对每个 $s\le t$ 几乎处处成立：
两边对每个 $A\in\mathcal F_s$ 积分正是限制测度相等，条件期望的唯一性给反向。
逐个归一化不足以保证这个条件；无限路径扩张还需相应可测空间与限制映射的扩张条件。
[原生长时卷命题 66.1](FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md)已经在其连续路径空间内以真鞅及可数前缀扩张构造共同律。

具体沿用该卷定义 65.1 的同一来源、确定初态、原坐标、时钟及 G/C/N/F 前提，
取 $0<\alpha<1/2,r>0,\widehat m>0$，定理 68.1 给一个不随终止 horizon 改变的 $V_*$，满足

$$
D((V_*)_T\Vert\mathbb P_T)
=\lambda T+\frac{\pi^2\widehat m}{4r^2(1-2\alpha)}T^{1-2\alpha}
 +o(T^{1-2\alpha}),\qquad
|X_t|<r(1+t)^\alpha\quad\hbox{对所有 }t\ge0.
$$

故对每个固定 $b>0$，$\sup_{0\le s\le b}|X_{Ts}|/\sqrt T\le r(1+Tb)^\alpha/\sqrt T\to0$，
而同卷定义 41.1、定理 42.2 的 $\mathbb Q$ 投影极限是方差率 $2\widehat m$ 的非退化 Brownian 运动。
结合定理 55.1 的 $\mathbb Q$ 熵率 $\lambda$，这正是同一主导熵率不能选择该扩散行为的已有应用。
推论 68.2 保留齐次 height-only 控制类与移动管约束类的不同量词；
此处不独立认证原生前提链，也不将上述连续路径过程从五态矩阵推出。

### 15.6. 转移谱的来源与适用边界

命题 15.2 的离散矩阵、负或零隐藏根及新增 lag 证书为 `repo-derived` 的具体观察反例。
其正交谱分解是经典中间工具，参见 Levin–Peres–Wilmer，
[*Markov Chains and Mixing Times*, 第二版](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf)，第 12 章的可逆链谱方法；
行随机约定在这里转置为列随机约定。
[静态 seam 卷命题 30.12](AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)已有连续时间隐藏谱及随机率锥，
这里不重列那些结论；$K_\eta$ 的负根也不主张是该连续半群的指数。
本节 $K_\eta$ 的转移谱、$\operatorname{diag}(f)$ 的读出谱、相干态的约化谱及定理 13.2 的替换矩阵谱是不同对象。
本反例没有提供原生 FIB 转移实现、物理实现、一般 HMM 的识别分类或普适复杂度界。

## 追加锚（本行以下为增补区）

## 16. 有限约束图的来源、目标与逐分支辨识接口

本章把 §11 的合法链矩坐标接到 §8 的输出解析预测商。包含反演、有限函数代数和不可观察子空间是中间工具；所需结论是：给定来源类与真实许可菜单，当前遗漏、未来仍遗漏、目标恢复和同源乘积任务怎样对应。这里的总体概率是实验记录的律，不表示一次轨迹已给出这些数值。

### 16.1. 约束图上的概率坐标与乘积任务

**定义 16.1（图模式与末端菜单）。** 令 $G=(V_G,E_G)$ 为有限无向简单图，允许空顶点集。置

$$
\Sigma_G=\{S\subseteq V_G:S\text{ 不包含任何边}\},\quad
N_G=|\Sigma_G|,\quad x_A(S)=\mathbf1_{\{A\subseteq S\}}.
$$

只对合法 $A\in\Sigma_G$ 保留非零占位函数，$x_\varnothing=1$。全部实读出构成逐点函数代数 $\mathbb R^{\Sigma_G}$。固定整数 $k\ge0$，令

$$
W_k=\operatorname{span}_{\mathbb R}\{x_A:A\in\Sigma_G,\ |A|\le k\},\quad
r_k=\#\{A\in\Sigma_G:|A|\le k\},\quad
M_kp=(\mu_A)_{|A|\le k},\quad \mu_A=\sum_{S\supseteq A}p_S.
$$

来源域暂取全部 $\Delta(\Sigma_G)$。末端菜单是上述占位二元效果及常数效果；在不同独立重复制备上选择不同末端实验。数学上可定义的任意函数或其乘积，并不自动加入实际菜单。

以下坐标计算是动态接口的准备。§11 的反演只用合法族向下封闭，故对 $\Sigma_G$ 同样适用。按大小排列的评价矩阵 $Z_{S,A}=\mathbf1_{A\subseteq S}$ 为对角全一的整数三角矩阵，因而

$$
\begin{aligned}
f&=\sum_{A\in\Sigma_G}c_A(f)x_A,
&c_A(f)&=\sum_{B\subseteq A}(-1)^{|A|-|B|}f(B),\\
p_S&=\sum_{\substack{A\supseteq S\\A\in\Sigma_G}}
 (-1)^{|A|-|S|}\mu_A,
&\mathbb E_pf&=\sum_Ac_A(f)\mu_A.
\end{aligned}
$$

两方向的验证均在合法区间 $[B,S]$ 上求和：中间子集全合法，交替和是 $(1-1)^{|S\setminus B|}$。因此候选完整矩来自概率的充要条件为 $\mu_\varnothing=1$ 且每个显示的逆坐标非负。合法集合偏序不必是 Boolean 格；这里仅使用它的每个包含区间是 Boolean 区间。

这些函数满足

$$
x_Ax_B=\begin{cases}x_{A\cup B},&A\cup B\in\Sigma_G,\\0,&\text{否则},\end{cases}
\qquad
\mathbb R^{\Sigma_G}\simeq
\mathbb R[X_v:v\in V_G]/(X_v^2-X_v,\ X_uX_v:\{u,v\}\in E_G).
$$

商代数中先去掉重复幂，再消去含边的支撑，剩余合法单项式张成；评价矩阵的可逆性证明没有更多关系。这一代数表示在这里用来判定同一来源上的乘积任务。记 $\alpha(G)$ 为最大独立集大小，则 $W_k$ 对乘法封闭恰在 $k=0$ 或 $k\ge\alpha(G)$ 时成立：常数或全代数时成立；若 $1\le k<\alpha(G)$，取合法 $C=A\sqcup\{v\}$、$|A|=k$，则 $x_A,x_v\in W_k$ 而 $x_C\notin W_k$。

特别地，已知 $\mu_A,\mu_B$ 能计算数值 $\mu_A\mu_B$，却未必能识别 $\mathbb E_p(x_Ax_B)$。前者是独立副本的乘积期望，后者是同一模式中的联合任务。期望泛函对全部函数保持乘法只会发生于单点来源：对精确模式指示 $e_S$ 应用 $e_S^2=e_S$ 得 $p_S^2=p_S$，归一化迫使恰有一个质量为一。这里既未改变组合算术，也未授予无损联合测量。

### 16.2. 当前盲核、未来盲核与目标恢复

**定理 16.2（有限图的动态目标辨识）。** 在定义 16.1 的完整来源域上，固定已知的有限动作及输出仪器。采用列概率约定，每个分支 $T_{a,o}$ 非负，$\sum_oT_{a,o}$ 列随机；所有仍影响未来的环境和控制状态均包含在这个有限载体中。按 §8 的逐输出闭包，置

$$
\mathcal U_0=W_k,\qquad
\mathcal U_{j+1}=\mathcal U_j+\sum_{a,o}T_{a,o}^*\mathcal U_j,
\qquad r=\dim\mathcal U_\infty.
$$

这里星号是线性对偶；它将末端函数拉回初始来源。则有下列共同接口。

1. $M_k$ 的秩为 $r_k$。固定矩纤维若含全正概率，其仿射维数为 $N_G-r_k$。当前全部来源上的目标 $\mathbb E_pf$ 可恢复，恰当且仅当 $f\in W_k$。
2. 闭包至多在 $N_G-r_k$ 次扩张后稳定。所有未来实验仍无法区分的差方向是 $\mathcal U_\infty^\perp$，维数 $N_G-r$；未来增加的独立统计方向数是 $r-r_k$。
3. 从全部许可有限实验的总体记录律，在全部来源上恢复 $\mathbb E_pf$ 的充要条件是 $f\in\mathcal U_\infty$。若目标是同源乘积 $fg$，就对函数 $fg$ 使用这个条件，不能改为分别检查 $f,g$。
4. 全未来预测商的规范化状态像具有仿射维数 $r-1$。任何在全部来源上充分的仿射实坐标摘要，秩至少为 $r-1$；该维数可达。持续更新某个给定历史编码，还须满足[未来闭合记忆卷 §15](AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md)的合法接续和右同余条件。

**证明。** 第一项的行独立性由 16.1 的函数基给出。常数行已计入，故核方向的坐标和为零。若纤维含 $p_*>0$，每个 $d\in\ker M_k$ 都允许足够小的双向扰动 $p_*\pm td$，其仿射包络正是该核的平移。

若 $f\in W_k$，其展开只消费已知矩。否则线性分离给 $d\in W_k^\perp$ 且 $f\cdot d\ne0$。从均匀正概率作上述双向扰动，得到相同当前矩而不同目标，给出全来源必要性。

对其余各项，应用 §8.4 的词效果、核及仿射因子证明，按 §8.1 的经典对应转置为列概率。具体说，对时间顺序历史 $h=(b_1,\ldots,b_m)$，$b_i=(a_i,o_i)$，有

$$
T_h=T_{b_m}\cdots T_{b_1},\qquad
\mathcal U_j=\operatorname{span}\{T_h^*g:|h|\le j,\ g=x_A,\ |A|\le k\}.
$$

一次维数不增长即已被每个分支对偶保持，所以以后不再增长；环境维数是 $N_G$，得到步数界。概率差全部为零恰是与全部词效果配对为零，因此得到未来盲核。固定反馈策略时，每个实际输出前缀确定共同的动作词，前缀概率是相应词效果的配对；逐前缀相等即完整记录同律。来源无关的共同随机种子可先固定再积分。

若 $f\in\mathcal U_\infty$，有限多个词效果的线性组合给出其期望；系数允许有负值，这是总体统计重组。若不在，取 $d\in\mathcal U_\infty^\perp$ 且 $f\cdot d\ne0$，从均匀正概率作双向扰动，得到全部未来记录同律而目标不同的两个来源。这证明第三项。

最后 $N:=\mathcal U_\infty^\perp\subseteq\ker\mathbf1^{\mathsf T}$，故商掉该核后，质量一仿射包络的维数为

$$
(N_G-1)-(N_G-r)=r-1.
$$

若仿射摘要在质量零空间上的线性部为 $L$，取 $d\in\ker L$ 并在均匀正概率附近作同样扰动。充分性迫使 $d\in N$，所以 $q(d)$ 通过 $Ld$ 唯一因子化；这里 $q$ 是商映射。秩下界和取商坐标的可达性随之成立。证毕。

该必要性使用完整概率单纯形的相对内部，未以某个低维候选族替代它。受限来源上，正确判据是目标在实际观察纤维上恒定；边界纤维也可偶然没有某个高阶自由方向。对固定非空当前纤维，若目标范围为 $[a_f,b_f]$，则 §15.3 的中点论证仍给最坏期望绝对损失 $(b_f-a_f)/2$：紧性给两个端点，随机估计对端点的损失和至少为区间长度，常数中点达到下界。这不是单次二元效果的概率损失。

路径特例直接消费 §11.2 的计数：

$$
N_{P_n}=F_{n+2},\qquad
r_k=\sum_{j=0}^{\min(k,\lceil n/2\rceil)}\binom{n-j+1}{j}.
$$

三点链一阶纤维通常遗漏一维，九点链二阶纤维在全正处遗漏 $89-(1+9+28)=51$ 维。稳定化步数有限，不意味着不计图大小的高效计算，更不意味着有限样本取得精确概率。

### 16.3. 有序载体对应、条件更新与固定规则标签

为明确经典图模型与 §8 量子模型共同消费什么，可把上述证明放在有限维有序载体上：取实空间 $V$、$D=\dim V$、闭尖生成凸锥 $C$，以及在 $C\setminus\{0\}$ 上严格正的线性质量 $u$。规范化状态为 $\Omega=C\cap\{u=1\}$。许可分支满足 $T_{a,o}C\subseteq C$、$u\sum_oT_{a,o}=u$，末端族 $\mathcal G\subseteq[0,u]$ 有限且含 $u$。

§8 的词效果和维数增长证明只用线性对偶，故环境维数由 $d^2$ 换成 $D$，初维数换成 $\dim\operatorname{span}\mathcal G$。其仿射必要性仍成立，因为生成锥的内部非空，规范化内部点 $v_*$ 对每个 $x\in\ker u$ 都允许足够小的 $v_*\pm tx\in\Omega$。这供应了整个质量一超平面的相对内部，而不是只给一个受限状态子族。

令 $N$ 为全部词效果的消去子。它是包含于初始效果消去子中的最大共同分支不变子空间：$g(T_bx)=(T_b^*g)(x)$ 给正向不变性；反过来，从任一初始盲且共同不变的子空间出发，任意词更新后仍被初始效果消去，故包含于 $N$。因此 $q:V\to V/N$ 上有良定义的 $\overline T_b$ 和 $\bar u$；当 $u(T_bv)>0$ 时，

$$
q\left(\frac{T_bv}{u(T_bv)}\right)
=\frac{\overline T_bq(v)}{\bar u(\overline T_bq(v))}.
$$

分母为零时不定义条件状态。经典对应是 $C=\mathbb R_+^{\Sigma_G}$、$u=\mathbf1^{\mathsf T}$；量子对应是 Hermitian 实空间、半正定锥、迹，且分支额外要求完全正。这个统计商不供应一个实际可调用的压缩或恢复通道，§8.8 已给出这种差别。

若规则本身未知，不能在某个已知规则的 $N_G$ 维空间内把它静默消去。有限候选标签集 $\Theta$ 的一种明确联合模型是

$$
V=\bigoplus_{\vartheta\in\Theta}V_\vartheta,\quad
C=\bigoplus_\vartheta C_\vartheta,\quad
T_b=\bigoplus_\vartheta T_b^{(\vartheta)},\quad
v=(w_\vartheta v_\vartheta)_\vartheta,\quad
\sum_\vartheta w_\vartheta=1.
$$

各分支保持标签，$u(v)=\sum_\vartheta u_\vartheta(v_\vartheta)$。权重是显式给定的先验，不是从记录自动产生的事实；观测后的改变只是条件化。各候选使用同一外部请求与输出标签，拒绝也须可见。于是可在维数 $\sum_\vartheta\dim V_\vartheta$ 上应用同一接口。无先验时保留兼容的联合来源集合；无限规则类也不能仅凭此有限直和公式获得同样的维数结论。

§15.4 已有中位交换动作 $\tau_2$，只交换 $0$ 与 $2$。若该动作确实许可且已知，则 $Z'=p_0$，原三均值连同 $Z'$ 恢复 $\kappa=Z'+X+Y+Z-1$，五态总体律全部可识别。该结论只识别固定仪器下的来源概率。另配[变化优先卷 §11](AURIC_FIB_ATOM_CHANGE_FIRST_RELATIONAL_FIELD_AND_INTEGRABILITY.md)的整数固定解析族，并同时运输普通乘法，整数制备下的加乘结果仍相同：标定函数固定整数，普通整数加乘仍留在整数内。这个逐项事实已足以给共同整数协议同律，不必重做其算术表示证明。状态辨识不识别非整数上的规则延拓；普通相容算术若不固定整数，则不在这一特例的结论范围内。

## 17. 完整块边缘的共同路径来源与三类接缝权限

### 17.1. 从既有接缝补全到一个共同来源

这里消费[隐藏关系卷命题 C-16.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)的精确接缝判据，以及[局部填充卷定理 10.1](AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md)、[边界运输卷定理 6.1](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md)的开放路径条件核拼接。目标是保留整块分布，不能只比较单位置均值。

设非空互不重叠链块 $B_1,\ldots,B_m$ 只由相邻端点排斥边连接，块内完整概率为 $p_i$。记 $a_i$ 为块 $i$ 的右端占位率，$b_{i+1}$ 为块 $i+1$ 的左端占位率。对每条接缝，必要条件是 $a_i+b_{i+1}\le1$。若条件成立，先选端点联合表

$$
q_i(0,0)=1-a_i-b_{i+1},\quad q_i(1,0)=a_i,\quad
q_i(0,1)=b_{i+1},\quad q_i(1,1)=0.
$$

在每个端点条件类内使用对应块的原条件分布，得完整块对耦合

$$
Q_i(S,T)=q_i(e_R(S),e_L(T))\,
 p_i(S\mid e_R(S))p_{i+1}(T\mid e_L(T)).
$$

这正是 C-16.2 按端点类分块的补全：在三位块时，其三块系数分别为 $1/(1-b)$、$1/(1-a)$、$(1-a-b)/[(1-a)(1-b)]$。端点率为零时，对应类的 $q_i$ 整行或整列也为零；率为一时另一端率必须零，只剩相应允许块。零质量类可任取条件分布，不对它作除法。逐行列求和给完整边缘 $p_i,p_{i+1}$。

把整个块模式当作路径上的一个有限字母，定义

$$
K_i(T\mid S)=\frac{Q_i(S,T)}{p_i(S)}\quad(p_i(S)>0),\qquad
P(S_1,\ldots,S_m)=p_1(S_1)\prod_{i=1}^{m-1}K_i(S_{i+1}\mid S_i).
$$

$p_i(S)=0$ 的行任选概率行。它们在归纳中质量始终为零：若第 $i$ 块边缘是 $p_i$，相邻块对边缘为 $p_i(S)K_i(T\mid S)=Q_i(S,T)$，包括这些零行；求和给下一块完整边缘 $p_{i+1}$。故 $P$ 归一化，同时保留全部给定块分布及全部所选相邻耦合。其质量只在合法接缝上非零。

共同来源映射是连接各块词

$$
\iota:(S_1,\ldots,S_m)\longmapsto S_1S_2\cdots S_m.
$$

固定块长使此映射在合法支撑上单射；推前 $\iota_*P$ 是同一条全链上的一份来源。它的第 $i$ 块投影恰为原 $p_i$，不只是端点率相同。它诱导的全部滑动三元边缘自动满足上述开放路径定理的公共二位边缘相等条件。反过来，那些定理可从相容三元边缘构造来源，但仅给三元边缘并不保证保留一个更长块的完整高阶分布；这里通过块字母保留了那项额外数据。这是现有条件核拼接在明确块图上的应用，既不主张共同来源唯一，也不主张独立性。

不能把此路径结论无条件用于闭环。三个单位置块围成三角形，若每个占位率为 $1/2$，每条边都满足两端率之和等于一；但全局独立集至多含一个顶点，期望总占位不超过一，与三个率之和 $3/2$ 矛盾。周期闭合必须另验共同来源，逐接缝可行不足以消去循环约束。

### 17.2. 独立乘积、筛选与分隔编码

对一条接缝，独立乘积的非法质量是 $ab$，故它本身合法恰在 $ab=0$。任何合法保边缘耦合都有端点乘积期望零，协方差为 $-ab$；这正说明保边缘补全一般要求依赖。

若另行执行“取独立样本后仅保留合法组合”的筛选，其成功率为 $1-ab$。成功率正时，成功支的左块边缘为

$$
\widetilde p_L(S)=\frac{p_L(S)}{1-ab}
\begin{cases}1-b,&e_R(S)=1,\\1,&e_R(S)=0.\end{cases}
$$

所以这是另一份来源，不能把成功支当作保留原边缘的补全。$a=b=1$ 时成功率零，根本没有可归一化的成功支。若筛选是许可动作，成功、失败及其概率都属于 §8 的输出分支。

五模式各自均匀时，$a=b=2/5$。两块原有 $25$ 个模式对，非法的 $2\times2$ 个删除后剩 $21$ 个，成功率 $21/25$。成功支在这 $21$ 个模式对上均匀；左端占位率变成 $6/21=2/7$，占位类每个模式质量 $3/21$，非占位类每个模式质量 $5/21$，均非原来的 $1/5$。与此同时 $a+b=4/5\le1$，C-16.2 的保边缘耦合确实存在；两种构造的来源合同不同。

若额外供应一个固定为空的分隔位，则

$$
|S\rangle\otimes|T\rangle\longmapsto|S\,0\,T\rangle
$$

把全部模式对单射地编码到更长合法链；正交基映射给等距嵌入。五模式时是 $25$ 维到七位合法空间的编码。此处消耗一个额外位置及其初始化权限，区别于直接相邻六位链的 $21$ 个合法基态；它正是 §8.9 的张量接缝边界，不能把数学编码当作已经具备的制备操作。

## 18. 图关系系数的对角统计、相位与逻辑立方体接口

### 18.1. 哪些量子协议仍只读取经典对角

另供 $H_G=\operatorname{span}_{\mathbb C}\{|S\rangle:S\in\Sigma_G\}$、密度态、Born 规则和完全正仪器。这些是量子扩展的假设。若末端效果全为对角，且每个许可分支的对偶保持对角子空间，那么 §8 的全部词效果仍为对角。于是全部未来记录仅依赖 $p_S=\rho_{SS}$；相同对角、不同相干的两态操作等价。

精确的经典对应为

$$
K_{a,o}(S,T)=\langle S|T_{a,o}(|T\rangle\langle T|)|S\rangle.
$$

正性给条目非负，分支和保迹给 $\sum_oK_{a,o}$ 列随机；对任意 $\rho$，对偶保持对角保证输出对角只由输入对角决定，并由该 $K_{a,o}$ 更新。因此记录律与图上的经典分支模型相同。若状态更新也保持对角态，则逐个后验密度态本身就有经典表示；若不保持，结论仍限于这些记录。仅有对角末端效果、却许可先作非对角分支变换时，不满足假设，不能宣布相位永远不可见。

### 18.2. 相位支撑与跨侧关系的同一组系数

沿用 §2 的符号规范，写纯态振幅为 $\sqrt{p_S}e^{-i\theta_S}$。在相位群 $\mathbb R/2\pi\mathbb Z$ 内令

$$
\Phi_A=\sum_{B\subseteq A}(-1)^{|A|-|B|}\theta_B,
\qquad N_A|S\rangle=x_A(S)|S\rangle.
$$

16.1 的整数单位三角变换可直接在这个加法群上使用，所以

$$
\theta_S=\sum_{A\subseteq S}\Phi_A,\qquad
U_\theta=e^{-i\Phi_\varnothing}
\prod_{\substack{A\in\Sigma_G\\A\ne\varnothing}}e^{-i\Phi_AN_A}.
$$

这里每个等号均按模 $2\pi$ 理解，因整数逆而没有额外覆盖。这消费 §11.2 的相位反演，不重新把相位反演作为独立经典结果。

若只允许对角门乘积，并把“支撑于 $B$”定义为相位仅依赖 $S\cap B$，那么支撑大小至多 $k$ 的这些门恰能产生所有高于 $k$ 阶的 $\Phi_A$ 为零的对角门，整体相位除外。充分性由显示乘积分解给出；必要性在诱导图 $G[B]$ 的合法模式上展开每个局部门，只含 $A\subseteq B$ 的系数，而对角门相乘只相加这些系数。这个结论没有许可非对角编译、辅助系统或任意控制，不能由它推出一般电路复杂度下界。

现在取独立顶点集 $I=L\sqcup R$，两侧均非空，其余位置固定为空。因为 $I$ 的所有子集都合法，得到完整逻辑立方体

$$
H_I\simeq(\mathbb C^2)^{\otimes|I|}.
$$

另行许可 $|+\rangle^{\otimes|I|}$ 的相干制备及上述门。输出关于 $L|R$ 可分，恰在所有同时接触两侧的 $\Phi_A$、$A\subseteq I$ 均为零时成立。其直接验证消费 §8.10 的四角秩判据：系数矩阵

$$
C_{u,v}=2^{-|I|/2}e^{-i\theta_{u\cup v}},\qquad u\subseteq L,\ v\subseteq R
$$

全部元素非零；秩一等价于每个锚四角满足

$$
\theta_{u\cup v}-\theta_u-\theta_v+\theta_\varnothing=0.
$$

代入关系展开，恰剩 $\sum_{A\subseteq u\cup v,\ A\cap L\ne\varnothing,\ A\cap R\ne\varnothing}\Phi_A$。若这些和全部为零，对 $u\subseteq L,v\subseteq R$ 作包含反演，逐个得到跨侧系数零；反向立即成立。这一逻辑立方体的张量划分不宣称一般有约束图的全空间天然按顶点分成张量积。

对实读出 $f$，若实际另供 $U_f(t)=e^{-it\operatorname{diag}(f)}$，则

$$
\mathbb E_pf=\sum_Ac_A(f)\mu_A,\qquad
\Phi_A(t)=t\,c_A(f)\pmod{2\pi}.
$$

因此同一个系数在总体统计中控制目标对关系矩的线性响应，在这个额外相位执行器中控制相位。三点链的逻辑双位取 $I=\{1,3\}$，唯一跨侧系数是 §15 的 $J_f$，可分恰在 $tJ_f\in2\pi\mathbb Z$。加法、乘积读出及其四角谱已由 §15.3、§15.5 给出，不将它们重复作为新算例，也不将该特定对角门结果扩大成关于所有量子计算的判断。

### 18.3. 全正域的矩角配对及符号范围

在 $p_S>0$ 的纯态域，非空矩给 $N_G-1$ 个实坐标，非空关系相位给同样多个角坐标。§11 的一形式计算在图模式上逐项仍为

$$
\alpha=\sum_Sp_S\,d\theta_S=\sum_A\mu_A\,d\Phi_A,\qquad
\omega:=-d\alpha=\sum_{A\ne\varnothing}d\Phi_A\wedge d\mu_A.
$$

这是上述负指数振幅及二形式的固定约定。若把振幅改写为 $e^{+i\widetilde\theta_S}$，同一态要求 $\widetilde\theta=-\theta$、$\widetilde\Phi=-\Phi$；不能保持角变量的名字与二形式符号同时不变。可分性中的模 $2\pi$ 零条件不受整体换号影响。

固定 $|A|\le k$ 的矩，并商去对应非空低阶相位平移。若纤维含全正概率，剩余正域关系商维数是

$$
2(N_G-1)-2(r_k-1)=2(N_G-r_k),
$$

由每个遗漏高阶 $(\mu_A,\Phi_A)$ 配对。证明只需交换有限求和并使用 16.1 的可逆坐标，未假设各高阶矩可独立在任意范围内制备。$c_A(f)$ 是完整矩坐标开域中 $\partial\mathbb E_pf/\partial\mu_A$；固定的常数矩不参与求导。概率为零时对应振幅相位失效，需转到实际支撑分层；一般概率纤维不能未经常秩和非退化条件统称向量丛。

### 18.4. 接口来源与结论范围

有限图的平方自由单项式与包含反演是成熟有限代数工具；这里的动态恢复判据消费其坐标后，接到本卷 §8.4–§8.7 的逐输出预测商。链的维数和矩角配对消费 §11.2；五态校准、交换动作、四角相位及前缀鞅相容性消费 §15.3–§15.5。后者已经给出共同历史律的相容条件，逐时刻归一化仍不能代替它。

完整块共同来源消费隐藏关系卷 C-16.2 的原有接缝边界及两份开放路径来源的条件核构造；筛选和分隔位是分别列明的操作改变。完整记忆、总体反演及正效果提升的区别由[未来闭合记忆卷 §§15–17](AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md)接续。以上都是这些明定有限模型中的普通数学推导，不附外部原创性或实际物理实现主张。

## 追加锚（本行以下为增补区）
## 19. 两两比较的共同实现、路径可积性与正 Gram 提升

本章把“对象可以两两比较，而且比较结果与顺序无关”压成一个可检验的关系接口。这里的“顺序无关”有三个容易混淆的含义：反向比较必须可逆；把同一比较拆成几段时，路径只由端点决定；这些二元结果是否来自同一个正内积结构。前两项是关系公理，后一项是量子提升的独立条件。把三者混成一句话会把真实缺口藏起来。

### 19.1. 最小二元公理与有限图势

**定义 19.1（共同实现的比较图）。** 令 $F=(I,E)$ 是有限连通有向图，$E$ 同时含每条边的反向边，$G$ 是带单位元的群。一个共同实现的比较图给每条有向边 $(i,j)$ 一个 $T_{ij}\in G$，并要求所有边值、路径复合和反向边值都在同一个实际来源或同一个表示中取得，而不是为每一对输入另选代表。其最小关系公理是

$$
T_{ii}=1,\qquad T_{ji}=T_{ij}^{-1},\qquad T_{ij}T_{jk}=T_{ik}
$$

其中最后一式只在相应三条边和三点共同实现时使用。对一般图，把它等价地写成：任意两条同端点路径 $\gamma,\gamma'$ 的乘积相等，$T_\gamma=T_{\gamma'}$。这一定义不要求任意两个独立物理操作交换；它只要求同一比较被不同地分解时得到同一个端点箭头。

**定理 19.2（有限平坦比较的势函数表示）。** 对有限连通图 $F$，下列条件等价：

1. 任意同端点路径有相同的比较乘积；
2. 每个有向闭路的 holonomy $T_\gamma$ 都是 $1$；
3. 存在 $g_i\in G$ 使每条边满足 $T_{ij}=g_i^{-1}g_j$。

**证明。** $1\Rightarrow2$：闭路的起点和终点相同，故其乘积等于空路径的 $1$。$2\Rightarrow1$：将 $\gamma'$ 反向后与 $\gamma$ 拼接成闭路，得 $T_\gamma T_{\gamma'}^{-1}=1$，所以 $T_\gamma=T_{\gamma'}$。$1\Rightarrow3$：固定基点 $o$，令 $g_i$ 为任意一条从 $o$ 到 $i$ 的路径乘积；条件 $1$ 使它与路径选择无关。于是从 $o$ 到 $i$ 再沿 $(i,j)$ 到 $j$ 的路径给出 $g_j=g_iT_{ij}$，即 $T_{ij}=g_i^{-1}g_j$。$3\Rightarrow1$：路径上的中间势逐项约去，只留下首尾的 $g_{\mathrm{start}}^{-1}g_{\mathrm{end}}$。若 $g_i$ 是一组势，则 $g_i\mapsto hg_i$ 不改变任何边值；这正是整体规范自由度。$\square$

当 $G$ 为加法群时，定理变成 $r_{ji}=-r_{ij}$ 与 $r_{ij}+r_{jk}=r_{ik}$，并有 $r_{ij}=q_j-q_i$。因此用户所说的“结果跟顺序无关”最简洁的数学内容是一个平坦的比较群胚，或在固定基点后的势差；它没有消除非交换乘法，只消除了同一端点箭头的路径记忆。

**命题 19.3（违反公理时的最小后果）。** 若某条反向边不满足 $T_{ji}=T_{ij}^{-1}$，来回比较不回到单位元，比较不可逆。若某个三角形的 $T_{ij}T_{jk}T_{ki}\ne1$，则不存在端点势函数，至少有一条分解路径带有可见记忆。若每条边都能在各自的局部模型中实现、但不能放进同一个共同实现，则这些局部结果不能组成一个全局比较系统。这里的反例只否定共同实现，不否定每一条边的局部可比性。

### 19.2. 从平坦比较到三维相位

**定义 19.4（有限三维提升）。** 令 $U_{ij}$ 是同一 Hilbert 空间上的单位算子，$U_{ji}=U_{ij}^{*}$。经典平坦条件是每个三角形

$$
U_{ij}U_{jk}U_{ki}=I.
$$

若只要求射影比较，则允许中心相位

$$
U_{ij}U_{jk}U_{ki}=\omega_{ijk}I,\qquad \omega_{ijk}\in U(1).
$$

固定四面体的定向约定后，四个三角形的边界相容性为

$$
\omega_{jkl}\,\omega_{ikl}^{-1}\,\omega_{ijl}\,\omega_{ijk}^{-1}=1.
$$

这是一条有限 $2$-cocycle 条件。改变边的相位会把 $\omega$ 改变一个 coboundary；只有在该 cocycle 可由边相位消去时，射影平坦性才可提升为严格平坦性。因而三维提升保留了量子相位的最小余量，却没有把所有闭路强行设为零。

**定理 19.5（有限正 Gram 的共同实现判据）。** 令 $K=(K_{ij})_{i,j\in I}$ 为 Hermitian 矩阵。以下两件事等价：

1. $K$ 的每个主子矩阵都是半正定，并且在重叠指标上限制相容；
2. 存在有限维复 Hilbert 空间和向量 $v_i$，使 $K_{ij}=\langle v_i,v_j\rangle$。

**证明。** $1$ 中包含 $I$ 本身的主子矩阵，故 $K\succeq0$。取谱分解 $K=V^*V$，令 $v_i$ 为 $V$ 的第 $i$ 列，即得 $K_{ij}=\langle v_i,v_j\rangle$。反向由 $K_J=(\langle v_i,v_j\rangle)_{i,j\in J}$ 是 Gram 矩阵而半正定，并且限制显然相容。有限性使这里不需要额外的完备性条件。$\square$

只检查每条边的 $2\times2$ 正性并不够。比如

$$
K=\begin{pmatrix}
1&0.9&0.9\\
0.9&1&-0.9\\
0.9&-0.9&1
\end{pmatrix}
$$

每个二阶主子式都非负，但 $\det K=1-3(0.9)^2-2(0.9)^3<0$，所以没有共同 Hilbert 实现。这是“逐对可比”与“一个共同量子态”之间最短的严格边界。

**定义 19.6（关系—Gram 接口）。** 一个有限关系—Gram 数据由平坦比较图 $(F,T)$、全局半正定 Gram 矩阵 $K$ 以及一个字符 $\chi:G\to U(1)$ 组成；在 $K_{ij}\ne0$ 时要求

$$
\frac{K_{ij}}{|K_{ij}|}=\chi(T_{ij}).
$$

该条件把关系势的相位与正内积的相位接上。定理 19.2 给出端点势，定理 19.5 给出 Hilbert 向量；二者合起来才得到带正内积的共同比较框架。平坦性本身不产生 $K$，逐边正性也不产生全局 $K$。

### 19.3. 与量子力学公理的逐级对应

关系—Gram 接口只供应运动学的候选坐标。Gram 因子化供应 Hilbert 向量；它没有供应真实的相干制备权限。要得到 Born 规则，还需一个凸状态空间、可加且非上下文的正效应赋值，以及满足 Gleason/Busch 型维数和连续性条件；否则同一个 Gram 数据可以配上不同的读出规则。要得到 Wigner 型结论，还需射影射线之间的双射和转移概率保持，不能从单纯的边标记推出。要得到 Stone 型时间生成，还需强连续的一参数酉群及其自伴生成元域；有限图没有物理时间。

张量积还需要独立复合对象的共同实现、局域操作的组合律和相应的局域层析或单体结构。CP/Kraus 动力学需要完整仪器、全输出归一化和更新规则；Lüders 更新是额外选择，不由 Gram 正性推出。完整合法历史、未来效果闭包、真实返回或 \`CountRead\` 需要把历史寄存器和输出菜单纳入同一个模型。最后，能量和物理钟需要自伴生成元的共同定义域以及共同的正 $\hbar$。因此本候选仍须保留七项消费者：Hilbert 与真实相干准备；正质量完整菜单的 Born 读出；真实联合张量；整台箭头及递归同源参考 CP/Kraus；完整仪器和全输出更新/TP 及另付的 Lüders；全合法历史未来与真实返回/\`CountRead\`；物理钟能量生成元域与共同正 $\hbar$。

本章与已有关系丛 §7.4 的核平行、§15–16 的有限正核和回路条件、§18 的有限图相位接口相接。最新有限谱窗的共同盲核结果说明：当比较只能看到同一窗口时，路径独立仍可能留下不可识别方向；窗口分离能恢复某些方向，却不自动供应全局 Gram 或完整仪器。因而本候选减少的是“每一种分解都另付一个端点一致性公理”这一重复负担，把它们统一为一个共同实现的平坦关系；它没有减少正性、概率、复合、动力学或物理钟这些独立桥梁。

**定理 19.7（当前候选的范围）。** 在有限共同实现图上，定理 19.2 与定理 19.5 的假设足以推出端点势和有限 Hilbert Gram 表示；加上中心 $U(1)$ 四面体 cocycle，只得到射影相位的相容性。它们不足以推出 Born、Wigner、Stone、张量、CP 更新或完整量子力学。证明是前述三个定理的逐项组合，且每一步都保留了未付的正性、读出、复合和动力学条件。$\square$

白话说：先把世界看成一张图，每两个点之间有一支箭头；箭头倒过来就是逆箭头，沿着几段箭头走，最后的箭头只看起点和终点。这说明比较本身没有路径记忆，但没有说任何两支实际操作都能交换。把图抬到三维时，三角回路可以严格回到原点，也可以只差一个中心相位；四面体要求这些相位彼此拼得上。要成为量子力学，还必须把所有二元比较放进同一个半正定 Gram 矩阵，才能得到 Hilbert 空间；Born 概率、张量复合、仪器更新和时间生成仍是另外的桥。复杂性来自把这几座桥误写成一条“比较公理”，而不是来自二元比较本身。

## 追加锚（本行以下为增补区）
## 20. 更简洁的量子候选：共同正射影比较核

第 19 章的严格平坦关系是经典骨架。它若被直接当作全部量子比较，就会错误地排除一般量子态的几何相位：三条射线的比较可以有非零 Bargmann 相位。因此更合适的最小候选不是把所有三角形压成 $1$，而是要求所有有限二元比较来自同一个、限制相容的正射影核。这样“加点的顺序无关”仍然成立，但三角回路的中心相位作为可见余量被保留下来。

**定义 20.1（共同正射影比较核）。** 对有限非空指标集 $I$，一个共同正射影比较核是一个矩阵类

$$
[K],\qquad K\in\mathbb C^{I\times I},\qquad K=K^*,\qquad K\succeq0,\qquad K_{ii}=1,
$$

其中等价关系为

$$
K\sim D^*KD,\qquad
D=\operatorname{diag}(e^{i\theta_i})_{i\in I}.
$$

对每个子集 $J\subseteq I$，共同实现要求取同一个 $K$ 的限制 $K|_J$；先加入哪几个指标不改变最后得到的限制。可观测的二元比较和三元相位分别记为

$$
p_{ij}=|K_{ij}|^2,\qquad
B_{ijk}=K_{ij}K_{jk}K_{ki},\qquad
\omega_{ijk}=\frac{B_{ijk}}{|B_{ijk}|}
$$

其中 $B_{ijk}\ne0$ 时才定义 $\omega_{ijk}$。这是一条单一的运动学公理：共同来源上的所有有限比较必须能装进这样的一个正核；它没有把正效应、概率仪器或时间演化偷偷放进来。

**定理 20.2（正射影核的 Hilbert 实现与规范不变量）。** 对定义 20.1 的 $K$：

1. 存在有限维复 Hilbert 空间和单位向量 $\psi_i$，使 $K_{ij}=\langle\psi_i,\psi_j\rangle$；
2. $K\mapsto D^*KD$ 恰对应 $\psi_i\mapsto e^{i\theta_i}\psi_i$，所以射影线 $[\psi_i]$、$p_{ij}$ 和 $\omega_{ijk}$ 不变；
3. 对每个非零四面体，三角相位满足
   $$
   \omega_{jkl}\omega_{ikl}^{-1}\omega_{ijl}\omega_{ijk}^{-1}=1.
   $$

**证明。** 由谱分解 $K=V^*V$，取 $V$ 的第 $i$ 列为 $\psi_i$；$K_{ii}=1$ 给出单位长度。反向的 Gram 矩阵显然半正定。对角相位变换只改变每个向量的代表，不改变其射影线；在 $B_{ijk}$ 中每个顶点相位恰好出现一次正次和一次逆次，故三元积不变。四面体公式中每条边同样成对抵消，留下 $1$。$\square$

这里的四面体关系不是严格平坦性。$\omega_{ijk}=1$ 是零几何相位的特殊情况；一般量子比较允许 $\omega_{ijk}\ne1$，而四面体恒等式只要求这些相位能共同拼接。第 19 章的 $T_{ij}=g_i^{-1}g_j$ 可以看成所有 $\omega$ 都为 $1$ 且比较只保留相位运输的退化层。

**命题 20.3（二元概率不能单独决定量子比较）。** 取三点且所有非对角模长为 $1/2$。下列两个 Gram 矩阵都有相同的 $p_{ij}=1/4$：

$$
K_0=
\begin{pmatrix}
1&1/2&1/2\\
1/2&1&1/2\\
1/2&1/2&1
\end{pmatrix},
\qquad
K_\pi=
\begin{pmatrix}
1&1/2&1/2\\
1/2&1&-1/2\\
1/2&-1/2&1
\end{pmatrix}.
$$

它们都半正定，但 $\det K_0=1/2$、$\det K_\pi=0$；相应的 Bargmann 相位分别为 $1$ 与 $-1$。所以逐对转移概率相同，整体 Hilbert 几何仍可不同。若只保留 $p_{ij}$ 而删掉三元相位，就把量子几何的真实自由度错误地压成经典距离表。

**定理 20.4（有限数据的共同实现与唯一性边界）。** 给定有限的模数据 $p_{ij}$ 和非零三角相位 $\omega_{ijk}$，若存在一个 Hermitian 半正定矩阵 $K$ 满足

$$
K_{ii}=1,\qquad |K_{ij}|^2=p_{ij},\qquad
\frac{K_{ij}K_{jk}K_{ki}}{|K_{ij}K_{jk}K_{ki}|}=\omega_{ijk},
$$

则这些数据有共同 Hilbert 实现。两个实现若给出同一个 $K$，则其向量族在所张成子空间上只差一个酉变换；若只给出 $p$ 和 $\omega$，还必须检查剩余环路的相位和整体半正定性，不能仅凭局部三角条件宣称唯一。

**证明。** 第一个结论由定理 20.2 的谱分解给出。若两个向量族有同一 Gram 矩阵，先在形式线性组合上定义 $\sum c_i\psi_i\mapsto\sum c_i\phi_i$；Gram 相等保证该映射保持内积并消去零向量，故在张成子空间上延为酉映射。最后一句来自两个事实：三角相位只约束三边的乘积，零边会切断相位坐标，且局部半正定不保证整个矩阵半正定。$\square$

这个候选把用户的“顺序无关”改写成更准确的版本：比较点按什么顺序加入，得到的二元概率和任意已确定子集的 Gram 限制都一样；但沿三点闭路的相位可以留下 $\omega_{ijk}$。因此它既保留端点关系，又不把量子几何相位误判为公理违反。

从该候选到现有量子力学公理的桥是分层的。定理 20.2 只给 Hilbert 射影运动学和真实的 Gram 向量候选，不给相干制备权限。要得到 Born 规则，还需正效应、凸状态和非上下文可加赋值；维数至少三时可接 Gleason 型定理，二维情形仍需 Busch/POVM 或连续性条件。要得到 Wigner，需射影射线之间的双射并保持 $p_{ij}$。要得到 Stone，需物理时间上的强连续一参数酉群及自伴生成元域。张量积需要独立系统的共同联合核和局部组合律；CP/Kraus、全输出更新、Lüders、完整合法历史和真实 CountRead 仍需各自的动态接口；能量和物理钟仍需共同正 $\hbar$ 与生成元的共同定义域。

**定理 20.5（当前量子候选的严格范围）。** 共同正射影比较核足以给出有限 Hilbert 射影表示、规范不变量的转移概率以及满足四面体恒等式的 Bargmann 相位；它不足以单独推出 Born、Wigner、Stone、张量、CP/Kraus、更新、完整历史或物理时钟。它相对于严格平坦比较的改进，是把非零三角相位作为内生关系保留；它相对于完整量子力学的缺口，是尚未提供正效应、联合系统和动力学。$\square$

白话说：每两个对象先给出一张“相似度”和一支带相位的箭头，但所有箭头必须来自同一张半正定总表。你按什么顺序把对象放进来，已经出现的子表都不变；绕三角形走一圈时，可能多出一个不可消掉的相位，这正是量子几何，而不是错误。总表能分解成 Hilbert 向量，才有量子态的空间；概率读出、系统合并、测量更新和时间演化仍要另接桥。这个候选比“所有三角都严格闭合”更接近量子，也明确显示二元可比性本身不会自动产生全部量子力学。

## 追加锚（本行以下为增补区）
## 21. 从共同正核到 Born 的最小效应桥

共同正射影比较核给出射影线和转移概率，但没有告诉我们一个准备如何给效应赋概率。把 Born 规则直接写成 $\nu(E)=\operatorname{Tr}(\rho E)$ 会把结论当前件。更小的桥是要求效应的可加赋值：互斥效应的概率只按它们的和相加。这个桥的几何对象是 Hilbert 空间上的效应区间，而不是额外指定一条动力学。

**定义 21.1（有限效应赋值）。** 在有限维 Hilbert 空间 $H$ 上令

$$
\mathcal E(H)=\{E\in\operatorname{Herm}(H):0\le E\le I\}.
$$

一个归一化效应赋值是函数 $\nu:\mathcal E(H)\to[0,1]$，满足：

1. $\nu(I)=1$；
2. 若 $E,F,E+F\in\mathcal E(H)$，则 $\nu(E+F)=\nu(E)+\nu(F)$；
3. 对每个效应 $E$，标量函数 $t\mapsto\nu(tE)$ 在 $[0,1]$ 上连续。

第 3 条是有限维证明所需的最小显式正则性；Busch 型效应 Gleason 定理把它替换为对整个效应区间的有界有限可加条件。若一组效应 $\{E_a\}$ 满足 $\sum_aE_a=I$，则称它为一个 POVM 菜单，$\nu$ 的输出概率为 $\nu(E_a)$。

**定理 21.2（效应可加性导出 Born 赋值）。** 若 $\dim H\ge3$，每个归一化效应赋值 $\nu$ 都存在唯一密度算子 $\rho$ 使

$$
\nu(E)=\operatorname{Tr}(\rho E)
\qquad(E\in\mathcal E(H)).
$$

于是每个 POVM 菜单都给出归一化概率 $\sum_a\nu(E_a)=1$。

**证明。** 先把 $\nu$ 限制在正交投影上。对任意正交投影分解 $I=P_1+\cdots+P_m$，可加性给出 $\sum_i\nu(P_i)=1$；特别地，秩一投影上的函数是一个非负 frame function。$\dim H\ge3$ 时，Gleason 定理给出唯一密度算子 $\rho$，使得 $\nu(P)=\operatorname{Tr}(\rho P)$ 对所有投影 $P$ 成立。

若 $E=\sum_i\lambda_iP_i$ 是谱分解，其中 $0\le\lambda_i\le1$ 且 $P_i$ 两两正交，则可加性给出

$$
\nu(E)=\sum_i\nu(\lambda_iP_i).
$$

由第 2 条先对有理数 $\lambda_i$ 得 $\nu(\lambda P)=\lambda\nu(P)$；第 3 条再把它延拓到所有实 $\lambda\in[0,1]$。故

$$
\nu(E)=\sum_i\lambda_i\operatorname{Tr}(\rho P_i)
=\operatorname{Tr}(\rho E).
$$

若 $\rho,\sigma$ 给出同一赋值，则 $\operatorname{Tr}((\rho-\sigma)P)=0$ 对所有秩一投影成立；谱分解或极化恒等式遂得 $\rho=\sigma$。POVM 的归一化由线性迹和 $\sum_aE_a=I$ 立即得到。$\square$

**命题 21.3（为什么这仍是关系理论的内生桥）。** 共同正射影核供应秩一投影的候选集合及其 Gram 几何；效应赋值只规定这些投影和其正区间如何共同读出。它没有预先指定 $\rho$ 或迹公式，而是由所有互斥效应的加法关系迫使出一个唯一的正线性泛函。因而这一桥把“比较结构”提升为“概率结构”，但没有增加时间、复合或仪器更新。

二维和无限维边界必须保留。只在二维 Hilbert 空间的投影集合上要求正交基和为一，存在非 Born 的 frame function；Busch 型结果使用整个效应区间的有界可加性来消除这个自由。无限维情形若要得到密度算子而不是奇异态，还需适当的可数可加性或 normality。若只给共同正核而不供应效应赋值，Born 仍然没有推出；若只要求不相容效应之间的局部加法，谱分解的延拓也未付。

**定理 21.4（本轮桥的严格范围）。** 共同正射影比较核加上定义 21.1 的效应赋值，在有限维 $\dim H\ge3$ 时推出 Born 概率和唯一密度算子；它仍不足以推出 Wigner 变换（还需保持射影转移概率的双射）、Stone 时间演化（还需强连续一参数群）、张量积（还需联合效应代数）、CP/Kraus 仪器和更新（还需全输出通道及状态转移）。这减少的是“直接另立 Born 公理”的负担，不是把概率、复合和动力学全部从二元比较中免费推出。$\square$

白话说：正核先给出一张共同的 Hilbert 几何地图，但地图本身没有概率。再要求互相排斥的效应合起来时，概率也按加法合起来；在三维以上，这个规则会强迫所有读数都等于某个密度矩阵的迹。于是 Born 规则成为“共同正核加效应加法”的定理。二维投影、无限维奇异态、张量复合、测量更新和时间演化仍是清楚分开的后续桥梁。

## 追加锚（本行以下为增补区）

## 22. 顺序无关的正比较公理

前两章把共同正核和效应赋值分开。现在把用户提出的直觉压成一个更短的候选：比较可以逐对进行，但任何有限次逐对比较都必须来自同一个非负二次型；因此先加入哪一个点、先删去哪一个点，都不会改变已经确定的比较结果。这里的“顺序无关”只管比较数据的限制与共同实现，不把不同物理操作声明为可交换。

**定义 22.1（顺序无关正比较系统）。** 设 $X$ 是对象集。对每个有限有序表 $F=(x_1,\ldots,x_n)$，给出矩阵 $K_F\in\mathbb C^{n\times n}$，并要求：

1. $K_F=K_F^*$ 且 $(K_F)_{ii}=1$；
2. 对每个子表和每个置换，限制相容：删去若干位置所得矩阵是主子矩阵，重排位置所得矩阵是相应的置换共轭；
3. 对所有 $c\in\mathbb C^n$，有
   $$
   c^*K_Fc\ge0.
   $$

把 $K(x_i,x_j):=(K_F)_{ij}$ 记作逐对比较。第 2 条使这个记号与选取的有限表无关；第 3 条是“这些两两比较可以共同实现”的唯一额外约束。

**定理 22.2（顺序无关正比较等价于 Hilbert 实现）。** 定义 22.1 等价于存在 Hilbert 空间 $H$ 和映射 $\phi:X\to H$，满足

$$
K(x,y)=\langle\phi(x),\phi(y)\rangle,\qquad \|\phi(x)\|=1.
$$

在由所有 $\phi(X)$ 张成的最小闭子空间上，这个实现只差一个唯一的酉变换。

**证明。** 由限制相容性，$K$ 是 $X$ 上的 Hermitian 核。令 $\mathbb C_0^{(X)}$ 为有限支撑形式和，定义

$$
\left\langle\sum_i a_i\delta_{x_i},\sum_j b_j\delta_{y_j}\right\rangle
 =\sum_{i,j}\overline{a_i}b_jK(x_i,y_j).
$$

正性使它成为半内积；商去零范数向量并完备，得到 Hilbert 空间 $H$。令 $\phi(x)$ 为 $\delta_x$ 的等价类，则 $\langle\phi(x),\phi(y)\rangle=K(x,y)$，且 $K(x,x)=1$ 给出单位长度。反向由 Gram 矩阵的恒等式

$$
\sum_{i,j}\overline{c_i}c_j\langle\phi(x_i),\phi(x_j)\rangle
=\left\|\sum_i c_i\phi(x_i)\right\|^2\ge0
$$

立即成立。若 $\phi$ 与 $\psi$ 给出同一核，在有限线性组合上定义 $\sum_i c_i\phi(x_i)\mapsto\sum_i c_i\psi(x_i)$；相同的 Gram 值保证它良定义且保持内积，故在最小闭包之间延为唯一酉变换。证毕。

这一定理给出本轮最简几何结构：对象是复 Hilbert 球面上的单位向量，物理上只能看到射影线 $[\phi(x)]$。二元概率是

$$
p(x,y)=|K(x,y)|^2,
$$

而三元闭路保留

$$
B(x,y,z)=K(x,y)K(y,z)K(z,x).
$$

$B$ 的相位在逐点相位变换 $\phi(x)\mapsto e^{i\theta_x}\phi(x)$ 下不变。因而“顺序无关”表现为同一 Gram 核的限制相容；相位不是顺序误差，而是射影几何的内生量。

**定理 22.3（三点的最小三维提升）。** 设三个对象的非对角比较为

$$
K=\begin{pmatrix}
1&a&\overline c\\
\overline a&1&b\\
c&\overline b&1
\end{pmatrix},
$$

其中 $a=K_{12}$、$b=K_{23}$、$c=K_{31}$。它们有共同 Hilbert 实现，当且仅当

$$
|a|,|b|,|c|\le1,\qquad
1-|a|^2-|b|^2-|c|^2+2\operatorname{Re}(abc)\ge0.
$$

若 $a,b,c$ 都非零，写 $abc=|abc|e^{i\vartheta}$，则第二个条件是

$$
1-r_{12}^2-r_{23}^2-r_{31}^2
+2r_{12}r_{23}r_{31}\cos\vartheta\ge0.
$$

**证明。** $2\times2$ 主子式给出三个模长条件；$3\times3$ 行列式正好等于第二个表达式。Hermitian $3\times3$ 矩阵半正定当且仅当所有主子式非负，故结论成立。证毕。

这个三点条件是一个真正的有限三维提升：模长给出三条边，$\vartheta$ 给出三角形的射影扭转，行列式是三向量张成体积的平方。行列式为零时三向量退化到二维子空间；严格为正时出现新的独立方向。若只给 $p_{ij}=r_{ij}^2$ 而不保留 $\vartheta$，就不知道三点能否放进同一个 Hilbert 几何中。

**命题 22.4（为什么“仅两两可比”还不够）。** 逐边满足 $2\times2$ 正性不能保证共同来源。取

$$
K=\begin{pmatrix}
1&0.9&0.9\\
0.9&1&-0.9\\
0.9&-0.9&1
\end{pmatrix}.
$$

每条边的 $2\times2$ 主子式均为 $0.19>0$，但

$$
\det K=1-3(0.9)^2-2(0.9)^3<0.
$$

所以任意一对都可比较，却没有一个共同 Hilbert 实现。必须把“两两可比”提升为“所有有限两两比较共同正定”。反过来，若把顺序无关误写成数值乘法 $K(x,z)=K(x,y)K(y,z)$，则所有比较退化为秩一的严格平坦层，量子相位和干涉自由度被错误删除。

从这个单一候选到现有量子力学公理的路线现在可以写得很短：定理 22.2 给出 Hilbert 射影运动学；定理 22.3 给出最小三维相位兼容条件；在有限维至少三维时，叠加效应的归一化可加性接上第 21 章并推出 Born 规则。Wigner 还需要保持射影转移概率的双射，Stone 还需要物理时间上的强连续一参数酉群；张量积需要联合核及系统组合律；CP/Kraus 和 Lüders 需要完整输出通道及更新规则。这些不是同一条“顺序无关”公理的隐藏结论。

**定理 22.5（本轮候选的范围）。** 顺序无关正比较公理等价于一个归一化正定核，因而足以构造最小 Hilbert 实现并保留 Bargmann 相位；它不足以单独推出 Born 以外的概率、系统张量、动力学、测量更新或物理时钟。若再加入第 21 章的效应可加桥，则在有限维 $\dim H\ge3$ 时得到 Born 赋值。证毕。

白话说：世界先只承认“两个对象怎么比较”，但要求所有这些二元结果能同时放进一张不产生负平方长度的总表。于是你先比较甲乙再加入丙，或先比较乙丙再加入甲，已经确定的结果都不变；这张表会自动长成一个 Hilbert 空间。三点时，三条边的长度还不够，还要有一个绕三角形的相位；行列式就是三维几何是否真的能拼起来的检查。若把顺序无关误解为每次操作都能交换，会得到过强的经典平坦结构；真正简洁的公理是“共同正定的比较核”。


## 23. 内生正比较状态公理

第 22 章给出了量子几何的最小二元关系。若希望把 Born 读出也放进同一个关系对象，最短的数学压缩是把比较对象扩展为一个带乘法和伴随的观测代数。这个候选的代价是前提更强：它统一了两个桥梁，却没有消除线性、事件组合和正性的内容。

**定义 23.1（内生正比较状态公理）。** 设 $\mathcal A$ 是带单位 $1$ 的复 $C^*$-代数。一个内生正比较是二元函数

$$
C:\mathcal A\times\mathcal A\longrightarrow\mathbb C
$$

满足：

1. $C$ 对第一变量共轭线性、对第二变量线性，并且
   $$
   C(a,b)=\overline{C(b,a)};
   $$
2. $C(1,1)=1$；
3. 对任意有限族 $a_1,\ldots,a_n$ 和 $z_1,\ldots,z_n\in\mathbb C$，
   $$
   \sum_{i,j}\overline{z_i}C(a_i,a_j)z_j\ge0;
   $$
4. 比较与代数乘法相容：
   $$
   C(ab,c)=C(b,a^*c).
   $$

第 4 条只要求同一乘积的括号和比较方式相容，不要求 $ab=ba$。因此它保留了物理操作的非交换性；“顺序无关”仍然只指有限比较表的重排与限制。

**定理 23.2（比较状态与正泛函等价）。** 定义 23.1 等价于存在唯一归一化正线性泛函 $\omega:\mathcal A\to\mathbb C$，使

$$
C(a,b)=\omega(a^*b).
$$

进一步，存在 Hilbert 空间 $H_\omega$、表示 $\pi_\omega:\mathcal A\to\mathcal B(H_\omega)$ 和循环单位向量 $\Omega_\omega$，满足

$$
\omega(a)=\langle\Omega_\omega,\pi_\omega(a)\Omega_\omega\rangle,
\qquad
C(a,b)=
\langle\pi_\omega(a)\Omega_\omega,\pi_\omega(b)\Omega_\omega\rangle.
$$

**证明。** 定义 $\omega(a):=C(1,a)$。取第 4 条中的 $a$ 为原来的 $a$、$b=1$、$c=b$，得到

$$
C(a,b)=C(1,a^*b)=\omega(a^*b).
$$

于是

$$
\omega(1)=1,\qquad
\omega(a^*a)=C(a,a)\ge0.
$$

所以 $\omega$ 是归一化正泛函；在 $C^*$-代数上它自动连续且范数为 $1$。反向地，任意这样的 $\omega$ 定义 $C(a,b)=\omega(a^*b)$，立即满足四条公理。对 $\omega$ 的零范数左理想作商并完备，令 $\pi_\omega(a)[b]=[ab]$，$\Omega_\omega=[1]$，即得所述 GNS 表示。唯一性是循环表示在酉等价意义下的唯一性。证毕。

这一定理说明：第 22 章的正定核不是被删除，而是变成

$$
K(a,b)=C(a,b)=\omega(a^*b)
$$

的特殊情形。比较关系、Hilbert 几何和代数作用由同一个二元对象承载。

**定理 23.3（Born 读出作为比较的对角值）。** 对任意效应 $0\le E\le1$，定义

$$
p(E):=\omega(E).
$$

则 $0\le p(E)\le1$。若 $E_1,\ldots,E_m$ 是有限 POVM，满足 $\sum_iE_i=1$，则

$$
\sum_i p(E_i)=1.
$$

若 $\mathcal A=M_d(\mathbb C)$，则存在唯一密度矩阵 $\rho$，使

$$
p(E)=\operatorname{Tr}(\rho E).
$$

**证明。** $E\ge0$ 且 $1-E\ge0$，正性给出

$$
0\le\omega(E)\le\omega(1)=1.
$$

线性给出 POVM 的归一化。有限维时，线性泛函在矩阵单位基下可唯一写成 $\omega(A)=\operatorname{Tr}(\rho A)$；对所有 $A^*A$ 的正性迫使 $\rho\succeq0$，而 $\omega(1)=1$ 迫使 $\operatorname{Tr}\rho=1$。反向由迹的正性成立。证毕。

因此在这个候选中，Born 公式不是另加的数值规则，而是同一正比较状态对效应的对角读出。它绕开了 Gleason 的投影维数门槛，但代价是先假定了事件所在的 $C^*$-代数和乘法兼容性。

**定理 23.4（三点提升与全局边界仍然存在）。** 对三个比较元素，令

$$
a=C(x,y),\qquad b=C(y,z),\qquad c=C(z,x).
$$

共同实现的三点条件仍为

$$
1-|a|^2-|b|^2-|c|^2+2\operatorname{Re}(abc)\ge0.
$$

逐边条件不能替代它。例如

$$
K=
\begin{pmatrix}
1&0.9&0.9\\
0.9&1&-0.9\\
0.9&-0.9&1
\end{pmatrix}
$$

的每个二阶主子式都是 $0.19>0$，但

$$
\det K=1-3(0.9)^2-2(0.9)^3<0.
$$

即使所有三点子矩阵都正，也不能自动推出任意更大矩阵正。四点矩阵

$$
G_{ij}=
\begin{cases}
1,&i=j,\\
-\frac12,&i\ne j
\end{cases}
$$

的每个三点主子矩阵半正定，但 $G$ 的特征值包含 $-\frac12$。所以内生正比较公理仍必须对所有有限比较族施加正性；三维条件只是最小可检验投影。

**定理 23.5（候选的严格范围）。** 内生正比较状态公理足以推出：

- 最小 GNS Hilbert 表示和射影比较几何；
- 二元转移概率与 Bargmann 相位；
- $C^*$-代数效应的正概率；
- 有限矩阵代数中的 Born 迹公式。

它仍不足以单独推出 Wigner 对称（还需保持转移概率的射影双射）、Stone 时间演化（还需强连续的一参数自伴群）、张量积系统（还需 $C^*$-张量积与组合律）、CP/Kraus 仪器（还需完全正映射和输出守恒）、Lüders 更新或物理时钟。若状态对一族强连续的保状态 $*$-自同构不变，GNS 表示可得到酉实现；强连续性和生成元仍是额外条件。证毕。

这一候选是否“更简单”，必须分两层回答。作为数学包装，它把第 22 章的正核与第 21 章的效应赋值写成一个二元形式 $C(a,b)=\omega(a^*b)$。作为基础假设，它更强，因为它预先要求复线性、单位、乘法、伴随和 $C^*$-范数。因而它是**更统一的单一结构**，不是已经证明的**更少前提理论**。真正更简的开放目标，是只给准备与事件之间的原始二元关系 $R(x,E)$，从限制相容、有限正性、事件合成和完备归一化中反向构造 $\mathcal A$；如果不能构造，失败点就精确说明事件结构为何不可省略。

白话说：先前我们只有一张“对象之间的相似度总表”，它长成 Hilbert 空间，但还没有测量。现在把“对象”和“事件”都放进同一间带乘法的房间，比较两件东西的结果必须等于先取伴随再相乘后的正读数。这个统一关系自动长成 GNS Hilbert 空间；事件的对角读数就是 Born 概率。它把两座桥合成一座，但房间本身的墙——线性、乘法、伴随和正性——仍然是明确付出的前提。下一步真正困难的地方，是不用先给这间房子，直接从准备—事件的两两比较把房子建出来。


## 24. 准备—事件二元关系的不可压缩边界

第 23 章把事件域放进 $C^*$-代数，因而统一了 Hilbert 几何和 Born 读出。现在反向减去这层代数结构，检验用户所说的“只保留两两比较”能否仍然完成重建。结论是：若比较只记录准备与事件之间的实数读数，量子相位无法从中恢复；必须额外保留相位型准备—准备比较或等价的干涉操作。

**定义 24.1（准备—事件读数关系）。** 设 $P$ 是准备集合，$\mathcal E$ 是带 $0,1$ 和部分和 $\oplus$ 的有限效应系统。一个实读数关系是

$$
R:P\times\mathcal E\longrightarrow[0,1]
$$

并满足：

1. $R(x,1)=1$、$R(x,0)=0$；
2. 若 $e\oplus f$ 有定义，则
   $$
   R(x,e\oplus f)=R(x,e)+R(x,f);
   $$
3. 对事件的重排、分块和细化，读数保持相同。

这正是“准备和事件两两可比较，且比较次序无关”的实数版本。

**定理 24.2（实准备—事件关系不能识别量子相位）。** 仅给出定义 24.1 的 $R$，不能唯一确定准备之间的 Gram 核、Bargmann 相位或 Hilbert 维数。即使所有事件读数都已给定，也存在不同的量子几何产生同一份 $R$。

**证明。** 先取最小事件系统 $\mathcal E=\{0,1\}$。任何准备集合都只有同一份读数 $R(x,0)=0$、$R(x,1)=1$，但准备可以由任意数量、任意 Gram 相位的单位射线表示。特别地，三条射线可以取第 20 章的 $K_0$ 或 $K_\pi$；两者的三元 Bargmann 相位分别为 $1$ 和 $-1$，而 $R$ 完全相同。

增加一个有限 Boolean 事件表也不能修复这一点：若事件只读取一组固定正交分解，则 $R$ 只看到各准备密度矩阵的对角元。保持这些对角元而改变非对角相干，所有 $R(x,e)$ 不变。经典单纯形模型同样可以实现同一份有限实读数。故从 $R$ 无法反向唯一构造相位、共同 Gram 核或最小 Hilbert 维数。证毕。

因此，任何声称由“准备—事件实二元比较”单独推出完整量子几何的理论，都必须指出它的干涉信息藏在哪里；若没有额外操作或复值比较，它会被上述同读数模型反驳。

**候选 24.3（最小联合比较接口）。** 保留两种同一来源上的二元关系：

1. 准备—准备关系 $K:P\times P\to\mathbb C$，满足第 22 章的全有限正定和限制相容；
2. 准备—事件关系 $R:P\times\mathcal E\to[0,1]$，满足定义 24.1 的归一化与可加性。

再加入一条联合相容要求：对每个有限准备族，所有事件读数都由同一个正核实现，即存在同一个 Hilbert 表示和效应 $E_e$，使

$$
K(x,y)=\langle\psi_x,\psi_y\rangle,\qquad
R(x,e)=\langle\psi_x,E_e\psi_x\rangle.
$$

在这个候选下，三点正性仍由

$$
1-|K_{12}|^2-|K_{23}|^2-|K_{31}|^2
+2\operatorname{Re}(K_{12}K_{23}K_{31})\ge0
$$

检验；事件的 POVM 归一化给出 Born 概率。

这是一条完整但诚实的联合接口，却还不是更少前提的起源公理：最后一条已经把共同 Hilbert 实现写进了条件。真正未解的压缩问题是，能否只用 $K$、$R$ 的原始有限表、事件细化和干涉复合规则，证明这条共同实现，而不把它作为前提。若失败，定理 24.2 说明缺失的正是相位型关系；若成功，所得定理才会比第 23 章的 $C^*$-状态形式更基础。

**定理 24.4（本候选的范围）。** 候选 24.3 加上共同实现条件，足以给出 Hilbert 射影几何、Bargmann 相位、效应概率和有限维 Born 迹表达；它仍不推出 Wigner、Stone、张量积、CP/Kraus 或 Lüders 更新。若删去准备—准备的复关系 $K$，则定理 24.2 立即使量子相位重建失效。证毕。

白话说：只问“这个准备遇到这个事件会读出多少”，你得到的是一张概率表；概率表可以来自经典单纯形，也可以来自带不同相位的量子态。两者在固定事件菜单上完全一样。要看见量子，必须再保留“准备和准备之间怎样相干比较”的关系，或者保留一个等价的干涉实验。最小诚实候选因此是同一来源上的两种二元关系：复杂度没有消失，但缺口被准确定位在“事件读数如何读取准备之间的相位”。


## 25. Dagger 比较范畴的减法检验

把二元比较写成箭头和伴随，看起来比 $C^*$-代数更几何。必须先检验它是否真的减少了前提。下面的候选给出最强的直接结果，也显示它的代价。

**定义 25.1（正 Dagger 比较包）。** 取一个带单位对象 $I$ 的 Dagger 范畴 $\mathcal C$，并要求：

1. 每个 $\operatorname{Hom}(I,A)$ 是有限维复向量空间，复标量由 $\operatorname{End}(I)=\mathbb C$ 给出；
2. 伴随满足 $(g\circ f)^\dagger=f^\dagger\circ g^\dagger$，且 $x^\dagger y\in\mathbb C$ 对所有态射 $x,y:I\to A$；
3. 有限 Dagger 双积和双线性复合存在；
4. 效应是端omorphism $0\le E\le1_A$，准备箭头 $x:I\to A$ 归一化为 $x^\dagger x=1$；
5. 正性按 $x^\dagger E x\ge0$ 和 $x^\dagger(1_A-E)x\ge0$ 定义。

这是一条将准备、比较和事件写入同一箭头系统的候选公理。

**定理 25.2（正 Dagger 包的直接后果）。** 对每个对象 $A$，空间

$$
V_A=\operatorname{Hom}(I,A)
$$

带有内积

$$
\langle x,y\rangle=x^\dagger y.
$$

它是有限维 Hilbert 空间。对归一化准备 $x$ 和效应 $E$，

$$
p_x(E)=x^\dagger E x
$$

属于 $[0,1]$；若 $E_i$ 是有限 POVM，$\sum_iE_i=1_A$，则

$$
\sum_i p_x(E_i)=1.
$$

**证明。** Dagger 公理给共轭对称性和复线性；$x^\dagger x\ge0$ 且零范数商掉后得到内积空间。有限维自动完备。效应正性给 $0\le x^\dagger E x$ 与 $x^\dagger(1_A-E)x$，故 $0\le p_x(E)\le1$；双线性和单位分解给 POVM 归一化。证毕。

这一定理确实同时产生 Hilbert 比较和 Born 型效应读数，但它的关键前提已经是复向量空间、单位、Dagger、效应序和正性。它是第 23 章正比较状态的范畴化表达，不是更少前提的起源证明。

**命题 25.3（Dagger 结构本身不足以选出量子几何）。** 仅要求 Dagger 范畴、甚至对称 Dagger 紧范畴，不能推出复 Hilbert 空间或 Born 规则。

**证明。** 有限集合与关系构成 Dagger 紧范畴 $\mathbf{Rel}$：伴随是关系反转，复合是关系复合，紧结构由关系对偶给出；其标量是布尔真值，没有连续复相位和正半定 Gram 理论。有限维实矩阵范畴与复矩阵范畴也都具有转置或共轭转置 Dagger，但前者没有复 Bargmann 相位。故 Dagger、紧性和图式顺序相容本身不能选出 $\mathbb C$、Hilbert 正性或 Born 读数。证毕。

三点检验仍然是同一个行列式：

$$
1-|K_{12}|^2-|K_{23}|^2-|K_{31}|^2
+2\operatorname{Re}(K_{12}K_{23}K_{31})\ge0.
$$

若要从范畴得到它，必须已经要求态射空间的复内积和正性；若还要得到真实系统复合，则需单体积与独立组合律。Wigner、Stone、CP/Kraus、Lüders 和物理时钟仍分别需要对称双射、强连续时间、完全正映射、更新原则和时钟生成元。因而 Dagger 候选的严格结论是：它提供一种统一记号和组合语言，但不减少已识别的数学桥梁。

白话说：把比较画成箭头、把反向箭头叫伴随，图会更漂亮，但图本身没有告诉我们箭头的长度是不是平方长度，也没有告诉我们相位为什么是复数。只要补上复线性、正性和效应，就已经把 Hilbert 空间和 Born 规则放进公理了。范畴语言能整理关系，却不能凭语言消除关系所需的信息。

## 追加锚（本行以下为增补区）

## 28. 把事件桥压成一条正交框架归一化律

第 27 节已经从二次自比较得到 Hilbert 几何，但 Born 规则仍以事件桥为前提。再做一次减法：不先给效应代数，只要求每个正交测量框架的读数总和为一，并且读数只看同一个二元比较的模平方。

**定义 28.1（二次框架读出公理）。** 设 $H$ 是由定义 27.1 的二次律得到的 Hilbert 空间，$\psi\in H$ 为单位准备，$e$ 为单位事件射线。要求存在同一个函数

$$
g:[0,1]\longrightarrow[0,1]
$$

使每个秩一事件的读数为

$$
p_\psi(e)=g\!\left(|\langle e,\psi\rangle|^2\right),
$$

并满足 $g(0)=0$、$g(1)=1$。对任意有限维正交框架 $C=(e_1,\ldots,e_d)$（$d\ge3$）要求

$$
\sum_{i=1}^{d}p_\psi(e_i)=1,
$$

且 $g$ 与准备、框架次序和框架的其他上下文无关。这是唯一新增的事件层公理；没有预先指定投影、效应或概率测度。

**定理 28.2（平方律由框架归一化强迫）。** 定义 28.1 必然有

$$
g(t)=t\qquad(0\le t\le1).
$$

因此

$$
p_\psi(e)=|\langle e,\psi\rangle|^2.
$$

**证明。** 给定任意 $x,y\ge0$ 且 $x+y\le1$，可在三维框架中选取单位准备，使三个重叠平方为 $x,y,1-x-y$。同一个准备也可在另一个框架中使三个重叠平方为 $x+y,0,1-x-y$。两次归一化相减，利用 $g(0)=0$，得到

$$
g(x)+g(y)=g(x+y).
$$

所以 $g$ 在 $[0,1]$ 上可加。它取值于 $[0,1]$，因而有界；有界可加函数在该区间上必为线性函数。由 $g(1)=1$ 得 $g(t)=t$。证毕。

**定理 28.3（从框架读出到现有量子测量公理）。** 对任意正交投影 $P_E$，取其像空间的正交基 $(e_i)$，定义

$$
p_\psi(E):=\sum_{e_i\in E}|\langle e_i,\psi\rangle|^2.
$$

Parseval 恒等式使该定义与所选基无关，并给出

$$
p_\psi(E)=\langle\psi,P_E\psi\rangle,
\qquad
p_\psi(I)=1,
$$

以及互斥投影的有限可加性。对有限 POVM $E_i\ge0$、$\sum_iE_i=I$，谱分解和线性延拓给出

$$
\sum_i\langle\psi,E_i\psi\rangle=1.
$$

若把一般效应识别为 $H$ 上的正算子，并采用其谱分解的线性延拓，则

$$
\sum_i\langle\psi,E_i\psi\rangle=1
$$

对有限 POVM $E_i\ge0$、$\sum_iE_i=I$ 成立；对混合态按凸组合延拓，得到 $p_\rho(E)=\operatorname{tr}(\rho E)$。所以正交投影的 Born 公理直接由“二次比较 + 正交框架总量为一”推出，一般 POVM 还承担了“效应是正算子”的识别桥；平方模不是另加的数值猜测，而是框架相容性强迫的唯一函数。

**命题 28.4（事件桥仍有明确边界）。** 若去掉同一个 $g$ 的上下文独立性，可为不同框架任意指定读数，无法得到非情境 Born 规则；若只允许二维框架，归一化只给出 $g(t)+g(1-t)=1$，不强迫 $g(t)=t$；若去掉正交框架的完备性，读数可以不归一。时间演化、张量积、完全正通道和 Lüders 更新仍未由本候选推出。

**候选 28.5（最简完整测量图景）。** 量子结构由两层组成：第一层是自由复关系空间上的非负二次律，它产生内积、相位和 Hilbert 状态；第二层只要求所有正交框架共享同一个归一化二次读出。第一层给出“能否相干比较”，第二层给出“比较如何成为投影概率”；把一般效应接成正算子是后续的线性扩展。框架元素的排列不影响总读数，单条振幅的相位仍通过三点 holonomy 保留干涉信息。

白话说：先让所有准备的合成长度服从平行四边形，得到一张带相位的 Hilbert 网；再规定任何完整的互相垂直的测量菜单，所有答案加起来都必须正好是一，而且同一答案只由它和准备的重叠大小决定。三维以上，这条规则会逼出唯一的平方律，所以 Born 概率不是外加的数字选择，而是正交菜单能够彼此兼容的结果。至于时间、复合系统和测量后的状态变化，仍需要更高层的公理。

## 29. 关系的关系：乘法比较与张量几何

第 28 节解决了单个系统的事件读出，仍没有说明两个系统怎样形成一个整体。只给两边各自的两两比较，联合关系并不唯一；最短的复合候选是把独立性的定义写成比较值的乘法。

**定义 29.1（独立复合的乘法比较公理）。** 设 $A,B$ 是两个已经带有二次自比较和正定核的系统。独立复合的准备对象写成 $(a,b)$，并要求

$$
\kappa_{A\boxtimes B}\bigl((a,b),(a',b')\bigr)
 =\kappa_A(a,a')\,\kappa_B(b,b').
$$

复合对象的有限形式和按双线性延拓；交换两个独立因子的映射

$$
\sigma(a,b)=(b,a)
$$

只改变标记，并满足

$$
\kappa_{B\boxtimes A}(\sigma x,\sigma y)=\kappa_{A\boxtimes B}(x,y).
$$

这是一条关于“比较如何组合”的公理，不先把张量积 Hilbert 空间写进定义。

**定理 29.2（乘法比较生成张量几何）。** 若 $K_A,K_B$ 是任意有限比较族的 Gram 矩阵，则复合族的 Gram 矩阵为

$$
K_{A\boxtimes B}=K_A\otimes K_B.
$$

因为 Kronecker 积保持正半定性，乘法比较公理保持全有限自比较正性。由第 27 节的极化和商完备化，复合空间的乘积子空间等距嵌入

$$
H_A\widehat\otimes H_B,
\qquad
[e_a]\otimes[f_b]\longmapsto[(a,b)].
$$

交换因子由酉 flip 实现。若 $(e_i)$、$(f_j)$ 是两边的正交框架，则

$$
p_{\psi\otimes\phi}(e_i\otimes f_j)
 =|\langle e_i,\psi\rangle|^2|\langle f_j,\phi\rangle|^2,
$$

且对 $(i,j)$ 求和为 $1$。第 27 节的自由复线性闭包允许

$$
\Psi=\sum_{i,j}c_{ij}\,e_i\otimes f_j
$$

这样的非可分离准备；对它应用第 28 节的框架律，就得到纠缠态的联合平方读出。证毕。

**命题 29.3（边缘比较不能决定联合关系）。** 取两个二元读口 $X,Y$，令两者边缘都为均匀分布。联合表

$$
J_{\rm ind}(x,y)=\frac14\quad\text{(四格均等)},
$$

和

$$
J_{\rm corr}(0,0)=J_{\rm corr}(1,1)=\frac12,
\qquad
J_{\rm corr}(0,1)=J_{\rm corr}(1,0)=0
$$

具有完全相同的边缘两两读数，却有不同的联合相关。故“每个子系统都可比较”与“交换读口次序不改变边缘”不能推出复合关系；乘法独立律正是把缺失的联合约束写出来。若把独立复合改成加法，单位比较立即给出 $\kappa_{A\boxtimes B}((a,b),(a,b))=2$，破坏归一化。证毕。

**定理 29.4（对现有量子公理的对应）。** 乘法比较公理与前两层结合后给出：

1. 纯积态的张量积几何和因子交换的酉对称；
2. 产品测量框架的联合 Born 概率及其边缘归一化；
3. 复线性闭包中的纠缠态和非因子化联合振幅；
4. 在把混合态识别为密度算子后，局部投影读出的求和给出标准边缘态和无信号结论。

它仍不推出局部层析（局部产品读数是否足以区分所有整体态）、一般完全正通道、时间演化、测量更新或物理上的独立性判据。特别是，乘法律本身只描述被声明为独立的复合；它没有证明自然界中哪些系统真的独立。

**候选 29.5（最简关系网络几何）。** 单系统是非负二次比较空间；独立复合把比较值按乘法组合，因而在几何上形成带酉 flip 的对称单体结构。边是比较，三边 holonomy 是相位，乘法复合是关系的关系，正交框架是概率读口。张量积不是外部输入，而是乘法比较在 GNS 完备化后的几何影像；局部层析和动力学则是更高层约束。

白话说：两个系统各自会比较，还不能说明它们合在一起怎样比较；同样的两张边缘表，可以拼成独立的联合，也可以拼成强相关的联合。最短的独立性规则是“合在一起的比较等于两边比较相乘”。这条规则会自己长出张量积、产品 Born 概率和纠缠的线性空间，但不会凭空告诉我们什么是物理独立、怎样随时间演化或测量后如何更新。

## 30. 比较保持流：从顺序无关关系到酉动力学

前面几节已经给出态、读出和独立复合；剩余的时间问题可以反过来问：时间是否只是保持所有两两比较的连续变换？如果是，Hamiltonian 应该是这种变换的生成元，而不是外部输入。

**定义 30.1（比较保持流公理）。** 令 $\mathbb P(H)$ 为 Hilbert 空间的射影单位向量空间，定义转移比较

$$
r([\psi],[\phi])=|\langle\psi,\phi\rangle|^2.
$$

一个时间流是映射 $T:\mathbb R\times\mathbb P(H)\to\mathbb P(H)$，满足

$$
T_0=\mathrm{id},\qquad T_{t+s}=T_t\circ T_s,
$$

每个 $T_t$ 是双射，并且

$$
r(T_t[\psi],T_t[\phi])=r([\psi],[\phi]).
$$

另要求 $t\mapsto T_t[\psi]$ 对每个射影态连续；在无限维情形，选择代表向量时要求得到强连续的局部提升。公理只说时间保持比较，不预设 $U_t$ 或 Hamiltonian。

**定理 30.2（Wigner–Stone 重建）。** 在 $\dim H\ge2$ 且满足定义 30.1 时，每个 $T_t$ 由一个酉或反酉算子 $U_t$ 在射影空间上的作用给出。连续性和 $T_0=\mathrm{id}$ 排除反酉分支；在连续相位选择下可取

$$
U_{t+s}=U_tU_s,
\qquad U_0=I.
$$

若该提升强连续，则存在自伴算子 $H$ 使

$$
U_t=e^{-itH}.
$$

在 $H$ 的定义域上，态满足

$$
i\frac{d}{dt}\psi_t=H\psi_t.
$$

**证明。** 保持所有转移概率的射影双射由 Wigner 定理实现为酉或反酉算子。酉和反酉射影作用属于两个不连通分支；从 $T_0$ 出发的连续路径只能留在酉分支。射影群律可能先给出一个 $U(1)$ 二-cocycle，$\mathbb R$ 的连续相位可将其消去，得到严格的一参数酉群。Stone 定理把强连续一参数酉群唯一表示为 $e^{-itH}$，并给出最后的微分方程。证毕。

**命题 30.3（删去条件的反推）。**

1. 删去比较保持，射影球面的任意连续变形都可作为 $T_t$，例如改变 Bloch 球纬度的非等距映射；它没有酉实现。
2. 删去双射和群逆，振幅阻尼等不可逆 CP 半群仍可存在，但不能写成单一自伴 Hamiltonian 的酉流。
3. 删去连续性，可用 Hamel 基上的非连续加法函数构造保持比较的 $U_t=e^{-if(t)A}$；它没有强连续生成元，Stone 桥不能应用。
4. 删去群律，任意时间依赖的 $U_t$ 都可逐时保持比较，却不对应固定 Hamiltonian。

**定理 30.4（对现有动力学公理的对应）。** 比较保持流自动保持第 28 节的正交框架总量和 Born 概率。若两个独立系统还满足因子相容

$$
U_t^{A\boxtimes B}=U_t^A\otimes U_t^B,
$$

则产品比较和局部读出同时保持；若允许相互作用，整体仍由 $H_{AB}$ 生成，但因子化本身不再成立。开放系统的完全正通道、测量后的 Lüders 更新、耗散半群和局域因果约束，都不是比较保持流的推论。

**候选 30.5（最简动力学几何）。** 时间是正比较网络射影空间上的连续自同构群；酉算子是保持所有二元比较的坐标表达，Hamiltonian 是该群的无穷小生成元。时间反演可以作为离散的反酉对称出现，但它不是从单位元连续长出的动力学分支。

白话说：如果时间只是把整张“相似度网”连续地搬动，而且任何两态的比较结果都不变，那么这种搬动只能是酉搬动；连续地一圈一圈搬，就必然有一个自伴生成元，也就是 Hamiltonian。放弃可逆性会得到开放系统，放弃连续性会失去生成元，放弃群律会失去单一时间演化方程；这些边界不能被同一条比较公理掩盖。

## 31. 完全比较保持：从联合正性到量子通道

第 29 节说明辅助系统是关系的关系；第 30 节只处理可逆流。对一般变换，最短的开放系统候选是：变换必须在加入任意独立辅助系统后仍保持联合自比较非负。

**定义 31.1（完全比较保持公理）。** 令 $A,A'$ 为有限维比较系统，$\Phi_A$ 为其算子比较空间上的线性变换。称 $\Phi_A$ 合法，当且仅当对每个有限维辅助系统 $B$ 和每个联合正算子 $X\succeq0$，都有

$$
(\Phi_A\otimes\mathrm{id}_B)(X)\succeq0,
$$

并且对所有 $X$ 保持迹：

$$
\operatorname{tr}\Phi_A(X)=\operatorname{tr}X.
$$

这里的正性是第 27 节二次自比较在算子层的延拓；“对所有 $B$”是独立复合律的关系版本，不直接把完全正性写成名称。

**定理 31.2（Choi–Kraus 重建）。** 定义 31.1 的正性条件等价于 $\Phi_A$ 完全正且迹保持。取一组基，定义 Choi 比较元

$$
C_\Phi=\sum_{i,j}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|).
$$

对最大纠缠向量的联合自比较给出 $C_\Phi\succeq0$；反向地，$C_\Phi\succeq0$ 的谱分解

$$
C_\Phi=\sum_\alpha\lambda_\alpha|v_\alpha\rangle\langle v_\alpha|
$$

把 $v_\alpha$ 重排为矩阵并吸收 $\sqrt{\lambda_\alpha}$，得到

$$
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
$$

迹保持恰好等价于

$$
\sum_\alpha K_\alpha^\dagger K_\alpha=I.
$$

因此 Kraus 表示是联合比较正性的坐标表达，而不是新的原始公理。证毕。

**命题 31.3（只保持局部正性的最小反例）。** 转置映射 $\tau(X)=X^{\mathsf T}$ 把单系统正算子送到正算子，但不是完全比较保持。对 Bell 态

$$
|\Omega\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2}
$$

有

$$
(\tau\otimes\mathrm{id})(|\Omega\rangle\langle\Omega|)
=\frac12
\begin{pmatrix}
1&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},
$$

其特征值为 $1/2,1/2,1/2,-1/2$。负特征值就是一个联合自比较为负的方向；所以单独检查每个系统不能保护关系的关系。

**定理 31.4（对现有开放量子公理的对应）。** 完全比较保持加迹保持给出标准量子通道。若把一个事件分支改为迹不增的完全比较保持映射 $\Phi_i$，并要求 $\sum_i\Phi_i$ 迹保持，则

$$
p_i=\operatorname{tr}\Phi_i(\rho),
\qquad
\rho_i=\frac{\Phi_i(\rho)}{p_i}
$$

给出仪器概率和条件态；第 30 节的酉流是只有一个 Kraus 算子的特殊情形。Lüders 形式

$$
\Phi_E(\rho)=\sqrt E\,\rho\,\sqrt E
$$

还需要重复性或最小扰动原则，不能从完全正性单独选出。无限维情形还需正规性和连续性条件，局部因果与 Markov 性也不由本候选自动产生。

**候选 31.5（最简开放系统几何）。** 正比较空间及其张量复合形成一个正锥网络；合法变换正是对所有辅助因子都保持正锥的线性箭头。Choi 矩阵是把“所有辅助关系”压缩到一个最大纠缠比较上的坐标，Kraus 向量是其谱分解。于是开放量子动力学仍由比较关系内生，但具体允许哪些通道和哪一种更新规则需要额外物理约束。

白话说：一个变换在自己身上看起来没把长度变成负数，还不够；把它接到任何另一个系统旁边，也不能制造负的联合长度，才是真正合法的量子通道。转置操作在单边检查时合格，一接 Bell 纠缠就出现负方向。这个“所有辅助系统都要通过”的规则会长出 Choi 矩阵和 Kraus 分解，但不会单独告诉我们测量后必须采用哪一种状态更新。

## 32. 锐事件的比较压缩与 Lüders 更新

第 31 节给出了所有合法通道，却没有选出一次锐测量后的具体状态。对投影事件 $P$，可以把更新写成一个更小的比较压缩条件：接受后进入 $P(H)$，而已经在 $P(H)$ 内的比较完全不变。

**定义 32.1（锐事件压缩公理）。** 令 $P=P^2=P^\dagger$ 为事件投影。一个分支变换 $\Phi_P$ 满足：

1. $\Phi_P$ 完全正且迹不增；
2. **投影效应：** $\Phi_P^*(I)=P$，等价于
   $$
   \operatorname{tr}\Phi_P(\rho)=\operatorname{tr}(P\rho);
   $$
3. **输出支撑：** $\Phi_P(\rho)=P\Phi_P(\rho)P$；
4. **接受子空间不扰动：** 若 $\sigma=P\sigma P$，则 $\Phi_P(\sigma)=\sigma$。

第四条是比较语言中的“条件化后保留已经满足条件的全部关系”，没有直接写入 $\sqrt P\rho\sqrt P$。

**定理 32.2（Lüders 规则的唯一性）。** 定义 32.1 唯一给出

$$
\Phi_P(\rho)=P\rho P.
$$

因此非归一化的条件态是 $P\rho P$，事件概率为 $\operatorname{tr}(P\rho)$；概率非零时归一化态为

$$
\rho_P=\frac{P\rho P}{\operatorname{tr}(P\rho)}.
$$

**证明。** 取 Kraus 表示 $\Phi_P(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger$。输出支撑对每个向量态都成立，故 $K_\alpha=PK_\alpha$。投影效应给出

$$
\sum_\alpha K_\alpha^\dagger K_\alpha=P,
$$

从而 $K_\alpha(I-P)=0$，即 $K_\alpha=K_\alpha P$。于是

$$
\Phi_P(X)=\Phi_P(PXP).
$$

第四条再给 $\Phi_P(PXP)=PXP$，合并即得 $\Phi_P(X)=PXP$。证毕。

**命题 32.3（重复结果本身不能选出 Lüders 更新）。** 只要求输出落在 $P(H)$、效应为 $P$，并且再次测量 $P$ 必然得到同一结果时，任意作用在 $P(H)$ 内的酉 $U$ 都给出合法分支

$$
\Phi_{P,U}(\rho)=U_P P\rho P U_P^\dagger,
\qquad U_P^\dagger U_P=U_PU_P^\dagger=P,
$$

其中 $U_P$ 是 $P(H)$ 上的酉，并以部分等距延拓到 $H$。

它保持事件概率和结果重复性，但除 $U= P$ 外不等于 Lüders 压缩。故“重复性”只约束事件标签，不约束接受子空间内的相位和比较；第四条不扰动条件正是缺失的选择原则。

**定理 32.4（对现有测量公理的对应与边界）。** 锐事件压缩公理给出投影测量的概率、非归一化分支和 Lüders 条件态；与第 31 节的完全正分支族组合，就得到量子仪器的锐测量特例。对一般效应 $0<E<I$，没有 $P(H)$ 支撑和重复性，$\sqrt E\rho\sqrt E$ 仍需最小扰动、连续性或仪器实现原则；退相干、选择性反馈和时间排序也不由本候选推出。

**候选 32.5（最简更新几何）。** 测量不是任意地把状态改写，而是沿事件投影压缩比较网络：先按 $P$ 取出分支权重，再把所有已在 $P(H)$ 内的关系原样保留。Lüders 更新是“正性 + 支撑 + 投影效应 + 接受内不扰动”的唯一坐标表达；其余仪器更新是允许在接受子空间内继续施加比较保持变换的更大类。

白话说：测到一个锐事件后，状态必须站进那个事件的子空间；如果它本来已经站在那里，就不能偷偷旋转、改相位或重新混合。Kraus 形式一展开，这四句话会把所有多余动作都消掉，只剩 $P\rho P$。只要求“下一次仍测到同一结果”还允许子空间里任意转圈，所以重复性本身不是 Lüders 规则。

## 33. 纯化闭包：混合比较是否只是更大纯比较的边缘

第 32 节选出了锐测量更新；混合态的来源还可以继续反问：混合比较是不是某个更大纯比较的边缘？这条原则在抽象重构中很短，但在已经得到的复 Hilbert 张量几何里可以被完整证明，因此它首先是一次减法检验。

**定义 33.1（纯化闭包候选）。** 对每个有限维系统 $A$ 的正比较状态 $\rho_A\succeq0$、$\operatorname{tr}\rho_A=1$，要求存在辅助系统 $B$ 和单位纯比较 $\Psi_{AB}$，使

$$
\rho_A=\operatorname{tr}_B|\Psi_{AB}\rangle\langle\Psi_{AB}|.
$$

在最小辅助维数 $\dim B=\operatorname{rank}\rho_A$ 下，要求同一 $\rho_A$ 的任意两种纯化只相差辅助系统上的酉比较保持：

$$
|\Phi_{AB}\rangle=(I_A\otimes U_B)|\Psi_{AB}\rangle.
$$

更大辅助空间中的两种纯化则只要求由辅助等距映射相连。

**定理 33.2（纯化存在与本质唯一性）。** 在第 29 节的复合张量几何中，定义 33.1 不需要新增公理。若

$$
\rho_A=\sum_{i=1}^{r}\lambda_i|i\rangle\langle i|,
\qquad \lambda_i>0,
\qquad \sum_i\lambda_i=1,
$$

取 $B$ 的正交基 $|i\rangle_B$，则

$$
|\Psi_{AB}\rangle=\sum_{i=1}^{r}\sqrt{\lambda_i}\,|i\rangle_A\otimes|i\rangle_B
$$

给出纯化。任意另一种最小纯化的 Schmidt 系数相同；Schmidt 基在简并子空间内的变化由一个辅助酉吸收，故两种纯化满足定义 33.1 的酉关系。证毕。

**定理 33.3（从纯化到谱、纠缠与 steering）。** 纯化闭包候选的几何后果是：

1. $\rho_A$ 的非零谱就是任一最小纯化的 Schmidt 权重；$\operatorname{rank}\rho_A=1$ 当且仅当纯化不纠缠；
2. 在 Schmidt 基上测量 $B$ 的投影 $|i\rangle\langle i|$，以概率 $\lambda_i$ 将 $A$ 条件化为 $|i\rangle_A$，并满足 $\sum_i\lambda_i|i\rangle\langle i|=\rho_A$；
3. 通过改变 $B$ 上的测量框架，可得到 $\rho_A$ 的其他凸分解。这是有限维 HJW steering 结论，来自同一纯化的辅助酉自由度。

因此混合态的密度算子、谱分解和远端条件化都可以看作一个更大纯比较网络的边缘读数；它们不是互不相干的概率表。

**命题 33.4（删去闭包条件的边界）。** 若不要求纯化存在，混合表可以被当作没有任何联合来源的原始经典不确定性，因而无法推出纠缠或 steering。若不要求最小纯化的辅助酉唯一性，抽象模型可以把同一边缘状态绑定到无法由辅助比较变换互相转换的额外标签；这种标签在边缘 Born 读数中不可见，却改变联合预测。故纯化唯一性是排除隐藏联合结构的条件，而在复 Hilbert 模型中它已由 Schmidt 定理自动满足。

**定理 33.5（对现有量子公理的对应与未证边界）。** 纯化闭包与前面的比较、框架和张量公理结合，给出密度算子作为纯态边缘、纠缠谱、steering 以及局部投影的边缘 Born 读数。若同时允许全部局部效应 $E\otimes F$，有限维线性代数还可证明局部层析；只有产品准备或不完整事件菜单时，局部层析仍是 open。纯化闭包不推出动力学与纯化相容性、通道的物理可实现性或相对论局域性。

**候选 33.6（最简混合几何）。** 混合不是新的基本点，而是纯比较网络沿一个辅助方向的边缘；辅助方向的酉自由度正是同一混合态的规范冗余。由此，谱权重是 Schmidt 长度，纠缠是不可分解的联合关系，steering 是改变辅助读口后的同一边缘。

白话说：一张混合的概率表可以看成更大房间里一条纯粹的关系，只是你把辅助房间遮住了。把遮住的房间换一个坐标，得到的仍是同一边缘状态；在辅助房间换测量方向，就会得到不同的制备分解，这就是 steering。重要的减法是：在已经有复 Hilbert 张量结构以后，纯化不是再加的一条外部公理，而是谱分解自动给出的定理。

## 34. 局部比较完备性：不允许隐藏的整体关系

第 33 节把混合态解释成纯化边缘，但仍有一个整体性问题：所有局部比较是否足以识别整体状态？把它写成一个单一分离条件，可以检验复数 Hilbert 几何是否已经把“关系的关系”封闭。

**定义 34.1（局部比较完备公理）。** 对复合系统 $A\boxtimes B$，若两个状态 $\rho,\sigma$ 满足

$$
\operatorname{tr}\!\left((\rho-\sigma)(E\otimes F)\right)=0
$$

对所有局部效应 $0\le E\le I_A$、$0\le F\le I_B$ 都成立，则要求 $\rho=\sigma$。等价地，所有产品事件读数必须分离整体正比较状态。

**定理 34.2（复 Hilbert 中的局部层析）。** 在有限维复 Hilbert 张量积中，定义 34.1 由线性代数推出。取 $\mathrm{Herm}(H_A)$、$\mathrm{Herm}(H_B)$ 的基 $\{A_i\}$、$\{B_j\}$。每个 Hermitian 算子是两个正算子的差，而每个正算子乘一个足够小的标量就是效应；因此产品效应的线性张成包含所有 $A_i\otimes B_j$。若 $\Delta=\rho-\sigma$ 对所有产品效应的迹配对为零，则对全部 $A_i\otimes B_j$ 也为零，故

$$
\Delta=0.
$$

这证明复 Hilbert 的产品比较没有遗漏整体方向。证毕。

**命题 34.3（删去局部完备性的隐藏扇区反例）。** 令整体比较空间扩张为

$$
\widetilde H_{AB}=(H_A\otimes H_B)\oplus K,
$$

并让所有产品效应在隐藏扇区 $K$ 上作用相同（例如都按同一个标量乘 $I_K$）。隐藏扇区内两个不同状态 $\eta_0\ne\eta_1$ 对所有产品效应给出相同读数，却可由一个整体效应区分。于是若不要求定义 34.1，局部数据不能排除额外的整体关系。

**命题 34.4（实复合的维数障碍）。** 对实 Hilbert 系统，局部对称算子空间维数为

$$
\frac{d_A(d_A+1)}2\,\frac{d_B(d_B+1)}2,
$$

而整体对称算子空间维数为

$$
\frac{d_Ad_B(d_Ad_B+1)}2.
$$

两者差为

$$
\frac{d_Ad_B(d_A-1)(d_B-1)}4>0
$$

（当 $d_A,d_B>1$），所以产品比较在实复合中必然留下局部看不见的整体方向。局部完备性因此是区分复 Hilbert 复合与某些替代复合的结构性条件，而不是一句关于测量方便性的口号。

**定理 34.5（与现有量子公理的对应）。** 定义 34.1 与第 29 节的乘法复合、第 28 节的局部框架读出结合，给出有限维局部层析；与局部通道的迹保持和产品效应求和结合，则局部边缘概率不依赖远端测量菜单，得到量子无信号的代数结论。它不单独推出相对论因果锥、相互作用 Hamiltonian 的局域性或实验上哪些产品效应可取得。

**候选 34.6（最简整体闭合几何）。** 一个整体关系只有在某个局部比较上留下可见投影时才算属于系统；任何与全部产品比较正交的方向都必须被排除或显式登记为额外扇区。复 Hilbert 张量积恰好把产品比较张成整个 Hermitian 算子空间，因此是“无隐藏关系”的最简闭合实现。

白话说：两台仪器各自看得很全，还不代表它们合起来没有一间藏起来的房间。局部比较完备性规定：如果所有“左边一个问题、右边一个问题”的答案都一样，整体状态就必须一样。复 Hilbert 空间满足这条，因为产品算子能铺满整个房间；实复合或偷偷加一个隐藏扇区时，房间里会出现局部仪器永远看不到的方向。

## 35. 自对偶齐性比较锥：比 Hilbert 坐标更原始的几何候选

前面一直用复向量和算子来表达比较。再做一次坐标减法：只保留状态的正锥、比较配对以及“所有内部状态可以互相变换”的齐性。

**定义 35.1（自对偶齐性比较锥公理）。** 对每个有限系统 $A$，取有限维实向量空间 $V_A$、尖闭生成锥 $C_A\subset V_A$、序单位 $u_A$ 和非退化比较配对 $\langle-,-\rangle_A$，满足：

1. **自对偶：**
   $$
   C_A=\{x\in V_A:\langle x,y\rangle_A\ge0\ \text{对所有 }y\in C_A\};
   $$
2. **齐性：** 保持 $C_A$ 的线性自同构群在 $\operatorname{int}C_A$ 上传递；
3. **读出：** 状态是 $x\in C_A$ 且 $\langle u_A,x\rangle_A=1$，效应是 $0\le e\le u_A$，概率为 $\langle e,x\rangle_A$；
4. **复合：** 独立系统的锥包含 $C_A\otimes C_B$ 的正生成，并满足第 34 节的局部比较完备性。

这条候选不预设复数、矩阵乘法或 Hilbert 坐标；它只把“比较不会给负概率”和“内部状态之间没有不可达地层”写成锥几何。

**定理 35.2（锥几何的 Jordan 化）。** 在有限维、闭、尖、生成和自对偶齐性的条件下，$V_A$ 上存在一个 Euclidean Jordan 代数结构，使 $C_A$ 正好是平方元锥，序单位是 Jordan 单位。比较自同构成为 Jordan 正性自同构，状态具有谱分解

$$
x=\sum_i\lambda_i p_i
$$

其中 $p_i$ 是一组正交 primitive idempotent，$\lambda_i\ge0$。复量子系统

$$
C_A=M_d(\mathbb C)_+,
$$

是该候选的一个特例；经典单纯形锥、实对称正定锥和四元数自伴正锥也满足同样的自对偶齐性。证毕（Koecher–Vinberg 表示定理）。

**命题 35.3（为什么这还不是复量子起源）。** 自对偶齐性本身不能排除经典或实/四元数分支：

1. $\mathbb R_+^n$ 的内部可由正对角自同构互相到达，并在标准配对下自对偶；
2. 实对称和四元数自伴正锥同样自对偶齐性，但没有一般复 Bargmann 相位；
3. 锥的谱分解只给出可加的特征值，不给出第 20 节的三点复 holonomy。

因此复量子还需要独立的相位闭环、纯化唯一性以及复合的局部完备性；第 33、34 节给出的条件正是排除这些替代分支的候选桥，而不是 35.1 的自动结论。

**定理 35.4（与既有公理的对应）。** 在选定复矩阵锥并采用其 Hilbert–Schmidt 配对后，定义 35.1 的效应读出退化为 Born 迹；锥自同构的连续一参数群退化为第 30 节的酉流；保持所有辅助锥正性的线性箭头退化为第 31 节的完全正映射；锐面上的不扰动压缩退化为第 32 节的 Lüders 规则。这个对应是一个坐标恢复定理，不是从锥公理单独选择复分支的证明。

**候选 35.5（最简坐标前几何）。** 量子起源可以先看成一个带自对偶正锥的关系空间：正性给可比性，齐性给可达变换，锥的面给事件，张量锥给复合，局部完备性排除隐藏方向。复 Hilbert 空间是再加入复相位闭环、纯化和复合选择条件后的一种最小坐标实现；若删去相位，候选会退回 Jordan/经典分支。

白话说：先不要急着画向量，只画一块“允许的正区域”。区域的镜像正好还是自己，内部每一点都能被某种保持区域的变换搬到另一点；这两条会长出 Jordan 代数和谱分解。但这张区域图还可能是经典的、实的或四元数的。要得到真正的复量子世界，还必须让三点绕圈留下复相位，并让纯化和复合没有隐藏方向。

## 36. 三点相位闭环：复数从哪里进入比较网

第 35 节说明正锥本身不能选择复数。把复数的最小痕迹放回原始关系：不是给每条边一个绝对相位，而是给三条边围成的闭环一个规范不变量。

**定义 36.1（$U(1)$ 型 holonomy 比较公理）。** 对非零比较边 $\kappa(a,b)$，定义可观测模平方

$$
r(a,b)=|\kappa(a,b)|^2
$$

和三点闭环相位

$$
\phi(a,b,c)=
\frac{\kappa(a,b)\kappa(b,c)\kappa(c,a)}
{|\kappa(a,b)\kappa(b,c)\kappa(c,a)|}.
$$

要求：

1. 局部相位规范 $\kappa(a,b)\mapsto\overline{\theta_a}\kappa(a,b)\theta_b$ 不改变 $\phi$；
2. 反向闭环满足 $\phi(a,c,b)=\phi(a,b,c)^{-1}$；
3. 对所有四点（相关边非零）满足闭环 cocycle
   $$
   \phi(a,b,c)\phi(a,c,d)
   =\phi(a,b,d)\phi(b,c,d);
   $$
4. 所有相位值属于连续、紧、连通、交换的一维 Lie 群 $G$，并且至少有一个非平凡闭环。

第四条是“相位为何不是离散符号”的最小选择；它不预设复向量空间，只规定闭环的内部群。

**定理 36.2（相位群与复线）。** 满足定义 36.1 第 4 条的群 $G$ 同构于 $U(1)$。因此每条比较边可局部写成

$$
\kappa(a,b)=\sqrt{r(a,b)}\,e^{i\vartheta_{ab}},
$$

而三点 holonomy 的相位

$$
\arg\phi(a,b,c)
 =\vartheta_{ab}+\vartheta_{bc}+\vartheta_{ca}pmod{2\pi}
$$

在局部规范下不变。四点 cocycle 正是这些局部相位可以拼成一个 $U(1)$ 主线丛连接的条件；若再加入第 26 节的全有限正半定性，GNS 构造得到复 Hilbert 比较空间。证毕。

**命题 36.3（替代分支的反推）。**

1. 经典比较的闭环相位恒为 $1$，没有干涉 holonomy；
2. 实 Hilbert 比较的相位最多为 $\{1,-1\}$，是离散不连通群，不能满足非平凡连续一维相位条件；
3. 四元数单位相位形成非交换的三维群 $SU(2)$，一般不满足交换一维条件；只有落在一个复切片的特殊子族会保留，不能由本公理单独排除这种退化；
4. 仅给任意三点相位而删去全有限正性，仍可构造通过所有三点检验却在四点 Gram 方向上为负的表。

所以 holonomy 选择的是复相位语言，不是单独的量子存在证明。

**定理 36.4（与现有量子公理的对应）。** $U(1)$ holonomy 与正比较核结合后，三点干涉项

$$
2\operatorname{Re}\bigl(\kappa_{12}\kappa_{23}\kappa_{31}\bigr)
$$

具有规范不变意义；第 28 节的正交框架归一化把其模平方读成 Born 概率，第 29 节的乘法比较把 holonomy 乘到复合系统，第 30–32 节分别给出酉流、CP 通道和 Lüders 压缩。若删去 holonomy，正锥仍能给 Jordan/实几何，但干涉相位没有内生来源。

**候选 36.5（最简复相位几何）。** 量子关系网的边只有模平方，三边闭环才携带方向；闭环值组成一个连续交换的一维紧群，因而是 $U(1)$。正性负责把这些相位拼成整体，张量和纯化负责把局部环路接成系统级几何。复数不是每条边的外部标签，而是闭环关系的最小连续群表示。

白话说：一条边上的箭头颜色可以换掉，单独没有意义；三条边围成一圈后，颜色绕一圈剩下的差才是真正可观测的相位。若这个相位既连续又可交换，最小的圆就是 $U(1)$，于是复数自然出现。可是只有圆还不够，所有有限比较表仍必须非负，才能真的铺成量子 Hilbert 空间。

## 37. 成对比较的顺序无关：从交换一致性到最小 Hilbert 几何

前面的章节逐层加入相位、事件、复合、通道和锥。把这些层暂时全部拿掉，用户的直觉可以压缩成一个更原始的问题：一组对象的知识是否只由两两比较组成，并且加入对象或重排比较的先后不改变已经得到的结果？这里必须区分两种“顺序无关”。

- **排列无关**：同一有限对象集换一个列举顺序，只是把比较表同时换行换列；
- **路径传递**：把直接比较写成经过中间对象的数值乘法，要求 $K(x,z)=K(x,y)K(y,z)$。

第一条是共同来源的一致性，第二条过强，会把几何压成一条线。量子结构需要前者，不需要后者。

**定义 37.1（有限成对比较相容公理）。** 取一个准备对象集 $P$ 和标量域 $\mathbb K$，其中 $\mathbb K=\mathbb R$ 或 $\mathbb C$。对每个有限子集 $S\subset P$ 给出表

$$
K_S:S\times S\longrightarrow\mathbb K,
$$

并要求：

1. **单位与反向比较：** $K_S(x,x)=1$，且 $K_S(y,x)=\overline{K_S(x,y)}$；
2. **有限正性：** 对任意 $z_x\in\mathbb K$，
   $$
   \sum_{x,y\in S}\overline{z_x}K_S(x,y)z_y\ge0;
   $$
3. **限制相容：** 若 $T\subset S$，则 $K_T$ 是 $K_S$ 在 $T\times T$ 上的限制；
4. **排列无关：** 对 $S$ 的任意重排，表只按同一个置换同时换行换列，所有二次型与主子式保持不变。

这条公理不要求比较值沿路径相乘，也不要求任何一个对象具有先验坐标。它只要求所有有限的两两比较表能够同时来自一个不产生负平方长度的来源。

**定理 37.2（有限表的全局化）。** 定义 37.1 等价于一个全局归一化正定核 $K:P\times P\to\mathbb K$。它存在一个 Hilbert 空间 $H_K$ 和单位向量族 $(\psi_x)_{x\in P}$，使

$$
K(x,y)=\langle\psi_x,\psi_y\rangle,
$$

且 $H_K$ 在这些向量张成的闭包内唯一到酉（实情形为正交）等距同构。

**证明。** 限制相容使有限表中的同一对 $(x,y)$ 具有唯一值，因而定义全局 $K$。在有限支撑函数空间 $\mathbb K^{(P)}$ 上设

$$
\langle f,g\rangle_K
 =\sum_{x,y}\overline{f(x)}K(x,y)g(y).
$$

有限正性保证这是半内积；商去零范数子空间并完备，得到 $H_K$。令 $\psi_x$ 为点质量函数的等价类，就有 $\langle\psi_x,\psi_y\rangle=K(x,y)$。任何另一组生成同一核的向量都在有限线性组合上给出同一个等距映射，延拓到闭包即得唯一性。证毕。

这个全局化结论说明，“增量加入顺序不变”不是额外的时间公理，而是有限子集形成的有向系统的限制相容；其最简几何就是 Gram 几何。换句话说，真正的起源压缩不是“对象之间有一条可传递的数”，而是“所有有限两两比较都能拼成同一个正半定表”。

**命题 37.3（仅两两可比或对称仍不足）。** 若删去有限正性，只保留 $K(x,x)=1$ 和 $K(y,x)=\overline{K(x,y)}$，则局部比较不一定有共同实现。反例为

$$
K=\begin{pmatrix}
1&0.9&0.9\\
0.9&1&-0.9\\
0.9&-0.9&1
\end{pmatrix}.
$$

每个二阶比较块都正定，但 $\det K=1-3(0.9)^2-2(0.9)^3<0$，所以不存在同时实现三条边的 Hilbert 向量。因而“每一对都能比较”只是局部可行性；共同正性才是整体关系的约束。

**命题 37.4（把顺序无关误作乘法传递会消灭干涉）。** 若对所有 $x,y,z$ 强加

$$
K(x,z)=K(x,y)K(y,z),
$$

并保留 $K(x,x)=1$ 与 Hermitian 反向关系，则取 $z=x$ 得 $|K(x,y)|^2=1$。因此所有比较向量满足 $|\langle\psi_x,\psi_y\rangle|=1$，由 Cauchy–Schwarz 等号条件，它们都共线，Gram 矩阵秩至多为一。这个分支没有非平凡三角形面积，也没有可观测的干涉相位。故量子所需的是“正定的非传递相容”，而不是数值乘法的平坦性。

**定理 37.5（与现有量子公理的最短桥）。** 在 $\mathbb C$ 分支中，定义 37.1 给出：

1. 归一化态向量及其射影空间；
2. 转移比较 $r(x,y)=|K(x,y)|^2$；
3. 三点 Bargmann 闭环 $K(x,y)K(y,z)K(z,x)$；
4. 在给定连续非平凡闭环群时的 $U(1)$ 相位（第 36 节）；
5. 由正交框架的上下文无关归一化得到平方律和投影 Born 读出（第 28 节）。

它还不能单独给出时间演化、系统张量、完全正通道或 Lüders 更新；这些分别需要连续流、复合乘法、辅助系统保持正性和锐事件压缩等附加关系。实 Hilbert 与经典正核也满足定义 37.1，所以该公理是 Hilbert/量子运动学的共同底座，而不是仅凭自身选择复数的证明。

**候选 37.6（最简量子起源表述）。** 世界的基本资料是一个有限成对比较网络。任何有限子网络都必须能同时嵌入同一个正几何，且加入节点、删去节点或重排节点只做限制和置换。实分支给出无相位的 Hilbert 几何；若闭环比较还具有连续、紧、连通、交换的一维非平凡 holonomy，最小扩展是复 $U(1)$ 线丛，三点闭环提供干涉；若再要求正交框架读数在所有测量菜单上归一且无上下文依赖，平方 Born 规则被强迫出来。

白话说：不是先有一套复杂的量子机器，再规定怎样比较；而是先有很多对象，任何两件都能比较。关键要求是：把这些比较放在一张桌子上时，不论先登记哪一对、最后怎样排列，整张桌子都必须来自同一个不会产生负平方长度的空间。只要求一对一对能说话，三件东西可能互相冲突；把比较值硬乘起来，又会把所有东西压成一条线，干涉消失。量子恰好位于两者之间：比较表整体正定但不作数值传递，三点绕圈保留相位，正交测量菜单的总量再把相位几何读成 Born 概率。

## 38. 负型比较距离：把 Gram 表再压成一条二元几何律

第 37 节仍把复值 $K(x,y)$ 当作基本数据。再向下回溯一次，只保留比较产生的平方差。设

$$
D(x,y)=\|\psi_x-\psi_y\|^2.
$$

它忘掉了共同相位和复 holonomy，只保留两对象之间可比较的几何能量。顺序无关现在表现为：$D$ 只依赖无序的有限对象集，有限表之间只做限制。

**定义 38.1（负型成对比较公理）。** 对准备集 $P$ 给出一个函数 $D:P\times P\to[0,\infty)$，要求：

1. $D(x,x)=0$ 且 $D(x,y)=D(y,x)$；
2. 对每个有限族 $x_1,\ldots,x_n$ 和满足 $\sum_i c_i=0$ 的实数 $c_i$，有
   $$
   \sum_{i,j}c_i c_jD(x_i,x_j)\le0;
   $$
3. 对有限子集的重排和限制，表值不变。

第二条是条件负定性（negative type）。它不是逐边的三角不等式，而是一次同时检查所有边的有限约束。

**定理 38.2（Schoenberg 全局化）。** 定义 38.1 当且仅当存在一个实 Hilbert 空间 $H_D$ 和映射 $\Phi:P\to H_D$，使

$$
D(x,y)=\|\Phi(x)-\Phi(y)\|^2.
$$

该嵌入在闭仿射包上唯一到 Euclidean 等距变换。

**证明。** 固定基点 $o\in P$，定义

$$
G_o(x,y)=\frac12\bigl(D(x,o)+D(y,o)-D(x,y)\bigr).
$$

对有限系数 $a_i$，令 $a_o=-\sum_i a_i$，并把 $o$ 加入有限族。由条件负定性，

$$
\sum_{i,j}a_i a_jG_o(x_i,x_j)
=-\frac12\sum_{u,v}\widetilde a_u\widetilde a_vD(u,v)\ge0.
$$

所以 $G_o$ 是正半定核。按第 37 节的 GNS/Gram 构造得到向量 $\Phi(x)$，且 $\Phi(o)=0$、$\langle\Phi(x),\Phi(y)\rangle=G_o(x,y)$。展开平方即得 $D(x,y)=\|\Phi(x)-\Phi(y)\|^2$。反向地，任意 Hilbert 距离满足

$$
\sum_{i,j}c_ic_jD(x_i,x_j)
=-2\left\|\sum_i c_i\Phi(x_i)\right\|^2\le0
$$

（因为 $\sum_i c_i=0$）。唯一性来自距离保持映射在仿射包上的唯一延拓。证毕。

因此，第 37 节的全有限正定 Gram 表与第 38 节的全有限负型距离是同一实几何的两种坐标：前者直接给内积，后者只给点之间的平方差。第 38 节更接近“任何两点都可比较”的直觉，也不预设复数。

**命题 38.3（仅对称、仅三角形都不够）。**

1. 对称性和非负性本身不够。令三点的平方差为
   $$
   D_{12}=D_{13}=0.2,\qquad D_{23}=3.8.
   $$
   则每一对都有非负比较，但 $\sqrt{D_{23}}>\sqrt{D_{12}}+\sqrt{D_{13}}$，不可能来自 Hilbert 距离；更直接地，取系数 $(1,-\tfrac12,-\tfrac12)$ 得 $\sum_i c_i=0$ 而 $\sum_{i,j}c_ic_jD_{ij}=1.5>0$，违反负型条件。
2. 即使 $d=\sqrt D$ 满足三角不等式，也不够。取四点的四环图距离：相邻点距离为 $1$，对顶点距离为 $2$。它满足普通三角不等式，但取系数 $(1,-1,1,-1)$ 得
   $$
   \sum_{i,j}c_ic_jd(i,j)^2=8>0,
   $$
   违反负型条件。因此 Hilbert 可实现性是比“距离看起来合理”更强的整体约束。

**命题 38.4（距离不能恢复复相位）。** 若 $D(x,y)=\|\psi_x-\psi_y\|^2$ 且各 $\psi_x$ 为单位向量，则

$$
D(x,y)=2-2\operatorname{Re}\langle\psi_x,\psi_y\rangle.
$$

所以 $D$ 只记录比较振幅的实部，忘掉三点 Bargmann 闭环的虚部和 $U(1)$ holonomy。即使所有 $D$ 已知，也可能存在不同的复 Gram 核具有相同实部而闭环相位互为共轭。负型距离因而只能恢复实 Hilbert 几何；复量子需要在其上再加相位纤维。

**定义 38.5（球面与相位的量子完成条件）。** 负型嵌入若还满足存在中心 $q$ 和半径 $R>0$，使

$$
\|\Phi(x)-q\|=R\qquad(x\in P),
$$

则可平移并缩放到单位球面，得到

$$
\operatorname{Re}K(x,y)=1-\frac12D(x,y).
$$

在这个球面实部上加入第 36 节的连续非平凡 $U(1)$ 闭环，并要求补成全有限正定的复核，就恢复复 Hilbert 比较；再加入第 28 节的正交框架归一化，得到投影 Born 规则。

**候选 38.6（最简距离版量子起源）。** 基本公理先只规定：所有两两平方差组成一个限制相容、全有限负型的比较距离，并且所有准备落在同一个比较球面上。这个公理唯一地产生实 Hilbert 几何；复数不是距离本身的属性，而是球面比较网络的闭环 $U(1)$ 纤维。Born 规则是相位补全后对正交框架的唯一无上下文归一化，动力学和复合仍是更高层结构。

这比直接写复 Gram 表更简洁，但它的结论也更准确：它解释了“为什么所有两两比较会长成 Hilbert 空间”，没有声称单靠距离就解释复相位。量子起源的最小分层因此是

$$
\text{负型两两距离}
\;\Longrightarrow\;
\text{实 Hilbert 几何}
\;\Longrightarrow\;
\text{球面 }U(1)\text{ holonomy}
\;\Longrightarrow\;
\text{Born 读出}.
$$

白话说：先不问箭头是什么颜色，只问两点之间相差多少。只要所有有限的差值表都满足同一个“负型”账本，它们就一定能铺成一张实的 Hilbert 地图。普通三角形规则还不够，必须所有点一起通过有限检验。距离看不见绕圈的颜色；把所有点放到同一个球面后，再给闭环加上一圈连续的 $U(1)$ 相位，复数和干涉才出现。概率是这张带颜色的球面上，完整正交菜单保持总量为一所强迫出来的读数。

## 39. 比较差的二次能量：把全有限正性压成一个不变量

第 38 节的负型条件仍然逐项写出有限距离表。把“先比较哪一对、怎样分组、怎样重排”直接视为一个形式差的平方长度，可以把整组条件压成一个二次能量。

**定义 39.1（顺序无关比较差公理）。** 令

$$
\operatorname{Diff}_0(P)
 =\left\{\mu=\sum_{x\in P}a_x\delta_x:\nobreak\text{支撑有限且 }\sum_xa_x=0\right\}.
$$

要求存在一个只依赖形式差本身的函数

$$
V:\operatorname{Diff}_0(P)\longrightarrow[0,\infty)
$$

满足：

1. **比较差归一：** $V(\delta_x-\delta_y)=D(x,y)$；
2. **齐次：** $V(t\mu)=t^2V(\mu)$ 对所有 $t\in\mathbb R$；
3. **重排无关的合成：**
   $$
   V(\mu+\nu)+V(\mu-\nu)=2V(\mu)+2V(\nu);
   $$
4. **正性：** $V(\mu)\ge0$。

形式差的有限展开、支撑枚举和括号分组都只表示同一个 $\mu$，不得改变 $V$。第三条是“比较结果与合成顺序无关”的单一代数表达；第四条是全局而非逐边的正性。

**定理 39.2（极化恢复 Hilbert 几何）。** 定义 39.1 当且仅当存在一个实 Hilbert 空间 $H_V$ 和映射 $\Phi:P\to H_V$，使

$$
D(x,y)=\|\Phi(x)-\Phi(y)\|^2,
$$

并且

$$
V\!\left(\sum_xa_x\delta_x\right)
 =\left\|\sum_xa_x\Phi(x)\right\|^2
$$

对所有总和为零的有限系数成立。

**证明。** 在 $\operatorname{Diff}_0(P)$ 上定义极化

$$
B(\mu,\nu)
 =\frac14\bigl(V(\mu+\nu)-V(\mu-\nu)\bigr).
$$

齐次性和平行四边形恒等式给出 $B$ 的对称双线性；正性给出 Cauchy–Schwarz 不等式。令 $N=\{\mu:V(\mu)=0\}$，则 $N$ 是 $B$ 的零空间。商空间 $\operatorname{Diff}_0(P)/N$ 带有内积 $B$，完备化得到 $H_V$。固定 $o\in P$，令

$$
\Phi(x)=[\delta_x-\delta_o].
$$

于是

$$
\|\Phi(x)-\Phi(y)\|^2
 =V(\delta_x-\delta_y)=D(x,y).
$$

反向地，任意 Hilbert 嵌入定义

$$
V(\mu)=\left\|\sum_xa_x\Phi(x)\right\|^2
$$

立即满足四条公理。展开点差并使用 $\sum_xa_x=0$，还得到

$$
V(\mu)=-\frac12\sum_{x,y}a_xa_yD(x,y),
$$

所以定义 39.1 与第 38 节的全有限负型条件等价。证毕。

**命题 39.3（三点反例直接击穿二次能量）。** 对第 38 节的三点距离

$$
D_{12}=D_{13}=0.2,\qquad D_{23}=3.8,
$$

取

$$
\mu=\delta_1-\tfrac12\delta_2-\tfrac12\delta_3.
$$

则

$$
V(\mu)=-\frac12\sum_{i,j}c_ic_jD_{ij}=-0.75<0.
$$

所以三条逐边比较无法延拓为一个顺序无关的正二次能量；缺失的正性不是记号问题，而是共同几何的实际约束。

**定理 39.4（这一压缩的严格范围）。** 比较差公理是第 38 节负型距离的二次形式重写：它把所有有限系数检验集中到一个对象 $V$，但没有减少实几何所需的信息。它给出实 Hilbert 几何和平方差，仍然不给出：

- 共同球面上的复内积虚部与三点 $U(1)$ holonomy；
- 正交框架上的 Born 归一化；
- 时间的一参数酉群；
- 张量复合、完全正通道和 Lüders 更新。

若在球面条件下补上连续非平凡 $U(1)$ 闭环，并要求复补全后的有限 Gram 表正半定，则恢复第 36–38 节的复比较几何；再加入第 28 节的框架无关归一化，得到平方 Born 规则。

**候选 39.5（最短的比较起源公理）。** 基本关系不是一张预先坐标化的复矩阵，而是形式差上的一个顺序无关、非负、二次的比较能量 $V$。点对点的比较只是 $V(\delta_x-\delta_y)$ 的边缘读数；极化把所有边缘关系重新组织成一个内积。量子复数、干涉和概率是这个实二次骨架加上球面相位纤维和框架归一化后的完成，而不是 $V$ 单独包含的结论。

这给出本路线目前最简的完整分层：

$$
\text{顺序无关的正二次比较能量}
\;\Longrightarrow\;
\text{实 Hilbert 商空间}
\;\Longrightarrow\;
\text{球面上的 }U(1)\text{ holonomy}
\;\Longrightarrow\;
\text{Born 读出}.
$$

白话说：把所有对象的两两差值写成“比较差的平方长度”。不论先算哪一对、怎样把差分组、怎样重新排列，只要最后得到的是同一个非负二次能量，就能把这些差拼成一张 Hilbert 地图。三点反例说明，单条边都正常，整体能量仍可能变成负数。这个二次能量已经是两两比较路线的信息下限；再往下删，就会漏掉某个有限组合的矛盾。复数和干涉要等到球面闭环携带 $U(1)$ 相位时才出现，Born 规则再由完整测量框架的总量约束产生。

## 40. 内生四分之一转：从实比较到复相位

第 39 节已经把两两比较压成实 Hilbert 商空间 $(H_V,g)$。复数不必作为边上的外部标签加入；可以只加入一个作用在比较空间内部的四分之一转 $J$，把“相位方向”写成几何自同态。

**定义 40.1（内生复结构公理）。** 在 $(H_V,g)$ 上给出一个实线性算子 $J$，满足

$$
J^2=-I,qquad g(Ju,Jv)=g(u,v).
$$

并要求所有由比较关系生成的允许等距变换与 $J$ 相容，即 $TJ=JT$。最后要求相位稳定子群的连通紧交换部分恰好是一维：

$$
\{\exp(\theta J):\theta\in\mathbb R\}\cong U(1).
$$

前两条是内生四分之一转，最后一条只用于排除更大的四元数相位群。

**定理 40.2（正交复结构恢复复 Hilbert 空间）。** 定义 40.1 的前两条使 $H_V$ 成为复向量空间，复数作用定义为

$$
(a+ib)u:=au+bJu.
$$

定义

$$
 h(u,v):=g(u,v)+i\,g(Ju,v).
$$

则 $h$ 是复 Hilbert 内积，且

$$
 h(u,u)=g(u,u),qquad
 h(Ju,v)=-i\,h(u,v),qquad
 h(u,Jv)=i\,h(u,v).
$$

**证明。** 正交性给出 $J^{-1}=J^*=-J$，所以 $g(Ju,v)=-g(u,Jv)$。由此直接验证 $h$ 的共轭对称性、第一变量共轭线性和第二变量线性；并且 $g(Ju,u)=0$，故 $h(u,u)=g(u,u)\ge0$，零向量条件不变。实完备性与复标量作用相容，因此 $H_V$ 的同一完备空间就是复 Hilbert 空间。证毕。

**定理 40.3（相位与三点 holonomy 内生出现）。** 对单位准备向量定义

$$
K_J(x,y):=h(\psi_x,\psi_y),qquad
r(x,y):=|K_J(x,y)|^2.
$$

令

$$
R_\theta=\cos\theta\,I+\sin\theta\,J.
$$

则 $R_\theta$ 保持 $g$、$h$ 和 $D$，并且对局部相位变换 $\psi_x\mapsto R_{\theta_x}\psi_x$ 有

$$
K_J(x,y)\mapsto e^{i(\theta_y-\theta_x)}K_J(x,y).
$$

所以三点乘积

$$
K_J(x,y)K_J(y,z)K_J(z,x)
$$

不变；它正是第 36 节的 Bargmann 闭环。若各态在单位球面上，则

$$
D(x,y)=2-2\operatorname{Re}K_J(x,y).
$$

因此 $J$ 把第 38 节距离中被遗忘的虚部补回，而 $U(1)$ 相位群由同一个内部转动生成。

**命题 40.4（为什么单个 $J$ 仍不能选出复量子）。**

1. 没有 $J$ 时，同一个实比较几何可以保持为经典或实 Hilbert 分支；$D$ 本身无法指定四分之一转。
2. 一个 $J$ 也不能排除四元数分支。若同一实空间上还有两个与 $J$ 反对易的正交复结构 $J_2,J_3$，则它们和 $J$ 生成四元数单位，内部相位群扩展为
   $$
   \operatorname{Sp}(1)\cong SU(2),
   $$
   它是非交换三维群，而不再是一维 $U(1)$。
3. 因而定义 40.1 的一维连通紧交换条件是必要的分支选择；它把“存在一个复切片”加强为“所有可观测相位只有一个圆方向”。

**定理 40.5（与现有量子公理的对应）。** 在球面比较和定义 40.1 下：

- $K_J$ 给出复 Hilbert 射影运动学，$r=|K_J|^2$ 是转移概率；
- 保持 $r$ 的射影双射由 Wigner 定理实现为酉或反酉；保持 $J$ 的分支是酉，反转 $J$ 的分支是反酉；
- 若时间变换是强连续的一参数 $J$-相容酉群，Stone 定理给出 $U_t=e^{-itH}$；
- 对正交框架加入第 28 节的上下文无关归一化，得到 $p(e|\psi)=|h(e,\psi)|^2$；
- 张量复合、完全正通道、Lüders 更新仍需第 29–32 节的独立条件。

**候选 40.6（最简复量子起源）。** 顺序无关比较首先产生实二次几何；复数的最小内生来源是一个与比较内积相容的正交四分之一转 $J$，而复量子分支的完整选择还要求其相位稳定子群只有一个连通紧交换圆 $U(1)$。复内积、Bargmann holonomy 和酉相位由 $J$ 自动生成；Born、动力学和复合分别由框架归一化、连续流和张量/完全正条件补足。

这条候选比直接把每条边写成复数更短，但它的边界也很清楚：$J$ 不是从纯距离 $D$ 的定理，而是“关系空间自身有一个四分之一转”的新增结构。若未来能从更原始的闭环关系证明 $J$ 存在，它才会成为真正的内生结论；当前仍是一个明确的开放桥梁。

白话说：实 Hilbert 地图只有长度和角度，还没有“向左转九十度”的内部方向。给这张地图加一个保持长度的四分之一转 $J$，就能把两个实方向合成一个复方向，绕它转一圈得到 $U(1)$ 相位，三点闭环因此有干涉颜色。若地图里同时有三个互相配合的四分之一转，就会长出四元数的三维相位群；所以必须额外要求相位只有一个圆。复数于是成为比较空间内部的一种旋转结构，而不是外部贴上去的数字。

## 41. 对称—反对称二元关系：把复结构完全放回比较关系

第 40 节用算子 $J$ 表示复相位。若公理必须直接作用在二元关系上，可以把 $J$ 换成一个有向的二元比较：对称部分记录长度，反对称部分记录有向面积。

**定义 41.1（对称—反对称比较公理）。** 在第 39 节得到的实 Hilbert 商空间 $(H_V,g)$ 上，给出一个连续双线性形式

$$
\omega:H_V\times H_V\longrightarrow\mathbb R
$$

满足：

1. **反向取负：** $\omega(u,v)=-\omega(v,u)$；
2. **Riesz 相容：** 存在唯一有界实线性算子 $J$，使
   $$
   \omega(u,v)=g(Ju,v);
   $$
3. **四分之一转闭合：** $J^2=-I$；
4. **关系相容：** 每个由比较关系生成的允许等距变换同时保持 $g$ 和 $\omega$；其连通紧相位稳定子群是一维交换群。

这里 $\omega$ 是公理的二元关系部分，$J$ 只是由 $g$ 和 $\omega$ 通过 Riesz 表示导出的记号。

**定理 41.2（二元关系直接生成复 Hilbert）。** 定义 41.1 的前三条给出

$$
 h(u,v):=g(u,v)+i\,\omega(u,v),
$$

它是一个复 Hilbert 内积；其中复标量作用由

$$
(a+ib)u=au+bJu
$$

定义。

**证明。** 由 $\omega$ 的反对称性，$J^*=-J$。结合 $J^2=-I$ 得

$$
 g(Ju,Jv)=g(u,v).
$$

因此 $J$ 是正交复结构。代入 $h$ 可得第一变量共轭线性、第二变量线性和共轭对称性；并且

$$
 h(u,u)=g(u,u)+i\omega(u,u)=g(u,u)\ge0.
$$

完备性来自原实 Hilbert 空间。证毕。

**定理 41.3（反对称关系就是相位和 holonomy）。** 令

$$
R_\theta=\cos\theta\,I+\sin\theta\,J.
$$

则 $R_\theta$ 同时保持 $g$、$\omega$ 和 $h$。对单位准备向量定义

$$
K_\omega(x,y)=h(\psi_x,\psi_y).
$$

局部变换 $\psi_x\mapsto R_{\theta_x}\psi_x$ 给出

$$
K_\omega(x,y)\mapsto e^{i(\theta_y-\theta_x)}K_\omega(x,y),
$$

所以三点乘积

$$
K_\omega(x,y)K_\omega(y,z)K_\omega(z,x)
$$

是规范不变量。它的模长由对称比较决定，辐角由反对称二元关系的闭环和决定。因而 $\omega$ 正是第 36 节 $U(1)$ holonomy 的局部关系表达。

**命题 41.4（反例和分支边界）。**

1. 若 $\omega=0$，则 $J=0$，没有复标量作用，模型退回实 Hilbert/经典分支。
2. 令 $J_0^2=-I$，并取 $\omega_\lambda(u,v)=\lambda g(J_0u,v)$。此时导出的 $J=\lambda J_0$，只有 $\lambda=\pm1$ 才满足 $J^2=-I$；任意缩放的反对称关系都不能成为相位。
3. 在四维实空间上若存在两个反对易的兼容形式 $\omega_1,\omega_2$，它们与乘积形式一起生成四元数单位，允许相位群扩张为 $SU(2)$。所以“一维连通紧交换稳定子”仍是排除四元数分支的必要条件。
4. 只有反对称性而没有 Riesz 相容和 $J^2=-I$ 时，$h=g+i\omega$ 只是一个复值双线性表，未必对应复 Hilbert 内积，也未必有可观测的圆相位。

**定理 41.5（与现有量子公理的对应）。** 对称比较 $g$、反对称比较 $\omega$ 和球面条件结合后：

- $h=g+i\omega$ 给出复 Hilbert 射影运动学，$|h(x,y)|^2$ 给出转移概率；
- 第 36 节的三点 Bargmann 相位成为 $\omega$ 在三边上的闭环积分；
- 保持 $g$、$\omega$ 的射影变换是酉，反转 $\omega$ 的分支是反酉；
- 强连续的酉一参数群经 Stone 定理给出 Hamiltonian；
- 第 28 节的正交框架无上下文归一化给出平方 Born 规则；
- 张量复合、完全正通道、Lüders 更新仍不由二元形式单独推出。

**候选 41.6（最简二元量子起源）。** 一个量子比较网络由两种同源的二元关系组成：对称关系 $g$ 负责平方长度，反对称关系 $\omega$ 负责有向面积。最小局部兼容律是：经 $g$ 对偶化后，$\omega$ 的作用平方为 $-I$；分支选择律是相位稳定子群为一维连通紧交换群。由此复数、$U(1)$ holonomy 和酉相位全部内生出现；Born、动力学和复合仍分别需要框架归一化、连续时间和系统组合条件。

这不是比第 40 节少了数学信息，而是把复结构从“一个外部算子”改写成“两个对象之间的对称与反对称比较”。它更符合关系优先的起源表述：复数是同一比较网络中长度关系和方向关系的兼容合成，而不是另加的坐标域。

白话说：两点之间有两种账：一账记录相差多远，另一账记录从一个方向绕到另一个方向时留下多少有向面积。第一账是 $g$，第二账是 $\omega$。如果第二账经过第一账的换算后，连续转两次正好反向，它就等于一个复数的“乘以 $i$”。三条边的有向面积加起来留下相位；若同时存在三种互相缠绕的面积方向，就会长成四元数，所以还要限制相位只有一个圆。

## 42. 正交框架守恒：二元复比较如何强迫 Born 读出

第 41 节已经给出复 Hilbert 比较 $h=g+i\omega$，但“比较结果怎样成为概率”仍可压成一条事件层关系：完整正交框架的总读数不依赖框架的排列、分组和上下文。

**定义 42.1（上下文无关框架守恒公理）。** 对单位准备 $\psi$ 和单位事件射线 $e$，令

$$
q_\psi(e)=|h(e,\psi)|^2.
$$

要求存在同一个函数 $f:[0,1]\to[0,1]$，与准备、框架和上下文无关，满足

$$
 f(0)=0,\qquad f(1)=1,
$$

并把秩一事件的读数定义为

$$
 p_\psi(e)=f(q_\psi(e)).
$$

对每个维数 $d\ge3$ 的正交完备框架 $C=(e_1,\ldots,e_d)$，要求

$$
\sum_{i=1}^d p_\psi(e_i)=1.
$$

这条公理只涉及二元重叠的模平方和完整框架的总量，不预先假设投影格、效应代数或 Born 公式。

**定理 42.2（框架守恒强迫平方律）。** 定义 42.1 必然有

$$
 f(t)=t\qquad(0\le t\le1).
$$

**证明。** 取任意 $x,y\ge0$ 且 $x+y\le1$。在三维中固定单位准备

$$
\psi=(\sqrt{x},\sqrt{y},\sqrt{1-x-y}).
$$

在第一组正交框架中，三个重叠平方是 $(x,y,1-x-y)$。在同一准备上，把前两个基向量旋转为

$$
 e'_1=\frac{\sqrt{x}\,e_1+\sqrt{y}\,e_2}{\sqrt{x+y}},
 \qquad
 e'_2=\frac{\sqrt{y}\,e_1-\sqrt{x}\,e_2}{\sqrt{x+y}},
 \qquad e'_3=e_3,
$$

（$x+y=0$ 时结论显然）。第二组框架的重叠平方为 $(x+y,0,1-x-y)$。两次框架守恒相减，并用 $f(0)=0$，得到

$$
 f(x)+f(y)=f(x+y).
$$

所以 $f$ 在 $[0,1]$ 上可加。由于 $f$ 取值于 $[0,1]$，它在区间上有界，因而单调且在有理数上满足 $f(m/n)=m/n$；用有理数逼近任意实数，得到 $f(t)=t$。证毕。

**定理 42.3（从框架读数到投影 Born 规则）。** 对任意正交投影 $P_E$，取其像空间的一组正交基 $(e_i)$，定义

$$
 p_\psi(P_E)=\sum_{e_i\in E}|h(e_i,\psi)|^2.
$$

Parseval 恒等式使该定义与所选基无关，并且

$$
 p_\psi(P_E)=\|P_E\psi\|^2=h(\psi,P_E\psi).
$$

互斥投影的和对应正交子空间直和，所以读数有限可加且 $p_\psi(I)=1$。有限维混合态按凸组合延拓后，存在密度算子 $\rho$，满足

$$
 p_\rho(P_E)=\operatorname{Tr}(\rho P_E).
$$

对一般 POVM，还需额外识别效应为正算子并使用谱分解；框架守恒本身直接强迫的是投影 Born 规则。

**命题 42.4（维数和上下文边界）。**

1. 若只允许二维框架，守恒律只有
   $$
   f(t)+f(1-t)=1,
   $$
   例如
   $$
   f(t)=\frac{t^2}{t^2+(1-t)^2}
   $$
   也满足边界条件，却不是 $f(t)=t$。三维框架是强迫加法的最小维数。
2. 若允许 $f$ 随框架改变，则每个框架都可以独立指定一组归一化读数，无法得到非情境 Born 规则。
3. 若删去完整框架条件，读数可以只在局部事件上归一，不能推出总概率为一。
4. 框架守恒没有给出测量后的状态更新；Lüders 规则仍需要第 32 节的不扰动锐事件压缩。

**候选 42.5（完整量子运动学的最简关系包）。** 对称二元比较 $g$、反对称二元比较 $\omega$ 和正交框架守恒组成一个最小事件闭包：

$$
(g,\omega)
\Longrightarrow
h=g+i\omega
\Longrightarrow
U(1)\text{ holonomy}
\Longrightarrow
f(t)=t
\Longrightarrow
\text{投影 Born 规则}.
$$

该关系包在有限维中给出复 Hilbert 射影运动学、转移概率、相位闭环和投影测量概率；Wigner 对称和 Stone 动力学分别还需射影概率保持与强连续时间，张量复合、通道和更新仍需更高层关系。

这一步是真正的逻辑减法：Born 公式不再作为一个数值公理写入，而只保留“所有三维以上正交比较菜单总量相同”。平方律由菜单之间的重叠重组被强迫出来；但 POVM、动力学和状态更新没有被偷渡进来。

白话说：同一个准备可以换不同的完整测量菜单。无论菜单怎样旋转，所有答案加起来都必须是一；而单个答案只看准备和这一根测量方向的重叠大小。三维菜单能把两个小重叠合并成一个大重叠，于是答案函数必须满足“先分开再相加”和“先合并再读出”相同，唯一结果就是平方律。二维菜单做不到这一步，所以二维本身不能强迫 Born 规则。

## 43. 比较保持流：从顺序无关关系到 Hamiltonian

第 42 节给出了静态量子运动学。把时间也看成关系，而不是外部坐标：时间演化是在准备空间上保持比较结构的一条连续流。

**定义 43.1（比较保持时间流公理）。** 在由 $h=g+i\omega$ 生成的射影准备空间 $\mathbb P(H)$ 上，要求存在一族双射

$$
T_t:\mathbb P(H)\longrightarrow\mathbb P(H),qquad t\in\mathbb R,
$$

满足：

1. **群律：** $T_0=I$ 且 $T_{t+s}=T_tT_s$；
2. **比较保持：**
   $$
   |h(T_tx,T_ty)|^2=|h(x,y)|^2
   $$
   对所有射影态 $x,y$ 成立；
3. **强连续：** 对每个射影态，$t\mapsto T_tx$ 在射影范数下连续；
4. **相位取向：** 若要求保持完整二元关系，则 $g$ 和 $\omega$ 分别保持；若只要求模平方保持，则允许反转 $\omega$ 的离散分支。

这条公理只说“时间推进不改变比较关系”，没有预先指定微分方程或 Hamiltonian。

**定理 43.2（比较保持流给出酉流）。** 定义 43.1 的前三条使每个 $T_t$ 由 Wigner 定理实现为酉或反酉射影变换。由于 $t\mapsto T_t$ 从 $T_0$ 连续开始，而酉与反酉分支不连通，整条连续流只能停留在酉分支。选择连续代表 $U_t$ 后，可能有一个射影相位二-cocycle：

$$
U_{t+s}=e^{i\alpha(t,s)}U_tU_s.
$$

对参数群 $(\mathbb R,+)$，连续 $U(1)$ 二-cocycle 可由连续相位重新规范化，因此得到严格的强连续一参数酉群

$$
U_{t+s}=U_tU_s.
$$

**证明。** Wigner 定理给出每个保持转移概率的射影双射的酉或反酉实现。强连续性排除从恒等射影变换跳到反酉连通分支。射影代表的乘法只差一个标量相位；实参数群的连续相位扩张可平凡化，得到严格群表示。证毕。

**定理 43.3（Stone 生成元和 Schrödinger 方程）。** 若 $U_t$ 是定理 43.2 的强连续一参数酉群，则存在唯一自伴算子 $H$，使

$$
U_t=e^{-itH}.
$$

对 $\psi$ 属于 $H$ 的定义域，

$$
 i\frac{d}{dt}U_t\psi=H U_t\psi,
$$

即现有的 Schrödinger 时间演化。Heisenberg 图像中可定义

$$
A(t)=U_t^*AU_t,
$$

在适当定义域上满足 $\dot A(t)=i[H,A(t)]$。

**命题 43.4（删除条件的反例）。**

1. **删去群律：** 任意时间标记的酉族都可保持转移概率，却未必存在单一生成元；例如在两个时间段使用不同且不满足拼接律的酉矩阵。
2. **删去连续性：** 取非连续加性函数 $a:\mathbb R\to\mathbb R$，令 $U_t=e^{ia(t)}I$。它满足群律和全部比较保持，却不是强连续流，不能由 Stone 定理得到物理 Hamiltonian。
3. **只保持模平方而不保持 $\omega$：** 反酉共轭也被允许；它保留 $|h|^2$，却反转相位取向。时间反演可以属于这一离散分支，但不能作为从恒等开始的连续动力学。
4. **删去双射性：** 单向等距嵌入可能保持部分比较，却没有可逆时间，也不构成物理的双向流。

**定理 43.5（与现有动力学公理的对应和边界）。** 比较保持时间流在已有复比较和 Born 框架上给出：

- Wigner 对称的酉分支；
- Stone 自伴生成元和 Schrödinger 方程；
- Heisenberg 可观测量的共轭演化；
- 完整 $g,\omega$ 保持所对应的相位取向守恒。

它不决定 $H$ 的具体谱、局域相互作用、相对论因果锥、张量复合或开放系统通道。那些需要经验输入或第 29–31 节的复合与完全正条件；Lüders 更新仍属于测量后的状态变换。

**候选 43.6（最简内生动力学公理）。** 时间不是外部流形参数，而是一族对全部二元比较保持、可逆、强连续并满足群律的关系变换。酉性是比较保持在连续连通分支中的定理，Hamiltonian 是这条关系流的自伴生成元，Schrödinger 方程是生成元定义的微分形式。反酉、非连续和不可逆分支分别对应时间反演、病态参数化和非物理单向过程。

白话说：时间推进就是把整张比较网一起搬动，但任何两点的比较结果都不变。只要求每一刻都能搬还不够，搬两次必须等于一次更长的搬动，而且搬动要连续。这样从恒等位置出发只能沿酉分支移动；Stone 定理把这条连续轨道压成一个自伴的 Hamiltonian，Schrödinger 方程只是“沿这条轨道走”的微分写法。

## 44. 乘法复合：从独立比较到 Hilbert 张量积

第 43 节给出单系统的连续动力学。两个系统如何形成一个整体，可以继续只用比较关系表达：独立系统的两两比较值相乘。

**定义 44.1（独立复合比较公理）。** 对两个已有复比较系统 $A,B$，要求存在复合系统 $AB$，使产品准备满足

$$
 h_{AB}(x\otimes u,y\otimes v)
 =h_A(x,y)h_B(u,v).
$$

同时要求：

1. **结合相容：** 三系统的两种括号化 $(AB)C$ 与 $A(BC)$ 由保持比较的自然等距同构连接；
2. **交换相容：** 交换 $A,B$ 的映射保持比较并满足交换两次为恒等；
3. **局部比较完备：** 有限维中，若两个整体状态对所有产品效应都给出相同读数，则它们相同：
   $$
   \operatorname{Tr}\bigl((\rho-\sigma)(E\otimes F)\bigr)=0
   \quad\text{对所有 }E,F
   \quad\Longrightarrow\quad \rho=\sigma.
   $$

第一条是乘法关系的结合律，第三条排除产品比较永远看不见的隐藏整体扇区。

**定理 44.2（乘法比较生成 Hilbert 张量积）。** 在有限维复 Hilbert 系统上，定义 44.1 的前两条唯一生成标准 Hilbert 张量积

$$
H_{AB}=H_A\otimes H_B,
$$

其简单张量内积为

$$
 h_{AB}(x\otimes u,y\otimes v)
 =h_A(x,y)h_B(u,v).
$$

**证明。** 在代数张量积 $H_A\odot H_B$ 上对简单张量规定上述内积，并按共轭双线性延拓到有限和。正性来自两个 Gram 矩阵的 Kronecker 乘积仍为正半定；商去零范数后完备化，得到 $H_A\otimes H_B$。结合律和交换律由有限和上的规范重排给出，并延拓为保持内积的酉同构。证毕。

**定理 44.3（乘积 Born 概率和纠缠）。** 对产品准备和产品效应，有

$$
 h_{AB}(x\otimes u,(E\otimes F)(x\otimes u))
 =h_A(x,Ex)h_B(u,Fu).
$$

因此独立概率相乘。张量积的线性完备化还包含一般向量

$$
\Psi=\sum_{i,j}c_{ij}e_i\otimes f_j,
$$

当系数矩阵 $c_{ij}$ 的秩大于一时，$\Psi$ 不能写成单一产品 $x\otimes u$；Schmidt 分解给出其纠缠谱。纠缠不是另加的对象公理，而是乘法比较空间的线性闭包。

**定理 44.4（有限维局部比较完备）。** 在 $H_A\otimes H_B$ 中，产品 Hermitian 算子 $A\otimes B$ 的线性张成包含整个 Hermitian 算子空间。因为每个正算子乘以足够小的正标量就是效应，所有产品效应的线性张成也相同。于是若 $\rho-\sigma$ 对所有 $E\otimes F$ 的迹配对为零，则对所有整体 Hermitian 算子配对为零，故 $\rho=\sigma$。

**命题 44.5（删除复合条件的反例）。**

1. **删除局部完备：** 令整体空间扩张为
   $$
   \widetilde H_{AB}=(H_A\otimes H_B)\oplus K,
   $$
   并让所有产品效应在 $K$ 上作用相同。$K$ 中两个不同状态对所有产品比较给出相同读数，却可被整体效应区分，形成隐藏扇区。
2. **删除结合律：** 可以让 $(AB)C$ 和 $A(BC)$ 各自拥有同样的产品边缘，却附带不同的括号依赖隐藏空间；没有保持比较的结合子时，三系统的整体状态不唯一。
3. **删除乘法因子化：** 即使两边各自是量子 Hilbert 空间，联合比较仍可选择非乘法的相关律，产品 Born 概率和标准张量积都不再被强迫。
4. **删除复合的物理可实现性：** 数学张量积不自动给出相对论局域性、实际相互作用或所有产品效应的实验可取得性。

**定理 44.6（与现有量子复合公理的对应和边界）。** 独立复合比较公理给出：

- Hilbert 张量积和其结合/交换同构；
- 产品态的乘法 Born 概率；
- Schmidt 分解、纠缠谱和产品测量；
- 有限维局部层析，即产品比较足以识别整体状态。

它不单独给出开放系统的完全正通道、相对论无信号约束、相互作用 Hamiltonian 或实验可实现性；这些属于通道、动力学和经验桥梁。

**候选 44.7（最简独立复合公理）。** 两个比较网络的独立复合由一个乘法关系给出；所有三重组合必须结合相容，交换只改变标签；若所有产品比较已相同，整体状态就必须相同。由此标准张量积和纠缠自动出现，隐藏扇区被排除。复合的本体仍是关系的关系，而不是预先指定的坐标乘法。

白话说：两台机器各自比较时，独立联合比较就是两边答案相乘。三台机器怎样先括哪两台，最后都必须得到同一张比较网；交换机器标签只改变名字。若所有“左边一个问题、右边一个问题”的答案都一样，整体状态也必须一样，否则就有一间局部仪器永远看不见的隐藏房间。满足这些条件后，张量积和纠缠不是额外魔法，而是乘法比较的线性闭包自然长出来的结构。

## 45. 辅助系统稳定的比较保持：从关系映射到 Kraus 通道

第 44 节给出复合系统。开放系统的变换不能只在单个系统上保持正性，因为它还必须在任何联合比较网络中保持正性。

**定义 45.1（完全比较保持公理）。** 对有限维系统 $A,B$，令

$$
\Phi:M_A(\mathbb C)\longrightarrow M_B(\mathbb C)
$$

为线性映射。要求：

1. **辅助稳定正性：** 对每个有限维辅助系统 $C$，
   $$
   \operatorname{id}_C\otimes\Phi
   $$
   把所有正半定算子送到正半定算子；
2. **比较预算：** 对确定性变换，
   $$
   \operatorname{Tr}\Phi(\rho)=\operatorname{Tr}\rho,
   $$
   对后选择变换则只要求 $\operatorname{Tr}\Phi(\rho)\le\operatorname{Tr}\rho$。

第一条把“保持正性”提升为对所有关系的联合保持，第二条把概率总量作为守恒或消耗预算。

**定理 45.2（Choi 正性和 Kraus 表示）。** 定义 45.1 的第一条等价于 Choi 矩阵

$$
J_\Phi=(\operatorname{id}_A\otimes\Phi)\bigl(|\Omega\rangle\langle\Omega|\bigr)
$$

正半定，其中 $|\Omega\rangle=\sum_i e_i\otimes e_i$。若

$$
J_\Phi=\sum_\alpha\lambda_\alpha|v_\alpha\rangle\langle v_\alpha|,
\qquad \lambda_\alpha\ge0,
$$

把 $\sqrt{\lambda_\alpha}v_\alpha$ 按向量化反变换为算子 $K_\alpha$，则

$$
\Phi(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^*.
$$

并且

$$
\sum_\alpha K_\alpha^*K_\alpha=I_A
$$

当且仅当 $\Phi$ 保迹；若只要求不增迹，则左边 $\le I_A$。

**证明。** 完全正性直接给出 $J_\Phi\succeq0$，因为它是一个最大纠缠正态在辅助稳定映射下的像。反向地，$J_\Phi\succeq0$ 的谱分解给出上述 $K_\alpha$；对任意正半定 $X$，将 $X$ 写成有限平方和并使用 $J_\Phi$ 的正性，可得 $(\operatorname{id}_C\otimes\Phi)(X)\succeq0$，故 $\Phi$ 完全正。对 Kraus 式取迹，得到

$$
\operatorname{Tr}\Phi(\rho)
=\operatorname{Tr}\left(\rho\sum_\alpha K_\alpha^*K_\alpha\right),
$$

于是对所有 $\rho$ 保迹恰好等价于算子和为 $I_A$。证毕。

**命题 45.3（单系统正性不足的转置反例）。** 转置映射

$$
\tau(\rho)=\rho^T
$$

在单系统上保持正性和迹，但它不是完全正。对 Bell 态

$$
|\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2}
$$

有

$$
(\operatorname{id}\otimes\tau)\bigl(|\Phi^+\rangle\langle\Phi^+|\bigr)
$$

的特征值为

$$
\frac12,\frac12,\frac12,-\frac12.
$$

因此只检查单系统比较，会把一个在联合系统上产生负概率的映射误收为物理通道。辅助稳定性正是排除此反例的最小关系提升。

**定理 45.4（通道、instrument 与 Lüders 边界）。**

- 保迹完全正映射是确定性量子通道；
- 保完全正且不增迹的映射是后选择分支；
- 一族 $\{\mathcal I_k\}$ 若每个分支完全正不增迹且 $\sum_k\mathcal I_k$ 保迹，则构成 quantum instrument；其效应为
  $$
  E_k=\mathcal I_k^*(I);
  $$
- 对锐投影 $P_k$，若再要求重复测量保持同一锐事件并满足最小扰动，才得到 Lüders 形式
  $$
  \mathcal I_k(\rho)=P_k\rho P_k.
  $$

所以完全正性和总迹守恒给出通道及 instrument，却不能单独选择 Lüders 更新；更新原则仍是独立的锐事件压缩条件。

**命题 45.5（删除条件的边界）。**

1. 删除辅助稳定性，转置等正但非完全正映射被允许；
2. 删除迹预算，映射可以任意放大或缩小总概率，不能解释确定性演化；
3. 只给 Choi 正性而不规定输出系统和线性组合，不能得到可组合通道；
4. 完全正和保迹不蕴含相对论局域性、实验可实现的 Kraus 限制或具体测量后状态。

**候选 45.6（最简开放系统公理）。** 一个物理变换就是对所有辅助比较网络都保持正性的线性关系映射，并按是否确定性守恒比较总量。Choi 正性把“所有辅助系统”压成一个矩阵检验，谱分解把通道展开为 Kraus 关系；instrument 是带分支的预算分解，Lüders 规则则是锐事件的额外最小扰动条件。

白话说：一台机器单独工作时看起来不产生负概率，还不够；把它接到任何辅助机器上，也不能把联合比较变成负数。这个“对所有辅助系统都安全”的要求就是完全正性。Choi 矩阵把所有辅助测试压成一次检查，Kraus 算子是这次检查的分解。若总概率守恒，就是通道；若概率被分到不同结果，就是 instrument；测量后究竟保留哪一个状态，还需要 Lüders 的最小扰动原则。

## 46. 固定点压缩：把比较顺序无关写成最小闭包

最新 dev 的关系 TOE 卷把几何、操作和记录组织成单调生成算子；这给“先比较哪一对”提供了比逐条交换更准确的解释。规则采用顺序无关，不等于每两条规则在每一步都交换，而是所有公平的构造顺序最终得到同一个最小闭包。

**定义 46.1（有限关系闭包）。** 令 $\mathscr R$ 为有限关系记录的集合，$S\subseteq\mathscr R$ 为种子。每一条生成规则给出单调算子

$$
\Phi_i:\mathcal P(\mathscr R)\longrightarrow\mathcal P(\mathscr R),
\qquad
S\subseteq S'\Longrightarrow\Phi_i(S)\subseteq\Phi_i(S').
$$

把规则合并为保持膨胀性的算子

$$
\Phi(T)=T\cup\bigcup_i\Phi_i(T).
$$

称 $T$ 为闭集，若 $\Phi(T)=T$；种子上的最小闭包定义为

$$
\operatorname{Cl}_\Phi(S)=\bigcap\{T\subseteq\mathscr R:S\subseteq T\land\Phi(T)=T\}.
$$

**定理 46.2（公平顺序的闭包不变性）。** 假设每条规则是有限前提规则：新记录的产生只依赖某个有限的已出现记录集。令

$$
S_0=S,\qquad S_{n+1}=\Phi(S_n),\qquad S_\omega=\bigcup_{n<\omega}S_n.
$$

则 $S_\omega=\operatorname{Cl}_\Phi(S)$。更一般地，若异步构造每一步只添加某个 $\Phi_i$ 已许可的记录，永不删除记录，并且对每个最终仍可触发的有限前提最终都会执行相应规则，则其并集也等于 $\operatorname{Cl}_\Phi(S)$。因此规则的公平采用顺序不改变结果。

**证明。** 任意包含 $S$ 的闭集 $T$ 都包含每个 $S_n$：$S_0\subseteq T$，若 $S_n\subseteq T$，单调性和闭性给出 $S_{n+1}=\Phi(S_n)\subseteq\Phi(T)=T$。故 $S_\omega\subseteq\operatorname{Cl}_\Phi(S)$。有限前提性使 $S_\omega$ 对每条规则闭合：若某记录的有限前提均在 $S_\omega$ 中，它们已在某个共同的 $S_N$ 中，于是该记录在 $S_{N+1}$ 出现。因此 $S_\omega$ 是包含 $S$ 的闭集，得到反向包含。异步情形中，公平性保证每个有限前提一旦全部出现就会被加入，故异步并集同样闭合；它又包含同步迭代可生成的每条记录，因而与最小闭包相等。证毕。

这里的有限前提和公平性是实质条件。若规则允许“只有在已经出现无限全集时才触发”的前提，有限迭代可能永远看不到它；若允许永久跳过某条已许可规则，顺序也可能改变所得到的非闭集合。因而不能把任意程序执行的偶然结果冒称为顺序无关。

**定义 46.3（正比较闭包候选）。** 在每个记录中只把二元比较表 $K$ 作为原始关系，并要求：

1. $K(y,x)=\overline{K(x,y)}$，且自比较归一；
2. 每个有限比较表半正定；
3. 取子记录和重排只取限制与置换；
4. 记录生成规则构成定义 46.1 的有限前提、单调、可公平执行的闭包。

候选公理是：实际关系账本是 $\Lambda=\operatorname{Cl}_\Phi(S)$，并满足 $\Phi(\Lambda)=\Lambda$。这里没有把向量、Hilbert 空间或 Born 数值写进原始记录。

**定理 46.4（固定点候选的几何内容）。** 正比较闭包候选给出两项且仅给出两项基础结论：

1. 闭包的构造顺序在公平条件下不影响最终关系账本；
2. 有限正比较表经 GNS 商与完备化得到 Hilbert Gram 实现 $K(x,y)=\langle\psi_x,\psi_y\rangle$。

**证明。** 第一项是定理 46.2。第二项对闭包中所有有限记录的限制表应用第 37 节的极化构造；限制相容保证同一对对象的值唯一，半正定性保证商空间上的半内积，完备化得到 Hilbert 空间。两项之间没有额外的物理假设。证毕。

固定点本身不等于完整量子理论。令规则只有恒等闭包，并取任意实对称正定核，则候选已经满足固定点和全有限正性，却没有复相位、测量读出、时间参数、复合系统或开放通道。要得到现有量子公理，必须把相应关系作为明确的闭包规则加入：正交复结构 $J^2=-I$ 选择复分支；框架无关归一化选择 Born 读出；乘法独立复合生成张量积；可逆强连续流生成 Wigner–Stone 动力学；辅助稳定正性生成 CP/Kraus 通道。固定点只保证这些规则的加入顺序不改变其共同闭包，不替它们承担内容。

**候选 46.5（最简内生量子公理）。** 世界是有限成对比较关系的最小正闭包：每个有限关系表都非负可实现，所有规则只通过有限前提生成关系，并且最终账本是公平生成顺序下唯一的最小不动点。Hilbert 几何是该闭包的 GNS 表示；复结构、Born、动力学、张量和 CP 分别是闭包中额外声明的最小关系桥，而不是外部坐标输入。

白话说：先有一张只记录“两件东西怎样比较”的账。任何一步只许从已经存在的有限关系推出新关系；你先登记哪一对、先展开哪一条规则，只要不永久漏掉合法步骤，最后得到的是同一张最小完整账。账上的所有有限比较不能拼出负平方长度，于是它自动摊成 Hilbert 几何。复数、概率、时间和开放系统不是被一句“顺序无关”偷偷推出，而是分别作为相位、读出、流和辅助稳定性的关系桥接入同一个闭包。


## 47. 再压缩的极限：二次不变量与闭包算子

第 46 节把采用顺序压成闭包算子，把几何相容压成有限正性。再向下删去任何一项之前，必须先问：剩下的关系能否区分不同的标量分支和读出律？答案是否定的，这给出继续简化的边界。

**定义 47.1（裸正关系骨架）。** 一个裸骨架是三元组

$$
\mathfrak B=(P,K,\operatorname{Cl}),
$$

其中 $P$ 是对象集，$K:P\times P\to\mathbb R$ 是归一化对称核，所有有限主表半正定，$\operatorname{Cl}$ 是记录幂集上的 extensive、monotone、idempotent 闭包算子。闭包只读取记录和 $K$ 的有限限制，不读取实现它们的坐标、标量域或测量解释。

**定理 47.2（裸骨架不能选择数域分支）。** 若裸骨架有一个实 Hilbert 实现 $\iota:P\to H_{\mathbb R}$，则它同时有复实现和四元数实现：

$$
\iota_{\mathbb C}(x)=\iota(x)\otimes 1
\in H_{\mathbb R}\otimes_{\mathbb R}\mathbb C,
\qquad
\iota_{\mathbb H}(x)=\iota(x)\otimes 1
\in H_{\mathbb R}\otimes_{\mathbb R}\mathbb H.
$$

三种实现对 $P$ 的成对比较都等于同一个 $K$，并且诱导同一个 $\operatorname{Cl}$。因此仅由裸骨架可证明的命题不能断言“基本标量必为 $\mathbb C$”，也不能断言存在非平凡 $U(1)$ holonomy。

**证明。** 实数嵌入 $r\mapsto r\otimes1$ 保持乘法、加法和共轭；对来自 $H_{\mathbb R}$ 的向量，复内积和四元数内积都退化为原来的实内积。因此

$$
\langle\iota_{\mathbb C}(x),\iota_{\mathbb C}(y)\rangle=K(x,y),
\qquad
\langle\iota_{\mathbb H}(x),\iota_{\mathbb H}(y)\rangle=K(x,y).
$$

闭包只读取 $P$、$K$ 和有限记录，故标量扩展不改变它。三种模型满足完全相同的裸骨架，而复数和四元数的额外方向在该骨架上没有观测项。证毕。

**命题 47.3（裸骨架不能选择 Born 读出）。** $K$ 只给出状态之间的比较，不给出事件集合、框架归一化或读出函数。因而从裸骨架不能推出

$$
 p_\psi(e)=|\langle e,\psi\rangle|^2.
$$

要得到这个式子，至少必须加入秩一事件的非上下文读出、正交框架总和为一以及维数至少三的条件；在这些条件下才可用 Gleason 型论证把读出固定为正算子期望。删除任一桥，裸骨架仍保持不变，而读出问题没有被决定。

**命题 47.4（固定点不自动产生开放系统）。** 即使 $\operatorname{Cl}$ 是唯一的最小闭包，单系统的正比较仍不能排除转置等正但非完全正映射。只有把“对每个辅助比较网络保持正性”写入闭包规则，才得到 CP/Kraus 结构；固定点只保证这条规则与其他规则的加入顺序相容。

由定理 47.2，复分支不能从实二次骨架中凭空出现。最小的内生分支选择是加入一个与二次型相容的正交算子 $J$，满足

$$
J^2=-I,
\qquad
Q(J\mu)=Q(\mu).
$$

若还要求相位稳定子群的连通紧部分是一维交换群，才排除四元数 $Sp(1)$ 分支并选出 $U(1)$。这正是前面 $g$、$\omega$ 和相位稳定子条件的不可删除部分，而不是坐标命名。

**定理 47.5（再压缩的最小诚实候选）。** 在不把复结构、事件读出、复合或辅助系统预先写进定义的前提下，最小可闭合候选可写成一个带类型的二元对象

$$
\mathfrak Q_{\min}=(\operatorname{Cl},Q),
$$

其中 $\operatorname{Cl}$ 是 extensive、monotone、idempotent 且由有限前提公平生成的关系闭包，$Q$ 是形式差空间上的非负二次不变量，满足

$$
Q(t\mu)=t^2Q(\mu),
\qquad
Q(\mu+\nu)+Q(\mu-\nu)=2Q(\mu)+2Q(\nu).
$$

它等价于“有限正比较核 + 最小闭包”：

$$
\boxed{
\text{物理账本是最小闭包，且其每个有限差的二次能量非负。}
}
$$

该候选恰好推出顺序无关的共同闭包和实 Hilbert 几何；它不能再推出复数、Born、动力学、张量或 CP。任何声称仅用 $\mathfrak Q_{\min}$ 得到这些结论的证明，必然在中间偷偷加入相应的分支或读出条件。

**证明。** $\operatorname{Cl}$ 的三条闭包律和公平有限生成给出第 46 节的顺序不变性。$Q$ 的齐次性、平行四边形恒等式和正性经极化得到实内积，商去零空间并完备化得到实 Hilbert 几何。定理 47.2 给出实、复、四元数模型的同一骨架；命题 47.3 和 47.4 分别给出读出和开放系统的独立缺口。因此结论是可推出内容的精确上界。证毕。

**候选 47.6（量子起源的最短白话）。** 世界不是先给出坐标和物理公式，而是先给出一份能自洽闭合的成对比较账。账的所有有限差必须有非负二次能量，所有有限规则的公平闭包必须唯一。这样首先得到实 Hilbert 几何；复相位、Born 概率、时间、张量和开放通道，只有在各自的关系桥被明确加入后才出现。


## 48. 自对偶锥的复分支选择：纯化与局部层析

第 35 节已经把比较压成自对偶齐性正锥，但正锥本身保留经典、实、复和四元数分支。结合 `dev` 的几何—操作—记录闭包，可以把选择条件集中到两个可观测的组合性质：纯化和局部层析。

**定义 48.1（对称复合比较锥）。** 对每个有限系统 $A$，给出有限维实向量空间 $V_A$、闭尖生成锥 $C_A$、序单位 $u_A$ 和内积 $\langle-,-\rangle_A$，要求：

1. **自对偶齐性：**
   $$
   C_A=\{x\in V_A:\langle x,y\rangle_A\ge0\text{ 对所有 }y\in C_A\},
   $$
   且锥内部的任意两点由保持锥的线性自同构互相到达；
2. **状态与效果：** $\Omega_A=\{\rho\in C_A:\langle u_A,\rho\rangle_A=1\}$，效果是对偶区间 $0\le e\le u_A$；
3. **独立复合：** 存在 $A\otimes B$，产品状态和产品效果生成其指定的局部关系；
4. **局部层析：** 整体状态由所有产品效果 $e_A\otimes e_B$ 的读数唯一决定；
5. **纯化：** 每个 $\rho\in\Omega_A$ 都是某个联合纯态 $\Psi_{AB}$ 的 $B$ 边缘，并且同一边缘的纯化只相差 $B$ 上的可逆变换。

这组条件仍以正锥、对偶配对和关系读数为原语，没有先写复矩阵。

**定理 48.2（自对偶齐性先给 Jordan 几何）。** 在定义 48.1 的有限维闭、尖、生成、自对偶齐性条件下，$V_A$ 可赋予 Euclidean Jordan 代数乘法，使 $C_A$ 正好是平方元锥，$u_A$ 是 Jordan 单位；每个状态具有有限谱分解，效果读数是正的双线性配对。

**证明。** 这是 Koecher–Vinberg 对称锥表示的应用：闭、尖、生成、自对偶且齐性的锥是对称锥，而每个对称锥由 Euclidean Jordan 代数的平方元生成。Jordan 谱分解给出状态的正特征值分解；对偶区间给出效果，配对的正性和序单位归一化给出概率读数。证毕。

该定理只得到 Jordan 分支，尚未选择复 Hilbert 量子理论。经典单纯形、实对称正定锥、复 Hermitian 正定锥和四元数自伴正锥都在其范围内。

**命题 48.3（局部层析的维数筛选）。** 令 $a,b>1$ 为两个局部 Hilbert 维数。实、复、四元数自伴空间的实维数分别为

$$
 r(d)=\frac{d(d+1)}2,
\qquad
 c(d)=d^2,
\qquad
 q(d)=2d^2-d.
$$

复分支满足

$$
 c(ab)=c(a)c(b),
$$

而实、四元数分支分别满足

$$
 r(ab)-r(a)r(b)=\frac{ab(a-1)(b-1)}4>0,
$$

$$
 q(ab)-q(a)q(b)=-2ab(a-1)(b-1)\ne0.
$$

因此产品效果不能在实或四元数分支中局部层析地识别全部联合状态；复分支的维数恰好满足局部层析的乘法。

**证明。** 产品效果张成的线性读数空间维数至多为局部维数乘积。局部层析要求它等于整体自伴空间维数。代入上式直接得到三个差值；$a,b>1$ 时实、四元数差值不为零，而复分支相等。证毕。

**命题 48.4（纯化排除经典分支）。** 经典单纯形锥 $\mathbb R_+^n$ 的纯态是单点分布。任意经典联合纯态也是单点分布，其边缘仍是单点分布。因此非退化混合分布不能由经典联合纯态纯化，定义 48.1 的纯化条件排除经典分支。

**证明。** 经典联合纯态的全部质量集中在一个 $(i,j)$ 上，取 $B$ 边缘后全部质量集中在 $i$ 上。含有两个正坐标的混合分布不可能这样得到。证毕。

**定理 48.5（复分支选择的条件范围）。** 若另行假设：

1. 每个简单有限系统的 Jordan 代数属于标准矩阵分支或已被组合公理排除的例外分支；
2. 复合对所有系统存在并满足定义 48.1 的局部层析与纯化；
3. 可逆变换在内部状态上连续且作用足够丰富；

则命题 48.3 和命题 48.4 排除经典、实和四元数标准分支，剩下复 Hermitian 矩阵锥作为量子分支。此处“剩下”依赖第 1、2 条的分类与组合存在定理；Koecher–Vinberg 本身不排除异常 $H_3(\mathbb O)$，也不供应任意两个 Jordan 系统的复合。

在复分支中，Jordan 谱分解和 Hilbert–Schmidt 对偶恢复正算子、投影事件与

$$
 p_\rho(E)=\operatorname{Tr}(\rho E)
$$

的 Born 读数。若要求所有辅助系统上的正性，得到 CP 映射和 Kraus 分解；若要求可逆强连续的一参数群，Stone 定理给出 Hamiltonian；锐事件的最小扰动仍需单独加入 Lüders 条件。

**候选 48.6（最简锥几何量子公理）。** 一个量子世界是带自对偶齐性正锥的对称复合关系系统；其复合同时满足局部层析和纯化，关系闭包取最小不动点。Jordan 几何由锥定理产生，经典分支由纯化排除，实/四元数分支由局部层析的维数障碍排除；复 Hilbert、Born、CP 和 Stone 仍分别依赖标准分支、效果、辅助正性和连续时间的对应定理。

白话说：先不要画复向量，先画一块允许的“正区域”。区域的镜像是自己，内部状态可以互相搬动；两台系统合起来时，局部问题足以看见整体，任何混合状态又都能藏在更大的纯关系里。经典区域做不到纯化，实和四元数区域的联合维数也对不上，只有复矩阵区域同时通过这两道筛选。这个候选比直接写复 Hilbert 坐标更原始，但它仍然需要异常锥的排除、组合存在性和动力学桥梁，不能冒称单独完成物理起源证明。
