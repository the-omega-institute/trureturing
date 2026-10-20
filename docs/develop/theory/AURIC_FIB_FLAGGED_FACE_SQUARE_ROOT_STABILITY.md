# AURIC FIB 最优面的平方根稳定性、最优指数与双证书间隙

在全复输入 $M_5$、保留二值经典旗标和原五维量子寄存器、任意未读取有限参考以及不折半菱形范数下，本文证明：首次完整 PVM 外部松弛中的通道若只有支撑亏损 $d=65-F(\mathcal T)$，则到整个支撑极大面 $\mathcal M$ 的距离至多 $256\sqrt d$。一个只用固定完整 PVM 与全寄存器相位幺正的实际协议族证明，任何大于 $1/2$ 的统一局部指数都不成立。对同一个通道联合使用支撑与相干证书，还得到显式距离增量

$$
\Delta_{1/2}=\frac{(U_0-L)^2}{2^{17}N^2}>2^{-36}.
$$

本文的证据上限是以所供数学接口和理想精确模型为条件的、可出错的 **UNEXECUTED 符号数学**：没有执行算术验证，也没有 Lean/kernel 核验。以下以 [E] 表示《[AURIC FIB 近支撑极大的显式四次根稳定性与同一通道的有效距离间隙](AURIC_FIB_EFFECTIVE_FLAGGED_PROJECTIVE_GAP.md)》。支撑最大值、整个极大面、规范 Kraus 残差、测量方向校正、相干测试及角度与停止接口均继承 [E]；新增的综合是残差控制的校正分数比较、平方根吸收、合法的整个面尖锐性构造和更强的同通道显式下界。Cauchy–Schwarz、Kraus 堆叠、正矩阵迹估计、凸凹性与有限维紧性是标准工具；外部优先权及文献完整性未确立。

## 1. 固定模型、实际菜单与继承接口

**定义 1.1（输入、输出与范数）。** 令 $H=\mathbb C^5$，正交基为 $e_0,\ldots,e_4$，内积对第一变量共轭线性。置

$$
\begin{gathered}
s=e_2,\qquad S=|s\rangle\langle s|,\\
P=|e_0\rangle\langle e_0|+|e_4\rangle\langle e_4|,\qquad
Q=|e_1\rangle\langle e_1|+|e_3\rangle\langle e_3|,\\
P_0=P,\quad P_1=Q,\quad P+Q+S=I_5,\\
H_j=P_j+\frac{S}{\sqrt2},\qquad C_j=2P_j+3S,\qquad
\widehat{\mathcal J}(X)=\bigoplus_{j=0}^1H_jXH_j.
\end{gathered}
\tag{1.1}
$$

这里 $X$ 遍历全部复矩阵 $M_5$，输出直和保存原二值经典旗标及原五维量子系统。因为 $H_0^2+H_1^2=I_5$，目标是归一化通道。对矩阵 $B$，记 $\operatorname{Ad}_B(X)=BXB^\dagger$；$\|B\|_\infty$ 为算子范数，$\|B\|_{\rm HS}^2=\operatorname{Tr}(B^\dagger B)$，$\|B\|_1=\operatorname{Tr}\sqrt{B^\dagger B}$。采用

$$
\|\Lambda\|_\diamond=
\sup_{k\ge1}\sup_{0\ne X\in M_5\otimes M_k}
\frac{\|(\Lambda\otimes\operatorname{id}_{M_k})(X)\|_1}{\|X\|_1}.
\tag{1.2}
$$

所有有限参考均不被读取，测试包括任意复算符，范数没有因子 $1/2$。[E] 定义 1.1 固定了同一对象与范数。

**定义 1.2（实际协议与三个类）。** 实际菜单只有全五维寄存器上的幺正、完整 Lüders PVM、可测且输入独立的经典硬币、自适应经典反馈和末端记录到二值旗标的粗化。全部测量结果及概率质量均保留；没有额外量子寄存器或能级、重置、非投影测量原语、任意 CPTP 后处理原语、参考读取或后选择。

$\mathfrak S_{\rm fin}$ 表示有统一有限操作深度上界的实际协议，$\mathfrak S_{\rm as}$ 表示对每个输入几乎必然有限终止的实际协议，$\mathfrak S_{\rm cl}=\overline{\mathfrak S_{\rm fin}}^{\diamond}$。硬币可预采样为包含所有可能反馈历史选择的整条输入独立经典带；这不把量子测量结果改为输入独立。定义与 [E] 定义 1.1 相同。

**定义 1.3（外部松弛与原索引）。** $\mathcal K$ 包含两类归一化带旗标通道。无非平凡首次分拆的一类仅为一个全空间幺正并报告一个确定旗标。另一类具有非平凡完整首次 PVM $\{E_\alpha\}$，随后允许代数 CP 后代。为每个后代保留首次结果 $\alpha$、原旗标 $j$ 与细 Kraus 索引 $t$，写 $\ell=(\alpha,j,t)$，要求

$$
L_\ell=L_\ell E_\alpha,\qquad
\sum_{\ell:\,\text{首次结果为 }\alpha}L_\ell^\dagger L_\ell=E_\alpha.
\tag{1.3}
$$

等价地，后代 CP 映射 $\Psi_{\alpha j}$ 满足 $\sum_j\Psi_{\alpha j}^\dagger(I_5)=E_\alpha$，通道第 $j$ 块为 $\sum_\alpha\Psi_{\alpha j}$。置

$$
\mathcal C=\overline{\operatorname{conv}}(\mathcal K).
$$

一般 CP 后代只是外部松弛；无分拆分量绝不扩为任意秩五 CP 续行。这是 [E] 定义 2.4 的量词。根据 [E] 命题 2.5，$\mathcal K$ 紧，$\mathcal C=\operatorname{conv}(\mathcal K)$ 紧凸，且 $\mathfrak S_{\rm fin}\subseteq\mathcal C$。这些事实没有反向的实际可实施性含义。

**定义 1.4（分数、面与距离常数）。** 对原旗标 Kraus 家族置

$$
F(\mathcal T)=\sum_\ell|\operatorname{Tr}(C_{j_\ell}^\dagger L_\ell)|^2,
\qquad d(\mathcal T)=65-F(\mathcal T).
\tag{1.4}
$$

$F$ 是未缩放的分数。它是通道的线性函数，与 Kraus 表示无关，不能与归一化重叠 $F/N^2$ 混用。定义

$$
\begin{gathered}
\mathcal A_+=(\operatorname{Ad}_{P+S},\operatorname{Ad}_Q),\qquad
\mathcal A_-=(\operatorname{Ad}_P,\operatorname{Ad}_{Q+S}),\\
\mathcal A_\lambda=\lambda\mathcal A_++(1-\lambda)\mathcal A_-,\qquad
\mathcal M=\{\mathcal A_\lambda:0\le\lambda\le1\},\\
N=3+4\sqrt2,\qquad N^2=41+24\sqrt2,\\
L=2\left(1-\frac{65}{N^2}\right)
=\frac{48(\sqrt2-1)}{N^2},\qquad
U_0=1-\frac1{\sqrt2},\qquad g=U_0-L.
\end{gathered}
\tag{1.5}
$$

每个端点是完整 PVM 协议，每个 $\mathcal A_\lambda$ 是同一个输入独立硬币的有限深度混合，故 $\mathcal M\subseteq\mathfrak S_{\rm fin}$。记 $\operatorname{dist}_\diamond(\mathcal T,\mathcal M)=\inf_{\mathcal A\in\mathcal M}\|\mathcal T-\mathcal A\|_\diamond$。[E] 定义 1.2、定义 2.2、命题 2.3、命题 3.2 与定理 5.1 给出

$$
\max_{\mathcal C}F=65,\qquad
\{\mathcal T\in\mathcal C:F(\mathcal T)=65\}=\mathcal M.
\tag{1.6}
$$

因此 $0\le d\le65$。本文保持这一支撑值与完整线段，不把某个端点当作整个面。

**命题 1.5（需要的范数、见证与几何接口）。** 以下均为 [E] 中给出的接口。

第一，有限维 CP 映射 $\Psi$ 满足

$$
\|\Psi\|_\diamond=\|\Psi^\dagger(I)\|_\infty.
\tag{1.7}
$$

归一化通道的范数为一，两通道距离至多二。这是 [E] 引理 2.1，包含全部复测试与有限参考。为明确后文堆叠的适用性，若 $V$ 是 Kraus 堆叠，则 $\Psi(X)=\operatorname{Tr}_E(VXV^\dagger)$，$V^\dagger V=\Psi^\dagger(I)$。迹范数对偶性给出

$$
\|\operatorname{Tr}_E Y\|_1
=\sup_{\|Z\|_\infty\le1}|\operatorname{Tr}[(Z^\dagger\otimes I_E)Y]|
\le\|Y\|_1
$$

对所有复 $Y$ 成立。张量任意参考后，乘法界给出 (1.7) 的上界；取效应的最大本征值纯态得到下界。

第二，[E] 定义 2.2、命题 2.3 的固定见证是

$$
\begin{gathered}
\rho=\frac{\sqrt2(P+Q)+3S}{N},\qquad
\psi_\rho=\sum_{k=0}^4\sqrt{\rho_{kk}}\,e_k\otimes e_k,\\
|B\rangle\!\rangle=\sum_kBe_k\otimes e_k,\qquad
a_j=\sqrt2\,|H_j\sqrt\rho\rangle\!\rangle,\qquad
\Pi=\bigoplus_j|a_j\rangle\langle a_j|.
\end{gathered}
\tag{1.8}
$$

$\psi_\rho,a_j$ 归一化，$\Pi$ 是投影，且

$$
\begin{gathered}
F(\mathcal T)=N^2\operatorname{Tr}\!\left[\Pi(\mathcal T\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|)\right],\\
b(\mathcal T):=2\left(1-\frac{F(\mathcal T)}{N^2}\right)
\le\|\widehat{\mathcal J}-\mathcal T\|_\diamond,\\
|F(\mathcal T)-F(\mathcal T')|\le N^2\|\mathcal T-\mathcal T'\|_\diamond.
\end{gathered}
\tag{1.9}
$$

这里的归一化由 $\operatorname{Tr}\rho=1$、$\operatorname{Tr}(\rho H_j^2)=1/2$ 及 $\sqrt2\rho H_j=C_j/N$ 固定。目标见证输出是 $\frac12\bigoplus_j|a_j\rangle\langle a_j|$，所以完整二元测试 $\{\Pi,I-\Pi\}$ 给出不折半下界 $b$。

第三，[E] 命题 3.2 给出：一个 $\mathcal K$ 分量若没有秩 $3+2$ 的首次 PVM，则 $d\ge1/6$。若它的秩三首次投影是 $E$，[E] 引理 4.1 给出某个

$$
E_0\in\{P+S,Q+S\},\qquad \|E-E_0\|_{\rm HS}^2\le6d.
\tag{1.10}
$$

[E] 引理 4.2 随后给出幺正 $U$，满足

$$
UEU^\dagger=E_0,\qquad
u:=\|U-I\|_\infty\le\sqrt2\|E-E_0\|_\infty\le\sqrt{12d}.
\tag{1.11}
$$

校正后的通道必须是

$$
\mathcal B=\mathcal T\circ\operatorname{Ad}_{U^\dagger},\qquad
B_\ell=L_\ell U^\dagger,\qquad
\mathcal T=\mathcal B\circ\operatorname{Ad}_U,
\qquad\|\mathcal T-\mathcal B\|_\diamond\le2u.
\tag{1.12}
$$

事实上 $(L_\ell U^\dagger)E_0=L_\ell U^\dagger$，同支完整效应变为 $UEU^\dagger$；仅旋转输出不校正输入右支撑。主角构造在每个正交二维平面把第一子空间主向量转到第二子空间主向量；角为零时固定，重复角各平面独立，直角同样可转。平面上 $\|U-I\|=2\sin(\theta/2)\le\sqrt2\sin\theta$，而投影差范数为 $\sin\theta$，故退化情形也包含于 (1.11)。两项幺正展开及 (1.7) 给出 (1.12) 的距离界。这些校正是分析步骤，没有给实际菜单添加原语。

**定理 1.6（本文的定量结论）。** 对每个 $\mathcal T\in\mathcal C$，

$$
\operatorname{dist}_\diamond(\mathcal T,\mathcal M)\le256\sqrt{65-F(\mathcal T)}.
\tag{1.13}
$$

对 $\mathcal T\in\mathcal K$ 可取某个端点 $\mathcal A_{\rm end}\in\{\mathcal A_+,\mathcal A_-\}$ 为比较点。指数 $1/2$ 在 $\mathcal C,\mathcal K,\mathfrak S_{\rm fin},\mathfrak S_{\rm as},\mathfrak S_{\rm cl}$ 上均为最优统一局部幂指数。同一 $\mathcal T\in\mathcal C$ 还满足

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge\max\left\{L+\frac{2d}{N^2},\ U_0-256\sqrt d\right\}
\ge L+\Delta_{1/2},
\qquad\Delta_{1/2}=\frac{g^2}{2^{17}N^2}>2^{-36}.
\tag{1.14}
$$

下文证明这些结论；常数的最优性不在声明之内。

## 2. 规范首次 PVM 的全部原索引残差

**引理 2.1（四种支撑与旗标情形）。** 设 $\mathcal B$ 的两个完整首次右支撑为 $E_0=P+S$ 与 $Q$。每个 Kraus 矩阵 $B_\ell$ 保留原标签 $\ell=(\alpha,j,t)$，其中 $\alpha=3,2$ 表示秩三、秩二支。令 $d'=65-F(\mathcal B)$。存在同标签分解

$$
B_\ell=M_\ell+R_\ell,
\qquad r^2=\sum_\ell\|R_\ell\|_{\rm HS}^2\le\frac{d'}8,
\tag{2.1}
$$

使正确旗标索引满足 $\operatorname{Tr}(C_j^\dagger R_\ell)=0$，错误旗标索引满足 $M_\ell=0$。若

$$
z(X)_\ell=\operatorname{Tr}(C_{j_\ell}^\dagger X_\ell),\qquad
q(X)=\sum_\ell|z(X)_\ell|^2,
\tag{2.2}
$$

则

$$
F(\mathcal B)=q(M)+q(R),\qquad q(M)\le65.
\tag{2.3}
$$

证明。此处重述 [E] 引理 4.3、式 (4.6)–(4.9) 的残差，显式保留下一节需要的逐索引正交性。置

$$
Y_3=14P+21S,\qquad Y_2=8Q,\qquad
D_\ell=\operatorname{Tr}(Y_\alpha B_\ell^\dagger B_\ell)-|z(B)_\ell|^2.
\tag{2.4}
$$

逆矩阵只在各自首次支撑内取。对右支撑 $E_\alpha$，加权 Hilbert–Schmidt Cauchy–Schwarz 为

$$
|\operatorname{Tr}(C_j^\dagger B_\ell)|^2
\le\operatorname{Tr}(E_\alpha C_j^2E_\alpha Y_\alpha^{-1})
\operatorname{Tr}(Y_\alpha B_\ell^\dagger B_\ell).
\tag{2.5}
$$

它来自向量 $C_jE_\alpha Y_\alpha^{-1/2}$ 与 $B_\ell Y_\alpha^{1/2}$，权重位于右支撑一侧。四种因子和相应近似为

| 首次支撑 | 原旗标 | (2.5) 的第一因子 | $M_\ell$ |
| --- | --- | --- | --- |
| $P+S$ | $0$ | $1$ | $z(B)_\ell E_0/7$ |
| $P+S$ | $1$ | $3/7$ | $0$ |
| $Q$ | $0$ | $0$ | $0$ |
| $Q$ | $1$ | $1$ | $z(B)_\ell Q/4$ |

例如第一因子为 $2\cdot4/14+9/21=1$，秩三错误旗标只剩 $9/21=3/7$，秩二正确旗标为 $2\cdot4/8=1$。所以 $D_\ell\ge0$；同一完整家族的两支效应给出

$$
\sum_\ell D_\ell=\operatorname{Tr}Y_3+\operatorname{Tr}Y_2-F(\mathcal B)
=49+16-F(\mathcal B)=d'.
\tag{2.6}
$$

在 $(\alpha,j)=(3,0)$ 时，$C_0E_0Y_3^{-1/2}$ 是单位 Hilbert–Schmidt 向量。$B_\ell Y_3^{1/2}$ 在其直线上的正交投影系数为 $z(B)_\ell$，且 $C_0E_0Y_3^{-1}=E_0/7$。取表中的 $M_\ell$ 后，投影残差为 $R_\ell Y_3^{1/2}$，故

$$
D_\ell=\|R_\ell Y_3^{1/2}\|_{\rm HS}^2\ge14\|R_\ell\|_{\rm HS}^2,
\qquad z(R)_\ell=z(B)_\ell-\frac{z(B)_\ell}7\operatorname{Tr}(C_0E_0)=0.
\tag{2.7}
$$

在 $(2,1)$ 时，$C_1QY_2^{-1}=Q/4$ 给出同样的正交投影，因而

$$
D_\ell=\|R_\ell Y_2^{1/2}\|_{\rm HS}^2\ge8\|R_\ell\|_{\rm HS}^2,
\qquad z(R)_\ell=0.
\tag{2.8}
$$

秩三错误旗标 $(3,1)$ 不要求分数为零。其 $M_\ell=0$，$R_\ell=B_\ell$，由因子 $3/7$ 得

$$
D_\ell\ge\frac47\operatorname{Tr}(Y_3B_\ell^\dagger B_\ell)
\ge8\|B_\ell\|_{\rm HS}^2.
\tag{2.9}
$$

秩二错误旗标 $(2,0)$ 因 $QC_0=0$ 而分数为零，但矩阵仍保留，且

$$
M_\ell=0,\qquad D_\ell=8\|B_\ell\|_{\rm HS}^2.
\tag{2.10}
$$

正确旗标上若分数为零，投影系数也为零，(2.7)–(2.8) 仍控制完整残差。四类相加并用 (2.6) 就得到 (2.1)，没有删除零分数矩阵、错误旗标、首次结果或概率质量。

定义

$$
a=\sum_{(3,0)}|z(B)_\ell/7|^2,\qquad
b=\sum_{(2,1)}|z(B)_\ell/4|^2.
\tag{2.11}
$$

同一完整秩三支的所有分数由 (2.5) 界为 $\operatorname{Tr}Y_3=49$，其中正确旗标分数为 $49a$，所以 $0\le a\le1$。秩二支同理给出 $0\le b\le1$。$M$ 所定义的 CP 仪器为

$$
\mathcal B_{\rm app}=(a\operatorname{Ad}_{E_0},\ b\operatorname{Ad}_Q),\qquad
\mathcal B_{\rm app}^\dagger(I)=aE_0+bQ\le I,
\qquad q(M)=49a+16b\le65.
\tag{2.12}
$$

每个正确旗标索引有 $z(R)_\ell=0$，每个错误旗标索引有 $M_\ell=0$。因此 $\overline{z(M)_\ell}z(R)_\ell=0$ 是逐索引等式，不是跨旗标抵消；展开 $q(M+R)$ 即得 (2.3)。$\square$

**引理 2.2（原标签堆叠与端点距离）。** 在引理 2.1 的条件下，

$$
\|\mathcal B-\mathcal A_+\|_\diamond\le4r.
\tag{2.13}
$$

证明。保留原索引作分析堆叠

$$
Vx=\sum_\ell|j_\ell\rangle\otimes B_\ell x\otimes|\ell\rangle,
\qquad
Wx=\sum_\ell|j_\ell\rangle\otimes M_\ell x\otimes|\ell\rangle.
\tag{2.14}
$$

$\ell$ 同时包含首次结果、旗标与细记录，所以对最后一个环境偏迹恰好给原来的经典旗标块，不产生旗标相干。由完整性和 (2.12)，

$$
V^\dagger V=I,\qquad W^\dagger W=aE_0+bQ\le I,\qquad
\|V\|_\infty=1,\quad\|W\|_\infty\le1,\quad
\|V-W\|_\infty\le r.
\tag{2.15}
$$

最后一步由 $\|\sum_\ell R_\ell^\dagger R_\ell\|_\infty\le\sum_\ell\|R_\ell\|_{\rm HS}^2$ 得到。对任意复 $X$，包括张量任意有限参考后，用

$$
VXV^\dagger-WXW^\dagger=(V-W)XV^\dagger+WX(V-W)^\dagger
$$

和 (1.7) 中的偏迹压缩，得到

$$
\|\mathcal B-\mathcal B_{\rm app}\|_\diamond\le2r.
\tag{2.16}
$$

又因 $a,b\le1$，$\mathcal A_+-\mathcal B_{\rm app}$ 是 CP，效应为 $I-W^\dagger W$。于是

$$
\begin{aligned}
\|\mathcal A_+-\mathcal B_{\rm app}\|_\diamond
&=\|I-W^\dagger W\|_\infty\\
&=\|V^\dagger V-W^\dagger W\|_\infty\le2r,
\end{aligned}
\tag{2.17}
$$

其中最后使用 $V^\dagger(V-W)+(V^\dagger-W^\dagger)W$ 的两项展开。三角不等式给出 (2.13)。有限维 CP 后代可按支、按原旗标选有限 Kraus 家族；若使用可数细记录，同样的非负和及平方可和堆叠给出同一界，无需条件归一化。环境、偏迹与次归一化近似都只是分析装置。交换 $P,Q$ 与两个旗标时，证明给出到 $\mathcal A_-$ 的同一界。$\square$

## 3. 残差控制的校正分数比较

**引理 3.1（正性与逐索引消去）。** 保持引理 2.1 的规范 $\mathcal B$、$M,R,r$。令 $U$ 为任意幺正，$u=\|U-I\|_\infty$，$\mathcal T=\mathcal B\circ\operatorname{Ad}_U$，其 Kraus 家族是 $B_\ell U$。则

$$
F(\mathcal T)\le F(\mathcal B)+17(2u+u^2)r^2+68ur.
\tag{3.1}
$$

证明。两个旗标均满足

$$
\|C_j\|_{\rm HS}^2=\operatorname{Tr}(4P_j+9S)=17.
\tag{3.2}
$$

由 Hilbert–Schmidt Cauchy–Schwarz 与 $\|R_\ell(U-I)\|_{\rm HS}\le u\|R_\ell\|_{\rm HS}$，

$$
\|z(R)\|_2\le\sqrt{17}\,r,\qquad
\delta:=z(RU)-z(R),\qquad\|\delta\|_2\le\sqrt{17}\,ur.
\tag{3.3}
$$

所以

$$
q(RU)=\|z(R)+\delta\|_2^2
\le q(R)+17(2u+u^2)r^2.
\tag{3.4}
$$

另一方面，每个非零 $M_\ell$ 是正确旗标上的 $cE_0$ 或 $cQ$。相应 $z(MU)_\ell=c\operatorname{Tr}(DU)$，其中

$$
D=C_0E_0=2P+3S\ge0\quad\text{或}\quad D=C_1Q=2Q\ge0,
$$

迹分别为七、四。对正矩阵谱分解 $D=\sum_i d_i|v_i\rangle\langle v_i|$，

$$
|\operatorname{Tr}(DU)|
\le\sum_i d_i|\langle v_i,Uv_i\rangle|
\le\sum_i d_i=\operatorname{Tr}D.
$$

故在每个非零索引上分数不增加，得到

$$
q(MU)\le q(M)\le65.
\tag{3.5}
$$

关键是对于每一个原索引及任意 $U$，均有精确等式

$$
\overline{z(MU)_\ell}\,z(R)_\ell=0.
\tag{3.6}
$$

正确旗标上是 $z(R)_\ell=0$；错误旗标上是 $M_\ell U=0$。这里没有声称 $z(RU)_\ell=0$，也没有声称任意通道在校正下具有一阶分数驻定性。由 (3.6)，混合项只能来自 $\delta$，于是

$$
\begin{aligned}
F(\mathcal T)
&=q(MU)+q(RU)+2\operatorname{Re}\langle z(MU),z(RU)\rangle\\
&=q(MU)+q(RU)+2\operatorname{Re}\langle z(MU),\delta\rangle\\
&\le q(M)+q(R)+17(2u+u^2)r^2+2\sqrt{65}\sqrt{17}\,ur.
\end{aligned}
$$

因为 $1105<34^2$，有 $2\sqrt{65\cdot17}\le68$；再用 (2.3) 即得 (3.1)。这将分数漂移控制为真实残差的函数，没有用裸分数 Lipschitz 界引入与残差无关的一阶损失。$\square$

## 4. 小亏损吸收与相同权重的凸化

**定理 4.1（单个分量的端点平方根界）。** 对每个 $\mathcal T\in\mathcal K$，存在 $\mathcal A_{\rm end}\in\{\mathcal A_+,\mathcal A_-\}$，使

$$
\|\mathcal T-\mathcal A_{\rm end}\|_\diamond\le256\sqrt d,
\qquad d=65-F(\mathcal T).
\tag{4.1}
$$

证明。先取 $0\le d<1/3072$。由继承的 $1/6$ 分拆间隙，首次 PVM 必为秩 $3+2$。用 (1.10)–(1.12) 对同一个通道校正，得到

$$
\mathcal B=\mathcal T\circ\operatorname{Ad}_{U^\dagger},\qquad
\mathcal T=\mathcal B\circ\operatorname{Ad}_U,\qquad
u\le\sqrt{12d}<\frac1{16}.
\tag{4.2}
$$

若 $E_0=Q+S$，同时交换 $P,Q$ 和旗标零、一。该对称由交换 $e_0,e_1$ 及 $e_3,e_4$、固定 $s$ 的全空间幺正 $R_{\rm sw}$ 实现：变换

$$
(\mathscr R\mathcal T)_j(X)
=R_{\rm sw}\mathcal T_{1-j}(R_{\rm sw}XR_{\rm sw})R_{\rm sw}
$$

保持 $F$、菱形距离及目标，并交换两个端点。因而可在规范右支撑 $P+S,Q$ 下证明，再反向转回原端点。

对同一校正家族施用引理 2.1 与引理 3.1，记 $d'=65-F(\mathcal B)$ 及 $k=17(2u+u^2)$。由 $u<1/16$，

$$
k\le\frac{561}{256}<3,
\qquad d'\ge8r^2,
\qquad d\ge d'-kr^2-68ur\ge5r^2-68ur.
\tag{4.3}
$$

所以 $r^2\le d/5+(68u/5)r$。对非负 $x,A,B$，若 $x^2\le A+Bx$，则正根界与 $\sqrt{B^2+4A}\le B+2\sqrt A$ 给出

$$
x\le\frac{B+\sqrt{B^2+4A}}2\le B+\sqrt A.
$$

代入 $x=r$、$A=d/5$、$B=68u/5$，得到

$$
r\le\sqrt{d/5}+\frac{68}{5}u\le\sqrt d+14u.
\tag{4.4}
$$

由同一个 $\mathcal B$ 的端点界及校正距离界，

$$
\begin{aligned}
\|\mathcal T-\mathcal A_{\rm end}\|_\diamond
&\le2u+4r\le4\sqrt d+58u\\
&\le236\sqrt d\le256\sqrt d,
\end{aligned}
\tag{4.5}
$$

其中 $\sqrt{12}<4$。全过程没有除以 $d,r,u$ 或分支概率。特别地，$d=0$ 时 $u=0$，(4.3) 强制 $r=0$，完整性进一步给出 $a=b=1$，故通道恰为对应端点；零分数和错误旗标矩阵仍包含在这一推导中。

若 $d\ge1/3072$，任选端点，由两通道距离至多二，

$$
\|\mathcal T-\mathcal A_{\rm end}\|_\diamond\le2\le256\sqrt d.
\tag{4.6}
$$

最后一步在阈值处平方等价于 $4\cdot3072<256^2$。该支包括阈值相等、所有其他秩分拆、确定旗标幺正和全部较大亏损；小亏损支已包含零亏损。因此所有边界均已覆盖。$\square$

**定理 4.2（整个紧凸松弛上的平方根稳定性）。** 对每个 $\mathcal T\in\mathcal C$，存在单个 $\lambda\in[0,1]$，使

$$
\|\mathcal T-\mathcal A_\lambda\|_\diamond\le256\sqrt d.
\tag{4.7}
$$

证明。取任意有限凸表示 $\mathcal T=\sum_i w_i\mathcal T_i$，其中 $\mathcal T_i\in\mathcal K$、$w_i\ge0$、$\sum_iw_i=1$。对每个分量选择定理 4.1 的端点 $\mathcal A_i$，以原来的同一组权重置

$$
\mathcal A=\sum_iw_i\mathcal A_i\in\mathcal M,
\qquad \lambda=\sum_{i:\,\mathcal A_i=\mathcal A_+}w_i.
$$

这是一枚输入独立硬币的一个固定面参数，未按亏损重新配权。线性性给出 $d=\sum_iw_id_i$，故三角不等式与平方根的凹性给出正确方向

$$
\|\mathcal T-\mathcal A\|_\diamond
\le256\sum_iw_i\sqrt{d_i}
\le256\sqrt{\sum_iw_id_i}=256\sqrt d.
\tag{4.8}
$$

[E] 命题 2.5 的 $\mathcal C=\operatorname{conv}(\mathcal K)$ 保证每个 $\mathcal T\in\mathcal C$ 都有这种有限表示。若从闭凸包定义出发，取有限凸组合 $\mathcal T_n\to\mathcal T$，在紧线段 $\mathcal M$ 中为比较点取收敛子列；$F$ 与范数连续，使同一个常数二百五十六传到极限。紧性只用于传递已证明的有效不等式。

当 $d=0$ 时，界使 $\mathcal T$ 位于整个面；这与继承的完整面 (1.6) 一致。单个 $\mathcal K$ 分量的零亏损比较是端点，凸化后的比较则可为内部点。$\square$

## 5. 合法相位族、整个面的下界与最优幂指数

**定义 5.1（固定完整 PVM 的相位族）。** 对实数 $0\le\eta\le1$，置

$$
\zeta_\eta=\frac{1+i\eta}{1-i\eta}
=\frac{1-\eta^2+2i\eta}{1+\eta^2},\qquad
V_\eta=P+Q+\zeta_\eta S,
\qquad
\mathcal T_\eta=(\operatorname{Ad}_{P+\zeta_\eta S},\operatorname{Ad}_Q).
\tag{5.1}
$$

分母非零，分子、分母模相等，所以 $|\zeta_\eta|=1$，$V_\eta$ 是全五维幺正。实际实现为先做完整固定 PVM $\{P+S,Q\}$，两结果都保留，再施加 $V_\eta$，按首次结果报告旗标。因为 $V_\eta Q=Q$，该实现恰为 (5.1)，其两个 Kraus 效应分别是 $P+S,Q$。因此 $\mathcal T_\eta$ 是确定的有限深度实际协议，也是单个 $\mathcal K$ 分量，并属于 $\mathcal C$ 与三个实际类。没有使用任意 CP 后处理或新增系统。

**命题 5.2（精确亏损与整个面的双侧估计）。** 该族满足

$$
d_\eta=65-F(\mathcal T_\eta)=\frac{48\eta^2}{1+\eta^2},
\qquad
\sqrt{\frac{d_\eta}{24}}
\le\operatorname{dist}_\diamond(\mathcal T_\eta,\mathcal M)
\le\sqrt{\frac{d_\eta}{3}}.
\tag{5.2}
$$

证明。原未缩放见证的两个迹为 $4+3\zeta_\eta$ 与四，故

$$
F(\mathcal T_\eta)=|4+3\zeta_\eta|^2+16
=41+24\operatorname{Re}\zeta_\eta.
$$

于是 $d_\eta=24(1-\operatorname{Re}\zeta_\eta)=48\eta^2/(1+\eta^2)$。这是精确恒等式；$\eta>0$ 时亏损正，且随 $\eta\downarrow0$ 趋于零。

取复非对角测试 $X=|e_0\rangle\langle s|$，其迹范数为一，在 (1.2) 中合法。对每一个 $\lambda\in[0,1]$，直接作用为

$$
\mathcal T_\eta(X)=(\overline{\zeta_\eta}X,0),\qquad
\mathcal A_\lambda(X)=(\lambda X,0).
$$

因此

$$
\|\mathcal T_\eta-\mathcal A_\lambda\|_\diamond
\ge|\overline{\zeta_\eta}-\lambda|
\ge|\operatorname{Im}\zeta_\eta|
=\frac{2\eta}{1+\eta^2}.
\tag{5.3}
$$

该下界对整个线段的每个参数同时成立，所以取下确界仍成立。其平方为

$$
\frac{4\eta^2}{(1+\eta^2)^2}
=\frac{d_\eta}{12(1+\eta^2)}\ge\frac{d_\eta}{24},
$$

得到 (5.2) 的下界。

上界另由端点 $\mathcal A_+$ 给出。将 $\mathcal T_\eta$ 与 $\mathcal A_+$ 的两个原旗标 Kraus 矩阵堆叠为等距映射，它们之差只在第一支的 $S$ 分量为 $(\zeta_\eta-1)S$，算子范数是 $|\zeta_\eta-1|$。对全部复参考测试应用两项展开，得

$$
\operatorname{dist}_\diamond(\mathcal T_\eta,\mathcal M)
\le\|\mathcal T_\eta-\mathcal A_+\|_\diamond
\le2|\zeta_\eta-1|
=\frac{4\eta}{\sqrt{1+\eta^2}}=\sqrt{d_\eta/3}.
\tag{5.4}
$$

这是到端点的上界；阻止靠近整个面的则是独立的、对所有 $\lambda$ 统一成立的 (5.3)。$\eta=0$ 时通道等于 $\mathcal A_+$，两侧均为零。$\square$

**定理 5.3（最优统一局部幂指数）。** 在 $\mathcal C,\mathcal K,\mathfrak S_{\rm fin},\mathfrak S_{\rm as},\mathfrak S_{\rm cl}$ 的每一个类上，对距离 $\operatorname{dist}_\diamond(\mathcal T,\mathcal M)$，最佳统一局部幂指数是 $1/2$。

证明。指数 $\beta$ 的统一局部界是存在有限常数 $C_0$ 及 $\varepsilon_0>0$，使该类所有 $0\le d\le\varepsilon_0$ 的通道均满足 $\operatorname{dist}_\diamond(\mathcal T,\mathcal M)\le C_0d^\beta$。定理 4.2 及实际类对 $\mathcal C$ 的继承包含给出 $\beta=1/2$；对 $\mathcal K$ 还有更强的端点比较。

若 $\beta>1/2$，同一条合法路径 $\mathcal T_\eta$ 位于全部上述类中。对充分小的正 $\eta$，(5.2) 将迫使

$$
C_0\ge\frac1{\sqrt{24}}d_\eta^{1/2-\beta}.
$$

右侧在 $d_\eta\downarrow0$ 时无界，与 $C_0$ 有限矛盾。因此更大的指数在每个类上都失败。固定非 $3+2$ 秩分拆有正亏损间隙，不能趋近此面；没有对这些局部空域声称非平凡尖锐性。这个证明不识别最佳平方根常数。$\square$

**命题 5.4（每个固定面点的局部障碍）。** 对任意固定 $\lambda_0\in[0,1]$，在 $\mathcal C$ 及三个实际类中，任何 $\beta>1/2$ 的局部界即使允许常数依赖 $\lambda_0$，也在趋向 $\mathcal A_{\lambda_0}$ 的协议上失败。

证明。先令 $0<\lambda_0\le1$，使用同一固定输入独立硬币

$$
\mathcal T_\eta^{(\lambda_0)}
=\lambda_0\mathcal T_\eta+(1-\lambda_0)\mathcal A_-.
\tag{5.5}
$$

这是统一有限深度实际协议，且由线性性

$$
D_\eta:=65-F(\mathcal T_\eta^{(\lambda_0)})=\lambda_0d_\eta,
\qquad
\|\mathcal T_\eta^{(\lambda_0)}-\mathcal A_{\lambda_0}\|_\diamond
\le\lambda_0\sqrt{d_\eta/3}\longrightarrow0.
\tag{5.6}
$$

对任意比较点 $\mathcal A_\lambda$，同一个 $X=|e_0\rangle\langle s|$ 的第一旗标系数差为 $\lambda_0\overline{\zeta_\eta}-\lambda$，所以

$$
\begin{aligned}
\operatorname{dist}_\diamond(\mathcal T_\eta^{(\lambda_0)},\mathcal M)
&\ge\lambda_0|\operatorname{Im}\zeta_\eta|\\
&\ge\lambda_0\sqrt{d_\eta/24}
=\sqrt{\lambda_0/24}\sqrt{D_\eta}.
\end{aligned}
\tag{5.7}
$$

对固定正 $\lambda_0$，该虚部在 $\eta>0$ 时非零，且系数为固定正数，故排除每个更大指数。

当 $\lambda_0=0$ 时，采用反射族

$$
\mathcal T_\eta^-=(\operatorname{Ad}_P,\operatorname{Ad}_{Q+\zeta_\eta S}).
\tag{5.8}
$$

它由完整 PVM $\{P,Q+S\}$ 和同一全寄存器幺正 $V_\eta$ 实现，亏损仍为 $d_\eta$，趋近 $\mathcal A_-$。测试 $X=|e_1\rangle\langle s|$ 在旗标一给出系数 $\overline{\zeta_\eta}-(1-\lambda)$，从而得到同样的统一虚部下界及反射端点上界。这样覆盖剩余端点，且未除以 $\lambda_0$。

内部面点的 (5.5) 是实际硬币混合，属于 $\mathcal C$ 和实际类，不把它宣称为单个 $\mathcal K$ 分量。$\mathcal K$ 上的统一指数障碍已由未混合的端点路径证明。$\square$

## 6. 同一个通道的两证书与显式间隙

**引理 6.1（继承的整个面相干接口）。** 按 [E] 引理 6.2，令

$$
\psi_\star=\frac{e_0+e_1}{2}+\frac{s}{\sqrt2},\qquad
h(\mathcal T)=\|(\widehat{\mathcal J}-\mathcal T)(|\psi_\star\rangle\langle\psi_\star|)\|_1.
\tag{6.1}
$$

则

$$
\begin{gathered}
h(\mathcal T)\le\|\widehat{\mathcal J}-\mathcal T\|_\diamond,\qquad
|h(\mathcal T)-h(\mathcal T')|\le\|\mathcal T-\mathcal T'\|_\diamond,\\
h(\mathcal A_\lambda)\ge U_0\quad(0\le\lambda\le1),\qquad
\min_{\mathcal A\in\mathcal M}\|\widehat{\mathcal J}-\mathcal A\|_\diamond
=\|\widehat{\mathcal J}-\mathcal A_{1/2}\|_\diamond=U_0.
\end{gathered}
\tag{6.2}
$$

这些是整个面的条件，不能用端点的单独误差替代。特别地，[E] 命题 6.1 给出

$$
\mathcal A_\lambda(S)=(\lambda S,(1-\lambda)S),\qquad
\|(\widehat{\mathcal J}-\mathcal A_\lambda)(S)\|_1=2|\lambda-1/2|.
\tag{6.3}
$$

合法公平中点同时有 $F=65$ 和零 $S$ 测试误差，所以支撑加 $S$ 测试的最大值在实际类上的最小值仍为 $L$。所需的附加关系是 (6.1) 的相干输入，而不是丢掉内部面点。

**定理 6.2（平方根稳定性给出的同通道下界）。** 每个 $\mathcal T\in\mathcal C$ 以其自身 $d=65-F(\mathcal T)$ 满足 (1.14)。

证明。固定一个 $\mathcal T$。由 (1.9)，

$$
b(\mathcal T)=2\left[1-\frac{65-d}{N^2}\right]=L+\frac{2d}{N^2}.
\tag{6.4}
$$

定理 4.2 给这同一个通道选择某个 $\mathcal A_\lambda$。用相同的 $h$ 及 (6.2)，

$$
h(\mathcal T)\ge h(\mathcal A_\lambda)-\|\mathcal T-\mathcal A_\lambda\|_\diamond
\ge U_0-256\sqrt d.
\tag{6.5}
$$

两个输入测试可以不同，但都界住这个 $\mathcal T$ 的同一个完整菱形误差，所以

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge\max\left\{L+\frac{2d}{N^2},U_0-256\sqrt d\right\}.
\tag{6.6}
$$

这没有组合分别可达却未必相容的优化值。

为作显式阈值分拆，先验证所用常数。由 $\kappa=\sqrt2$ 及 (1.5)，

$$
g=\frac{(\kappa-1)(41-24\kappa)}{\kappa N^2}.
\tag{6.7}
$$

平方比较 $2>49/25$、$2<9/4$ 给出 $7/5<\kappa<3/2$。所以

$$
\kappa-1>2/5,\quad 41-24\kappa>5,\quad
N^2<77,\quad\kappa N^2<231/2,
\qquad g>4/231>1/64.
\tag{6.8}
$$

最后一个有理比较为 $256>231$；又 $L>0$，故 $0<g<U_0<1$。置

$$
d_0=\left(\frac g{512}\right)^2,\qquad
\Delta_{1/2}=\frac{g^2}{2^{17}N^2}.
\tag{6.9}
$$

若 $d\ge d_0$，支撑项给出

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge L+\frac{2d_0}{N^2}=L+\Delta_{1/2}.
\tag{6.10}
$$

若 $d\le d_0$，相干项给出

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge U_0-256\frac g{512}=L+\frac g2\ge L+\Delta_{1/2},
\tag{6.11}
$$

因为 $\Delta_{1/2}/g=g/(2^{17}N^2)<1/2$。两支均包含阈值相等；$d=0$ 直接属于相干支。最后，由 (6.8)，

$$
\Delta_{1/2}>\frac1{77\cdot2^{29}}>2^{-36},
\tag{6.12}
$$

后式使用 $77<128$。这证明显式正间隙，无需求解精确极小化问题。$\square$

**命题 6.3（改进的量与未识别的量）。** [E] 定理 6.3 的显式增量为

$$
\Delta_{\rm old}=\frac{g^4}{2^{27}N^2}.
$$

两个保证值之比精确为

$$
\frac{\Delta_{1/2}}{\Delta_{\rm old}}=\frac{2^{10}}{g^2}>2^{10}.
\tag{6.13}
$$

这是显式下界保证的严格增强。为了区分不同对象，定义标量包络极小值、精确联合证书增量与松弛完整距离为

$$
\begin{gathered}
E_{\rm sc}=\min_{0\le x\le65}
\max\left\{L+\frac{2x}{N^2},U_0-256\sqrt x\right\},\\
\delta_{\rm joint}=\min_{\mathcal T\in\mathcal C}\max\{b(\mathcal T),h(\mathcal T)\}-L,\qquad
D_{\mathcal C}=\min_{\mathcal T\in\mathcal C}\|\widehat{\mathcal J}-\mathcal T\|_\diamond.
\end{gathered}
\tag{6.14}
$$

紧性与连续性保证这些最小值存在，且

$$
L+\Delta_{1/2}\le E_{\rm sc}\le L+\delta_{\rm joint}\le D_{\mathcal C}.
\tag{6.15}
$$

证明。(6.13) 由两个表达式相除及 $0<g<1$ 得出。对每个 $x\in[0,65]$，定理 6.2 中的同一阈值分拆适用于标量表达式，故给出 (6.15) 第一式。对每个 $\mathcal T\in\mathcal C$，(6.4)–(6.5) 说明该通道的联合证书至少为在 $x=d(\mathcal T)$ 的标量表达式，因而至少为 $E_{\rm sc}$。分别取最小值给出第二式。两个证书均不超过同一完整距离，再取最小值得第三式。$\square$

$\Delta_{1/2}$ 是阈值证明的显式保证；$U_0-256\sqrt d$ 是 $h(\mathcal T)$ 的下界，不能当作其公式。本文没有把 (6.15) 中任意两项设为相等，也没有识别 $\delta_{\rm joint}$、$D_{\mathcal C}$ 或其极小者。证书的最大值、标量包络和完整通道距离分别承担不同义务。

## 7. 角度、停止类型与原全局问题

**约定 7.1（继承的全角度坐标接口）。** 为明确原问题的量词，重述 [E] 定义 7.1 与引理 7.2 的符号。令

$$
\begin{gathered}
u_+=(e_0+e_3)/\sqrt2,\quad u_-=(e_0-e_3)/\sqrt2,\quad
v_+=(e_1+e_4)/\sqrt2,\quad v_-=(e_1-e_4)/\sqrt2,\\
K_0=|u_+\rangle\langle e_0|+\frac1{\sqrt2}|v_+\rangle\langle s|+|s\rangle\langle e_4|,\\
K_1=|u_+\rangle\langle e_1|+\frac1{\sqrt2}|v_+\rangle\langle s|+|s\rangle\langle e_3|,\\
A_0(\theta)=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1(\theta)=i\sin\theta K_0+\cos\theta K_1,\\
\mathcal J_\theta(X)=\bigoplus_jA_j(\theta)XA_j(\theta)^\dagger,\\
T_0=[u_+\ \ u_-\ \ v_+\ \ v_-\ \ s],\qquad
T_1=[u_-\ \ u_+\ \ v_+\ \ s\ \ v_-],\qquad
D_\theta=\cos\theta I+i\sin\theta R_{\rm sw}.
\end{gathered}
\tag{7.1}
$$

这里 $R_{\rm sw}$ 是定理 4.1 的交换幺正。$T_j$ 是全寄存器幺正；$\mathsf W=\bigoplus_jT_j$ 只表示按经典旗标控制的输出幺正。对每个实数 $\theta$，继承接口为

$$
\mathcal J_\theta=\operatorname{Ad}_{\mathsf W}\circ\widehat{\mathcal J}\circ\operatorname{Ad}_{D_\theta}.
\tag{7.2}
$$

这些输入、输出变换及其逆都在实际菜单内，保持三个类、停止类型及全部参考上的不折半菱形距离。给定原坐标通道 $\mathcal T$，规范代表是

$$
\widetilde{\mathcal T}
=\operatorname{Ad}_{\mathsf W^\dagger}\circ\mathcal T\circ\operatorname{Ad}_{D_\theta^\dagger}.
\tag{7.3}
$$

两个证书同时转移到这一代表：支撑输入为 $(D_\theta^\dagger\otimes I)\psi_\rho$，输出投影为 $(\mathsf W\otimes I)\Pi(\mathsf W^\dagger\otimes I)$，相干输入为 $D_\theta^\dagger\psi_\star$。因此所有角度使用的是同一通道的两读数；$\mathsf W$ 不授予相干旗标资源。

**约定 7.2（继承的有限截断与闭包接口）。** [E] 引理 7.3 给出

$$
\mathfrak S_{\rm fin}\subseteq\mathfrak S_{\rm as}\subseteq\mathfrak S_{\rm cl}\subseteq\mathcal C,
\qquad
\overline{\mathfrak S_{\rm as}}^{\diamond}=\mathfrak S_{\rm cl}.
\tag{7.4}
$$

其截断接口使用深度 $n$ 尚未停止路径的平均效应 $R_n$：$0\le R_n\le I$，忠实输入 $I_5/5$ 上的几乎必然终止给出 $\operatorname{Tr}R_n\to0$。原残余续行与立即停止、保留当前寄存器并赋固定旗标的替代残余，都有完整效应 $R_n$，故有限深度替代 $\mathcal T_n$ 满足

$$
\|\mathcal T-\mathcal T_n\|_\diamond
\le2\|R_n\|_\infty\le2\operatorname{Tr}R_n\longrightarrow0.
\tag{7.5}
$$

平均效应处理异常经典带，不另要求有限期望时长或所有条件分支的统一停止。由连续性，三个实际类到固定目标的下确界相同；(7.2) 又使它与实角度无关，记为

$$
d_\star=\inf_{\mathcal T\in\mathfrak S_{\rm fin}}\|\mathcal J_\theta-\mathcal T\|_\diamond
=\inf_{\mathcal T\in\mathfrak S_{\rm as}}\|\mathcal J_\theta-\mathcal T\|_\diamond
=\min_{\mathcal T\in\mathfrak S_{\rm cl}}\|\mathcal J_\theta-\mathcal T\|_\diamond.
\tag{7.6}
$$

最后的抽象闭包极小者来自归一化经典旗标通道 Choi 集的有限维紧性，正如 [E] 推论 7.4。它不识别该通道，不证明 $\mathfrak S_{\rm as}=\mathfrak S_{\rm cl}$，也不给有限或几乎必然停止实现。

**推论 7.3（原问题的增强下界与保留的条件上界）。** 对三个实际类中的每个协议和每个实数 $\theta$，定理 6.2 的下界对其规范代表成立。因此

$$
L+\Delta_{1/2}\le D_{\mathcal C}\le d_\star.
\tag{7.7}
$$

条件性保留 [E] 推论 7.4 与 §8 引用的实际倾斜 PVM 接口后，还有

$$
L+\Delta_{1/2}\le d_\star<U_0-\frac1{1000000}.
\tag{7.8}
$$

证明。$\mathcal C$ 上逐点成立的下界限制到实际子类，再用等距坐标和共同下确界，得到 (7.7)，方向由实际类包含于外部松弛决定。(7.8) 的右端独立复用 [E] 推论 7.4 引用的倾斜族参数 $\tau=1/10000$ 的有限深度上界。该引用指向另一卷的定义 4.1、4.3、命题 4.2、定理 6.2 与定理 7.1；那套倾斜构造的完整证明并未在此提供，故上界明确以该接口为条件，不虚构其上游推导或认证其链接。新的平方根定理、实际相位障碍和 (7.7) 的下界均不依赖该倾斜上界。$\square$

## 8. 来源对应、应用含义与未决边界

**约定 8.1（声明的来源与新增部分）。** 本文定义 1.1–1.4 的模型、菜单、范数、端点、分数与外部松弛对应 [E] 定义 1.1–1.2、定义 2.2、命题 2.3、定义 2.4、命题 2.5。精确支撑与完整面对应 [E] 命题 3.2、定理 5.1；分拆间隙和方向、主角接口对应 [E] 命题 3.2、引理 4.1–4.2。本文引理 2.1–2.2 重述并展开 [E] 引理 4.3、式 (4.6)–(4.9) 的规范残差与堆叠界，使新比较所需的原索引正交性可直接检查。

新的实质推导是引理 3.1、定理 4.1–4.2 的残差比较与吸收，命题 5.2、定理 5.3、命题 5.4 的合法整个面和逐面点幂指数障碍，以及定理 6.2、命题 6.3 的增强联合下界。相干接口、合法中点限制及旧显式增量分别继承 [E] 引理 6.2、命题 6.1、定理 6.3。角度、停止、闭包与保留上界分别使用 [E] 定义 7.1、引理 7.2–7.3、推论 7.4、§8。旧四次根定理仍是有效上界；这里给出更强的近极大幂次及其障碍，没有改变支撑最大值或改判其面。

**命题 8.2（整操作控制的含义）。** 若已知 $\mathcal T\in\mathcal C$ 且 $F(\mathcal T)\ge65-\varepsilon$，其中 $\varepsilon\ge0$，则存在一个固定、输入独立的 $\lambda$，使

$$
\|\mathcal T-\mathcal A_\lambda\|_\diamond\le256\sqrt\varepsilon.
\tag{8.1}
$$

因此任意有限参考及任意复输入 $X$ 的完整保留输出误差至多 $256\sqrt\varepsilon\,\|X\|_1$。这是定理 4.2 与范数定义的直接含义。单个 $\mathcal K$ 分量可用端点比较；混合则使用整个面。单一分数不能识别 $\lambda$，因为整个面分数都等于六十五；(8.1) 也不认证接近 $\widehat{\mathcal J}$，因为面自身到目标的最小完整误差为 $U_0$。

对机器学习的含义限于一条方法论：近饱和标量分数只有结合已证明的模型类、完整目标面和定量稳定性桥梁，才能控制整个响应。本文没有证明任何具体机器学习任务、表示或允许操作的对应桥梁，不给出经验性能或普遍机器学习定理。

**定义 8.3（保持 OPEN 的目标）。** 已确定的是这些固定类中的最佳局部幂指数 $1/2$；最佳平方根常数、常数二百五十六的最优替代、尖锐显式间隙、最佳阈值、精确 $\delta_{\rm joint}$ 与极小者、$D_{\mathcal C}$、原始精确 $d_\star$、最优反馈或首次 PVM、倾斜族最优参数及其全局最优性、实际闭包的完整刻画、有限深度或几乎必然终止的全局取到均为 OPEN。外部松弛可行性不反推实际协议；抽象闭包极小者不等于停止协议。这里的幂指数结论没有结算原完整全局优化目标。

所有首次结果、原旗标与概率质量在论证中均保留。CP 松弛、Kraus 环境、次归一化近似、主角校正以及范数证明中的参考与偏迹均为分析工具，不扩张实际菜单。本文不提供有限精度、校准、控制取得、物理可实现性或总成本保证。

## 追加锚（本行以下为增补区）
