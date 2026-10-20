# AURIC FIB 近支撑极大的显式四次根稳定性与同一通道的有效距离间隙

本文在全复输入 $M_5$、保留二值经典旗标和原五维量子输出、允许任意未读取有限参考且采用不折半菱形范数的原问题中，给出两个相连的定量结论。若首次完整 PVM 外部松弛中的通道 $\mathcal T$ 距精确支撑最大值的未缩放亏损为 $d=65-F(\mathcal T)$，则它到整个极大面 $\mathcal M$ 的菱形距离至多 $64d^{1/4}$；同一个通道同时满足支撑与相干证书，因而原问题的共同下确界有显式下界

$$
L+\Delta\le d_\star,
\qquad
\Delta=\frac{(U_0-L)^4}{2^{27}N^2}>2^{-58}>0.
$$

其中 $N=3+4\sqrt2$、$L=48(\sqrt2-1)/N^2$、$U_0=1-1/\sqrt2$。既有的实际倾斜 PVM 上界仍给出 $d_\star<U_0-10^{-6}$。新增内容是相对于既有支撑面与倾斜上界卷的有效稳定模量与显式联合间隙；精确支撑值、整个极大面、定性严格间隙及倾斜构造均予以归属。本文是条件性的 **UNEXECUTED 符号数学**，未作 Lean/kernel 验证；精确全局距离与实际最优协议的取到仍为 OPEN。

## 1. 全输入问题与定量结论

**定义 1.1（对象、菜单与范数）。** 取 $H=\mathbb C^5$，固定正交基 $(e_0,e_1,e_2,e_3,e_4)$，内积对第一变量共轭线性。置

$$
\begin{gathered}
s=e_2,\qquad S=|s\rangle\langle s|,\qquad
P=|e_0\rangle\langle e_0|+|e_4\rangle\langle e_4|,\qquad
Q=|e_1\rangle\langle e_1|+|e_3\rangle\langle e_3|,\\
P_0=P,\quad P_1=Q,\quad P+Q+S=I_5,\qquad
r=\sqrt2,\quad q=1/\sqrt2,\quad H_j=P_j+qS,\quad C_j=2P_j+3S.
\end{gathered}
\tag{1.1}
$$

规范目标为复线性带旗标仪器

$$
\widehat{\mathcal J}(X)=\bigoplus_{j=0}^1H_jXH_j,
\qquad X\in M_5.
\tag{1.2}
$$

因为 $H_0^2+H_1^2=P+Q+S=I_5$，目标是归一化通道。直和中的旗标是经典输出；量子输出仍为同一个 $H$。实际模拟器只允许 $H$ 上的幺正、完整 Lüders PVM、可测的输入独立经典随机性、自适应经典反馈及末端记录到二值旗标的粗化，保留全部结果与概率质量。不允许新增量子寄存器或能级、重置、非投影测量原语、任意 CPTP 后处理原语、读取参考或成功后选择。记 $\operatorname{Ad}_B(X)=BXB^\dagger$。菱形范数为

$$
\|\Lambda\|_\diamond=
\sup_{k\ge1}\sup_{0\ne X\in M_5\otimes M_k}
\frac{\|(\Lambda\otimes\operatorname{id}_{M_k})(X)\|_1}{\|X\|_1},
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}.
\tag{1.3}
$$

内层包括任意复算符，参考始终不被读取。$\mathfrak S_{\rm fin}$ 为有统一有限操作深度上界的实际协议，$\mathfrak S_{\rm as}$ 为对每个输入几乎必然有限终止的实际协议，$\mathfrak S_{\rm cl}=\overline{\mathfrak S_{\rm fin}}^{\diamond}$。独立随机选择可预采样为整条经典带，包括所有可能有限反馈历史的选择；固定带以后只剩确定的量子结果树。原始角度仪器 $\mathcal J_\theta$ 在定义 7.1 给出，并由合法幺正与 (1.2) 等距对应。

原问题的角度依赖下确界先定义为

$$
d_\star(\theta)=\inf_{\mathcal T\in\mathfrak S_{\rm fin}}\|\mathcal J_\theta-\mathcal T\|_\diamond.
$$

**定义 1.2（常数与两个实际端点）。** 置

$$
\begin{gathered}
N=3+4r,\qquad N^2=41+24r,\qquad
L=\frac{48(r-1)}{N^2}=2\left(1-\frac{65}{N^2}\right),\qquad U_0=1-q,\\
g=U_0-L=\frac{(r-1)(41-24r)}{rN^2},\qquad
\Delta=\frac{g^4}{2^{27}N^2}.
\end{gathered}
\tag{1.4}
$$

定义仪器的两个旗标操作为

$$
\begin{array}{ll}
\mathcal A_{+,0}=\operatorname{Ad}_{P+S},&\mathcal A_{+,1}=\operatorname{Ad}_Q,\\
\mathcal A_{-,0}=\operatorname{Ad}_P,&\mathcal A_{-,1}=\operatorname{Ad}_{Q+S},
\end{array}
\qquad
\mathcal A_t=t\mathcal A_++(1-t)\mathcal A_-,\quad
\mathcal M=\{\mathcal A_t:0\le t\le1\}.
\tag{1.5}
$$

端点分别是完整 PVM $\{P+S,Q\}$ 与 $\{P,Q+S\}$，按所列顺序报告旗标；输入独立硬币以同一权 $t$ 混合它们。因此整段均为实际有限深度协议。

**定理 1.3（显式稳定性及有效联合间隙）。** 令 $F$ 为定义 2.2 的未缩放线性分数，$\mathcal C$ 为定义 2.4 的紧首次 PVM 外部松弛。对每个 $\mathcal T\in\mathcal C$，记 $d=65-F(\mathcal T)\ge0$，则

$$
\operatorname{dist}_\diamond(\mathcal T,\mathcal M)
\le64d^{1/4},
\tag{1.6}
$$

而同一通道满足

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge\max\left\{L+\frac{2d}{N^2},\ U_0-64d^{1/4}\right\}
\ge L+\Delta,
\qquad \Delta>2^{-58}.
\tag{1.7}
$$

对每个实数 $\theta$ 以及 $\mathfrak S_{\rm fin}$、$\mathfrak S_{\rm as}$、$\mathfrak S_{\rm cl}$ 中的每个实际模拟器，有相同的下界 $L+\Delta$。三个类到 $\mathcal J_\theta$ 的下确界相同且与角度无关，记为 $d_\star$，并且

$$
L+\Delta\le d_\star<U_0-\frac1{1000000}.
\tag{1.8}
$$

右侧严格上界复用既有卷定理 7.1 的实际构造；不是本文重新优化得到的结论。以下逐步证明 (1.6)–(1.7) 并补全转移接口。精确 $d_\star$、匹配的全局最优策略及有限深度或几乎必然终止的全局取到均不由本定理结算。

## 2. 归一化见证与首次 PVM 松弛

**引理 2.1（CP 菱形范数与复参考测试）。** 有限维 CP 映射 $\Psi$ 的效应 $R=\Psi^\dagger(I)$ 满足

$$
\|\Psi\|_\diamond=\|R\|_\infty.
\tag{2.1}
$$

因此归一化 CP 通道的菱形范数为一，两个通道的菱形距离至多二。所有这些结论均采用 (1.3) 的任意复算符与任意有限参考。

证明。堆叠 Kraus 算符为 $V$，则 $V^\dagger V=R$，$\Psi(X)=\operatorname{Tr}_E(VXV^\dagger)$。迹范数对偶性给出，对任意复算符 $Y$，

$$
\|\operatorname{Tr}_E Y\|_1
=\sup_{\|Z\|_\infty\le1}|\operatorname{Tr}[(Z^\dagger\otimes I_E)Y]|
\le\|Y\|_1,
$$

因为 $\|Z\otimes I_E\|_\infty=\|Z\|_\infty$。在任意参考上使用同一不等式与两侧乘法界，得上界 $\|V\|_\infty^2=\|R\|_\infty$。以 $R$ 最大特征值的单位特征向量作正纯态输入，输出为正且迹为该特征值，得到反向不等式。归一化时 $R=I$；再用三角不等式即得距离至多二。这里的 Kraus 环境仅为分析工具，不是模拟器可用资源。$\square$

**定义 2.2（规范化见证与未缩放分数）。** 取

$$
\rho=\frac{r(P+Q)+3S}{N},\qquad
\psi_\rho=\sum_{k=0}^4\sqrt{\rho_{kk}}\,e_k\otimes e_k,
\qquad |B\rangle\!\rangle=\sum_kBe_k\otimes e_k.
$$

参考为一个未读取的五维系统，向量化输出在前。置

$$
\begin{gathered}
a_j=\sqrt2\,|H_j\sqrt\rho\rangle\!\rangle,\qquad
\Pi=\bigoplus_j|a_j\rangle\langle a_j|,\\
\sigma_{\mathcal T}=(\mathcal T\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|),\qquad
F(\mathcal T)=N^2\operatorname{Tr}(\Pi\sigma_{\mathcal T}).
\end{gathered}
\tag{2.2}
$$

这里 $F$ 是线性且未缩放的通道分数；归一化重叠为 $F/N^2$。它分别对应既有卷 §3 的 $\mathcal G$ 与 $\mathcal F$，不可混用其归一化。

**命题 2.3（见证因子、下界与连续性）。** 向量 $\psi_\rho$ 和每个 $a_j$ 均归一化，$\Pi$ 是投影。若 $L_{jt}$ 是 $\mathcal T$ 的实际旗标 Kraus 矩阵，则

$$
F(\mathcal T)=\sum_{j,t}|\operatorname{Tr}(C_j^\dagger L_{jt})|^2,
\tag{2.3}
$$

与 Kraus 表示无关，并有

$$
\begin{gathered}
\|\widehat{\mathcal J}-\mathcal T\|_\diamond\ge
b(\mathcal T):=2\left(1-\frac{F(\mathcal T)}{N^2}\right),\\
|F(\mathcal T)-F(\mathcal T')|
\le N^2\|\mathcal T-\mathcal T'\|_\diamond.
\end{gathered}
\tag{2.4}
$$

证明。$\operatorname{Tr}\rho=(4r+3)/N=1$，且

$$
\operatorname{Tr}(\rho H_j^2)=\frac{2r+3/2}{N}=\frac12,
\qquad \sqrt2\rho H_j=C_j/N.
$$

因此 $\|a_j\|=1$，目标见证输出为

$$
\omega=\frac12\bigoplus_j|a_j\rangle\langle a_j|,
\qquad \operatorname{Tr}(\Pi\omega)=1.
$$

任一 Kraus 矩阵的投影贡献是 $2|\operatorname{Tr}(\rho H_jL_{jt})|^2$；乘以 $N^2$ 即得 (2.3)。式 (2.2) 直接保证表示无关性与线性。对两归一化输出作测量 $\{\Pi,I-\Pi\}$，目标分布为 $(1,0)$，模拟分布为 $(F/N^2,1-F/N^2)$，不折半距离为 $b(\mathcal T)$。若 $Y=Y_+-Y_-$ 为 Hermitian，每个测量效应 $M$ 都满足 $|\operatorname{Tr}(MY)|\le\operatorname{Tr}[M(Y_++Y_-)]$，对完整测量求和即得迹范数压缩。归一化纯化是 (1.3) 中合法测试，所以给出 (2.4) 的第一式。第二式由同一输入、$\|\Pi\|_\infty=1$ 及迹范数对偶性得到。$\square$

**定义 2.4（首次 PVM 的集合 $\mathcal K$ 与 $\mathcal C$）。** $\mathcal K$ 包含两类归一化带旗标通道：第一类为一个全五维幺正、报告一个确定旗标；第二类先指定非平凡完整输入 PVM $\{E_a\}$，其正秩之和为五，随后允许代数 CP 后代 $\Psi_{aj}$，只要求

$$
\sum_j\Psi_{aj}^\dagger(I_5)=E_a,
\qquad \mathcal T_j=\sum_a\Psi_{aj}.
\tag{2.5}
$$

等价地，任选 Kraus 表示，有

$$
L_{ajt}=L_{ajt}E_a,
\qquad \sum_{j,t}L_{ajt}^\dagger L_{ajt}=E_a.
\tag{2.6}
$$

置 $\mathcal C=\overline{\operatorname{conv}}(\mathcal K)$。不进行首次非平凡分拆时只允许第一类，绝不包含任意秩五 CP 续行。一般 CP 后代是下界所用的外部松弛，并非实际操作授权。

**命题 2.5（紧性、右支撑与实际包含）。** $\mathcal K$ 紧，$\mathcal C=\operatorname{conv}(\mathcal K)$ 非空紧凸，且 $\mathfrak S_{\rm fin}\subseteq\mathcal C$。

证明。若一族 Kraus 的效应之和为投影 $E_a$，则对 $x\in\ker E_a$，$\sum_{j,t}\|L_{ajt}x\|^2=0$。各项非负，故每个矩阵在核上为零，给出 (2.6) 的右支撑。固定一个有序正秩分拆时，完整投影元组由投影、正交、和及迹固定秩的闭方程定义，且有界，因此紧。采用输出优先 Choi 定义

$$
J(\Psi)=\sum_{k,\ell}\Psi(|e_k\rangle\langle e_\ell|)\otimes|e_k\rangle\langle e_\ell|.
$$

矩阵 $J(\Psi_{aj})$ 满足

$$
J(\Psi_{aj})\ge0,
\qquad \sum_j\operatorname{Tr}_{\rm out}J(\Psi_{aj})=E_a^{\mathsf T}.
$$

其迹分别不超过 $\operatorname{rank}E_a$；联合可行集闭且有界，求和给出的通道像紧。有序正秩分拆有限多个，幺正与确定旗标的集合也紧，故 $\mathcal K$ 紧。在通道所处的有限维实向量空间中，Carathéodory 定理把凸包的点表示为至多维数加一个点的凸组合；允许零权后，凸包是一个紧乘积的连续像，因而闭且紧。

对实际有限深度协议固定完整输入独立经典带。若无非平凡 PVM，它只有幺正乘积与确定旗标，属于第一类。否则记首次 PVM 前的幺正乘积为 $U$、首次结果为 $R_a$，令 $E_a=U^\dagger R_aU$。每个末端后代为 $L_t=M_tR_aU$，满足 $L_t=L_tE_a$。从叶端逆向归纳，停止节点续行效应为 $I$，幺正节点共轭 $I$ 仍为 $I$，完整 PVM 节点对结果求和仍为 $I$；故同一实际子树满足 $\sum_{t\succ a}L_t^\dagger L_t=E_a$。不同分支的反馈和后代可以不同，按实际末端旗标分组仍满足 (2.5)。固定带通道因而属于 $\mathcal K$。

对可测经典带积分仍在闭凸集 $\mathcal C$ 中：有界有限维通道值函数可用其值域中有限小球的可测逆像划分来逼近，所选有限值均来自 $\mathcal K$，相应积分是有限凸组合，并在球半径趋零时收敛。故非原子随机性也不改变包含关系。这不表示任意松弛 CP 续行可实施。$\square$

本节见证、紧松弛及实际包含均继承既有卷定义 3.1、引理 3.2、定理 3.3 与命题 3.6 的结构；重述其所需论证是为固定后文的归一化与共同实现条件。

## 3. 完整分支界与非 $3+2$ 分拆的显式间隙

**引理 3.1（共同右支撑的分支估计）。** 设非零投影 $E$ 与矩阵 $L_t=L_tE$ 满足 $\sum_tL_t^\dagger L_t=E$，实际旗标为 $j_t$。在 $EH$ 上置 $A_j=EC_j^2E$，则

$$
\sum_t|\operatorname{Tr}(C_{j_t}^\dagger L_t)|^2
\le\max_{0\le p\le1}
\left[\operatorname{Tr}_{EH}\sqrt{pA_0+(1-p)A_1}\right]^2.
\tag{3.1}
$$

证明。这是既有卷引理 3.2 的分支界。为使后面的稳定常数可直接核对，给出完整推导。对 $EH$ 上任意正定 $Y$，对 $C_jEY^{-1/2}$ 与 $L_tY^{1/2}$ 用 Hilbert–Schmidt Cauchy–Schwarz；其内积由右支撑及迹循环性恰为 $\operatorname{Tr}(C_j^\dagger L_t)$，故

$$
|\operatorname{Tr}(C_j^\dagger L_t)|^2
\le\operatorname{Tr}_{EH}(A_jY^{-1})\,
\operatorname{Tr}_{EH}(YL_t^\dagger L_t).
\tag{3.2}
$$

只要两个第一因子都不超过一，完整效应求和就把总分数界为 $\operatorname{Tr}_{EH}Y$。该权重在共同右支撑一侧，不可换成无依据的左加权。

取 $\varepsilon>0$，置 $A_{j,\varepsilon}=A_j+\varepsilon I_{EH}$、$A_\varepsilon(p)=pA_{0,\varepsilon}+(1-p)A_{1,\varepsilon}$、$h_\varepsilon(p)=\operatorname{Tr}_{EH}\sqrt{A_\varepsilon(p)}$，并在闭区间上取一个最大点 $p_\varepsilon$。若 $Z=\sqrt{A_\varepsilon(p)}$，微分 $Z^2=A_\varepsilon(p)$ 得

$$
ZZ'+Z'Z=A_0-A_1,
\qquad
h_\varepsilon'(p)=\frac12\operatorname{Tr}_{EH}\!\left[A_\varepsilon(p)^{-1/2}(A_0-A_1)\right].
$$

第二式不要求交换性：在正定 $Z$ 的本征基中，$X\mapsto ZX+XZ$ 乘以两个正本征值之和，因而可逆；这给出微分存在性，再左乘 $Z^{-1}$ 取迹即得公式。令 $h=h_\varepsilon(p_\varepsilon)$、$Y=h\sqrt{A_\varepsilon(p_\varepsilon)}$ 及 $t_j=\operatorname{Tr}_{EH}(A_{j,\varepsilon}Y^{-1})$，则

$$
p_\varepsilon t_0+(1-p_\varepsilon)t_1=1,
\qquad h_\varepsilon'(p_\varepsilon)=\frac h2(t_0-t_1).
$$

内点最大时两者均为一；在 $p_\varepsilon=0$ 时右导数非正，故 $t_0\le t_1=1$；在 $p_\varepsilon=1$ 时左导数非负，故 $t_1\le t_0=1$。所以 $\operatorname{Tr}(A_jY^{-1})\le1$，由 (3.2) 得上界 $h^2$。

若 $k=\operatorname{rank}E$，则对所有 $p$ 一致有

$$
0\le\operatorname{Tr}\sqrt{A(p)+\varepsilon I_{EH}}
-\operatorname{Tr}\sqrt{A(p)}\le k\sqrt\varepsilon,
\qquad A(p)=pA_0+(1-p)A_1.
$$

这由逐个本征值的 $0\le\sqrt{\lambda+\varepsilon}-\sqrt\lambda\le\sqrt\varepsilon$ 得到。无正则化的迹一致有界，因此平方迹及其最大值也一致收敛，令 $\varepsilon\downarrow0$ 即得 (3.1)，包括奇异与端点情形。可数矩阵族由非负部分和极限处理；有限维 CP 映射本身总可选有限 Kraus 表示。这里的最大点只是符号存在性选择。$\square$

**命题 3.2（全分拆界与 $1/6$ 间隙）。** 在 $\mathcal K$ 上 $F\le65$。若某个 $\mathcal K$ 分量没有秩 $3+2$ 的首次 PVM，则其亏损满足

$$
65-F\ge\frac16.
\tag{3.3}
$$

两个端点的 $F$ 均为六十五，所以 $\max_{\mathcal C}F=65$，即归一化支撑最大值仍为 $65/N^2$。

证明。对首次投影 $E$，记 $k=\operatorname{rank}E$、$\sigma=\operatorname{Tr}(ES)$，并写

$$
M(p)=4pP+4(1-p)Q+9S,\qquad
EM(p)E\le H_E:=4E+5ESE.
$$

$H_E$ 在 $EH$ 上的谱是 $4+5\sigma$ 和 $k-1$ 个 $4$。正矩阵的有序本征值单调性及 (3.1) 给出分支上界

$$
g_k(\sigma)=\left[2(k-1)+\sqrt{4+5\sigma}\right]^2.
\tag{3.4}
$$

同一完整 PVM 的秩之和为五，$S$ 重叠之和为一。

对秩 $3+2$，令秩三的重叠为 $\sigma$，秩二为 $1-\sigma$。总分数至多

$$
G(\sigma)=\left[4+\sqrt{4+5\sigma}\right]^2
+\left[2+\sqrt{9-5\sigma}\right]^2.
$$

整个区间上

$$
G'(\sigma)=5\left[\frac4{\sqrt{4+5\sigma}}-\frac2{\sqrt{9-5\sigma}}\right]
\ge\frac53,
\qquad G(1)=65.
\tag{3.5}
$$

因为两比值分别至少为 $4/3$、至多为一。这也预先给出 $65-G(\sigma)\ge(5/3)(1-\sigma)$。

若各秩至多三且不是 $3+2$，则秩三时其余为 $1+1$；没有秩三时 $k_a^2\le2k_a$。故 $\sum_ak_a^2\le11$。先展开平方，再用 $\sqrt{4+5\sigma}\le2+5\sigma/4$，得到

$$
\begin{aligned}
g_k(\sigma)
&=4(k-1)^2+4(k-1)\sqrt{4+5\sigma}+4+5\sigma\\
&\le4(k-1)^2+4(k-1)(2+5\sigma/4)+4+5\sigma\\
&=4k^2+5k\sigma.
\end{aligned}
$$

总分数因而至多 $4\cdot11+5\cdot3=59$。

剩下的非平凡分拆为 $4+1$。$M(p)$ 的全空间谱为 $9,4p,4p,4(1-p),4(1-p)$。Rayleigh 极小极大原理把任意秩四压缩的各个递减本征值界为全空间的前四个。当 $p\ge1/2$ 时，其平方根迹至多

$$
3+4\sqrt p+2\sqrt{1-p}\le3+2\sqrt5,
$$

最后一步为对 $(2,1)$ 与 $(\sqrt p,\sqrt{1-p})$ 的 Cauchy–Schwarz；$p\le1/2$ 时交换 $P,Q$。秩四分数至多 $29+12\sqrt5$，秩一分数至多九。为了保留显式间隙，使用严格符号比较

$$
161^2=25921>25920=5\cdot72^2
\quad\Longrightarrow\quad
\sqrt5<\frac{161}{72},
$$

故总分数小于 $38+161/6=65-1/6$。这是同一 PVM 的两个有效分支上界之和，并未假设它们同时取到。

无非平凡 PVM 时，通道是确定旗标上的幺正 $U$。在 $C_j$ 的奇异基中，每个幺正对角元模不超过一，所以 $|\operatorname{Tr}(C_j^\dagger U)|\le\operatorname{Tr}C_j=7$，分数至多四十九。以上穷尽非平凡完整 PVM 的正秩分拆，证明 (3.3) 及 $\mathcal K$ 上的界。线性性与连续性把上界传至 $\mathcal C$。端点的两个重叠是七与四，故 $F(\mathcal A_\pm)=7^2+4^2=65$。这些支撑和分拆事实复用既有卷定理 3.3、命题 3.6；(3.3) 明确量化了所需的分拆分离余量。$\square$

## 4. 同一首次测量的方向与完整 Kraus 残差

下文采用 $\|B\|_{\rm HS}^2=\operatorname{Tr}(B^\dagger B)$。

**引理 4.1（实际分支分数给出的方向稳定性）。** 设 $\mathcal T\in\mathcal K$ 的首次 PVM 为秩 $3+2$，秩三投影为 $E$，且 $d=65-F(\mathcal T)$。则存在

$$
E_0\in\{P+S,Q+S\},\qquad
\|E-E_0\|_{\rm HS}^2\le6d.
\tag{4.1}
$$

证明。令 $f_3,f_2$ 为该通道这两个完整分支的实际分数，$F=f_3+f_2$，并令 $t=1-\operatorname{Tr}(ES)$。由 (3.5)，$t\le3d/5$。又有 $g_2(0)=16$ 及

$$
g_2'(t)=5\left[1+\frac2{\sqrt{4+5t}}\right]\le10,
$$

故 $f_2\le16+10t$，从而

$$
f_3\ge49-d-10t\ge49-7d,
\qquad 0\le e_3:=49-f_3\le7d.
\tag{4.2}
$$

上端 $f_3\le49$ 由 $g_3(\sigma)\le49$ 得到。这里的 $t,f_3,f_2$ 来自同一实际分拆与同一完整后代，不能独立挑选。

在 (3.1) 中为秩三分支选择最大点 $p$。在 $EH$ 上记 $A=EM(p)E$、$H=4E+5ESE$，则

$$
0\le A\le H\le9E,
\qquad \operatorname{Tr}\sqrt A\ge\sqrt{f_3},
\qquad \operatorname{Tr}\sqrt H\le7.
$$

设有序本征值分别为 $a_i,h_i$。即使 $A,H$ 不交换，正次序仍给出 $0\le a_i\le h_i\le9$，因此

$$
\begin{aligned}
\operatorname{Tr}(H-A)
&=\sum_i(\sqrt{h_i}-\sqrt{a_i})(\sqrt{h_i}+\sqrt{a_i})\\
&\le6\bigl(\operatorname{Tr}\sqrt H-\operatorname{Tr}\sqrt A\bigr)
\le6(7-\sqrt{f_3})\\
&=\frac{6e_3}{7+\sqrt{f_3}}
\le\frac{6e_3}{7}\le6d.
\end{aligned}
\tag{4.3}
$$

另一方面，$H-A=4E[(1-p)P+pQ]E$。若 $p\ge1/2$，则 $2\operatorname{Tr}(EQ)\le\operatorname{Tr}(H-A)\le6d$。取 $E_0=P+S=I-Q$，由两个投影同为秩三，

$$
\|E-E_0\|_{\rm HS}^2=2[3-\operatorname{Tr}(EE_0)]
=2\operatorname{Tr}(EQ)\le6d.
$$

若 $p\le1/2$，交换 $P,Q$，取 $E_0=Q+S$。当 $p=1/2$ 时任一选择均满足所列推导。没有假设近极大通道本来处于某个规范方向。$\square$

**引理 4.2（含退化主角的投影校正）。** 对同秩投影 $E,E_0$，存在幺正 $U$ 使

$$
UEU^\dagger=E_0,
\qquad \|U-I\|_\infty\le\sqrt2\|E-E_0\|_\infty.
\tag{4.4}
$$

若 $L=L E$，则 $LU^\dagger$ 的右支撑是 $E_0$；对应通道应作右预合成 $\mathcal T\circ\operatorname{Ad}_{U^\dagger}$。

证明。对两个子空间的正交基重叠矩阵作奇异值分解，得到主向量 $e_i,f_i$，满足 $\langle e_i,f_j\rangle=\delta_{ij}\cos\theta_i$，$0\le\theta_i\le\pi/2$。零角可选 $e_i=f_i$，固定不动。对非零角置 $g_i=(f_i-\cos\theta_i e_i)/\sin\theta_i$。由这些内积关系，$g_i$ 正交归一且与全部 $e_j$ 正交；相应二维平面互相正交。在每个平面上取旋转

$$
Ue_i=\cos\theta_i e_i+\sin\theta_i g_i=f_i,
\qquad Ug_i=-\sin\theta_i e_i+\cos\theta_i g_i.
$$

共同方向与剩余正交补取恒等。重复角不影响构造；直角时公式同样成立。平面上的两个投影差的范数为 $\sin\theta_i$，而 $\|U-I\|$ 为 $2\sin(\theta_i/2)\le\sqrt2\sin\theta_i$。对正交直和取最大值即证 (4.4)。最后

$$
(LU^\dagger)E_0=LU^\dagger UEU^\dagger=LEU^\dagger=LU^\dagger,
$$

且完整效应变为 $UEU^\dagger$。所以这里必须使用所写的右预合成方向；只转输出不能校正输入右支撑。$\square$

**引理 4.3（规范 PVM 的全部残差，包括错误旗标）。** 设归一化带旗标通道 $\mathcal B$ 的两个首次右支撑恰为 $E_0=P+S$ 与 $Q$，每支满足 (2.6)，保留原有旗标与任意 CP 后代。记 $d'=65-F(\mathcal B)$。则

$$
\|\mathcal B-\mathcal A_+\|_\diamond\le\sqrt{2d'}.
\tag{4.5}
$$

交换 $P,Q$ 与两个旗标时，同一结论给出到 $\mathcal A_-$ 的界。

证明。在秩三支取 $Y_3=14P+21S$，在秩二支取 $Y_2=8Q$。对每个带有原旗标 $j$ 的 Kraus 矩阵 $L$ 定义

$$
D_L=\operatorname{Tr}(Y_aL^\dagger L)-|\operatorname{Tr}(C_j^\dagger L)|^2,
\qquad a=3\ \text{或}\ 2.
\tag{4.6}
$$

(3.2) 的第一因子在四种情形中为

| 首次支撑 | 原旗标 $j$ | $\operatorname{Tr}(EC_j^2EY_a^{-1})$ |
| --- | --- | --- |
| $P+S$ | $0$ | $1$ |
| $P+S$ | $1$ | $3/7$ |
| $Q$ | $0$ | $0$ |
| $Q$ | $1$ | $1$ |

所有逆仅在支撑内取。故各 $D_L\ge0$；两支分别完整给出

$$
\sum_LD_L=\operatorname{Tr}Y_3+\operatorname{Tr}Y_2-F(\mathcal B)=49+16-F(\mathcal B)=d'.
\tag{4.7}
$$

这一步不删掉错误旗标或零分数矩阵。

对秩三、旗标零的 $L$，矩阵 $B_0=C_0E_0Y_3^{-1/2}$ 为 Hilbert–Schmidt 单位向量。$LY_3^{1/2}$ 到其张成直线的正交投影残差平方恰为 $D_L$，投影系数为 $\operatorname{Tr}(C_0^\dagger L)$。由 $C_0E_0Y_3^{-1}=E_0/7$，定义

$$
M_L=\frac{\operatorname{Tr}(C_0^\dagger L)}7E_0.
$$

因为 $Y_3$ 的最小本征值为十四，$\|L-M_L\|_{\rm HS}^2\le D_L/14$。对秩三、旗标一，令 $M_L=0$，系数 $3/7$ 给出

$$
D_L\ge\frac47\operatorname{Tr}(Y_3L^\dagger L)\ge8\|L\|_{\rm HS}^2.
$$

对秩二、旗标一，同样的正交投影使用 $C_1QY_2^{-1}=Q/4$，取

$$
M_L=\frac{\operatorname{Tr}(C_1^\dagger L)}4Q,
\qquad \|L-M_L\|_{\rm HS}^2\le D_L/8.
$$

对秩二、旗标零，分数为零，取 $M_L=0$，而 $D_L=8\|L\|_{\rm HS}^2$。四类求和得到

$$
\sum_L\|L-M_L\|_{\rm HS}^2\le d'/8.
\tag{4.8}
$$

由这些 $M_L$ 得到未必归一化的 CP 仪器

$$
\mathcal B_{\rm app}=(a\operatorname{Ad}_{E_0},\ b\operatorname{Ad}_Q),
\quad a=\sum_{3,0}\left|\frac{\operatorname{Tr}(C_0^\dagger L)}7\right|^2,
\quad b=\sum_{2,1}\left|\frac{\operatorname{Tr}(C_1^\dagger L)}4\right|^2.
$$

同一完整效应与上表的 Cauchy–Schwarz 界把秩三总分数界为四十九、秩二界为十六，故 $0\le a,b\le1$。

保留每个 Kraus 的首次结果、原旗标与细分索引 $\ell=(a,j,t)$，定义分析堆叠

$$
Vx=\sum_\ell |j\rangle\otimes L_\ell x\otimes|\ell\rangle,
\qquad
Wx=\sum_\ell |j\rangle\otimes M_\ell x\otimes|\ell\rangle.
$$

环境中的索引同时保存旗标，偏迹后只有原来的经典旗标块；错误旗标上的零近似仍保留其索引。完整性、$a,b\le1$ 及 (4.8) 给出

$$
V^\dagger V=I,\qquad W^\dagger W=aE_0+bQ,\qquad
\|V\|_\infty=1,\quad\|W\|_\infty\le1,\quad
\|V-W\|_\infty\le\varepsilon_K:=\sqrt{d'/8}.
\tag{4.9}
$$

最后一个界使用堆叠的算子范数不超过 Hilbert–Schmidt 范数。

对任意复 $X$ 及任意有限参考，使用恒等式

$$
VXV^\dagger-WXW^\dagger=(V-W)XV^\dagger+WX(V-W)^\dagger
$$

以及引理 2.1 的偏迹压缩，得 $\|\mathcal B-\mathcal B_{\rm app}\|_\diamond\le2\varepsilon_K$。这些乘法同时张量参考恒等，常数不变。另一方面 $\mathcal A_+-\mathcal B_{\rm app}$ 是 CP 映射，其效应为 $I-W^\dagger W\ge0$，所以引理 2.1 给出

$$
\|\mathcal A_+-\mathcal B_{\rm app}\|_\diamond
=\|I-W^\dagger W\|_\infty
=\|V^\dagger V-W^\dagger W\|_\infty
\le2\varepsilon_K.
$$

这里也只用了两项展开及两个堆叠均为压缩。三角不等式得到 $4\varepsilon_K=\sqrt{2d'}$，证明 (4.5)。所有残差都来自原有完整 Kraus 家族；分析环境与投影残差没有赋予模拟器额外量子系统或 CP 原语。$\square$

## 5. 整个紧凸松弛上的显式四次根模量

**定理 5.1（到完整极大面的有效稳定性）。** 对每个 $\mathcal T\in\mathcal C$，存在同一线段中的 $\mathcal A_t$，使

$$
\|\mathcal T-\mathcal A_t\|_\diamond\le64[65-F(\mathcal T)]^{1/4}.
\tag{5.1}
$$

在 $F=65$ 时右侧为零；因此 $\{\mathcal T\in\mathcal C:F(\mathcal T)=65\}=\mathcal M$，与既有卷定理 3.7 的完整极大面一致。

证明。先对单个 $\mathcal K$ 分量，令 $d=65-F(\mathcal T)$。若 $d\ge1/16$，任选一个端点。两个归一化通道距离至多二，而 $64d^{1/4}\ge32$，故所需界成立。

若 $0\le d<1/16$，命题 3.2 的 $1/6$ 分拆间隙强制首次 PVM 为秩 $3+2$。由引理 4.1 选择 $E_0$，再由引理 4.2 取 $U$，令 $u=\|U-I\|_\infty$，则

$$
u\le\sqrt2\|E-E_0\|_\infty\le\sqrt{12d}.
$$

置 $\mathcal T'=\mathcal T\circ\operatorname{Ad}_{U^\dagger}$。其 Kraus 是 $LU^\dagger$，两个完整右效应恰为 $E_0,I-E_0$。对于任意复参考扩张，两项展开给出 $\|\operatorname{Ad}_{U^\dagger}-\operatorname{id}\|_\diamond\le2u$；引理 2.1 及范数复合的次乘性因而给出

$$
\|\mathcal T-\mathcal T'\|_\diamond\le2u,
\qquad 0\le d':=65-F(\mathcal T')\le d+2N^2u.
\tag{5.2}
$$

非负性可直接由引理 4.3 的亏损和得到，也由一般支撑上界得到。若 $E_0=P+S$，应用引理 4.3；若为 $Q+S$，交换两个块与旗标。所得端点 $\mathcal A_{\rm end}$ 满足

$$
\|\mathcal T-\mathcal A_{\rm end}\|_\diamond
\le2u+\sqrt{2(d+2N^2u)}.
\tag{5.3}
$$

现在只作精确符号放宽。由 $r<3/2$ 得 $N^2<77$，且 $\sqrt{12}<4$。因为 $0\le d<1$，有

$$
u\le4\sqrt d,\qquad
 d+2N^2u\le d+616\sqrt d\le617\sqrt d.
$$

故 (5.3) 至多

$$
8\sqrt d+\sqrt{1234}\,d^{1/4}\le44d^{1/4}\le64d^{1/4},
$$

其中用 $\sqrt d\le d^{1/4}$ 与 $1234<36^2$。这里的四十四只是小亏损支路的证明余量，统一声明的常数为六十四；不另声称常数改进或最优性。$d=0$ 时所有投影与 Kraus 残差均为零，同一推导直接适用，无需除以 $d$。

对有限凸组合 $\mathcal T=\sum_i\lambda_i\mathcal T_i$，为每个分量取上述比较端点 $\mathcal A_i$，并使用原来的同一组权重定义 $\mathcal A=\sum_i\lambda_i\mathcal A_i\in\mathcal M$。线性性给出 $d=\sum_i\lambda_i d_i$，而三角不等式及 $x^{1/4}$ 的凹性给出正确方向

$$
\|\mathcal T-\mathcal A\|_\diamond
\le64\sum_i\lambda_i d_i^{1/4}
\le64\left(\sum_i\lambda_i d_i\right)^{1/4}=64d^{1/4}.
\tag{5.4}
$$

这同时处理异向首次测量与输入独立硬币，未把不同权重的最优读数拼接。

为显式核对闭包转移，取有限凸组合序列 $\mathcal T_n\to\mathcal T\in\mathcal C$。对应比较点 $\mathcal A_n$ 在紧线段 $\mathcal M$ 中有收敛子列，极限仍在 $\mathcal M$。分数和范数的连续性把 (5.4) 传到极限，得到 (5.1)。紧性只负责已给出常数的不等式的闭包转移，没有用它代替有效模量。最后，$F=65$ 时 (5.1) 迫使通道就在 $\mathcal M$；反向由端点及线性性已知。这也在本定量推导内核对了所引用的整个面，而非只核对若干例子。$\square$

## 6. 同一通道的相干约束与显式联合间隙

**命题 6.1（合法中点与支撑加 $S$ 测试的限制）。** 整个极大面逐旗标作用为

$$
\begin{aligned}
\mathcal A_{t,0}(X)&=PXP+t(PXS+SXP)+tSXS,\\
\mathcal A_{t,1}(X)&=QXQ+(1-t)(QXS+SXQ)+(1-t)SXS.
\end{aligned}
\tag{6.1}
$$

其效应为 $P+tS$、$Q+(1-t)S$，且在 $S$ 上的完整输出为 $(tS,(1-t)S)$。对一般通道定义 $e_S(\mathcal T)=\|(\widehat{\mathcal J}-\mathcal T)(S)\|_1$，则

$$
e_S(\mathcal A_t):=\|(\widehat{\mathcal J}-\mathcal A_t)(S)\|_1=2|t-1/2|.
\tag{6.2}
$$

只使用证书 $\max\{b(\mathcal T),e_S(\mathcal T)\}$，在三个实际类上的最小值仍恰为 $L$。

证明。展开端点及其同权凸组合即得 (6.1)，取迹与代入 $S$ 得其余公式。实际类在 $\mathcal C$ 内，所以 $F\le65$，从而 $b\ge L$。合法公平混合 $\mathcal A_{1/2}$ 却同时满足 $F=65$ 及 $\mathcal A_{1/2}(S)=\widehat{\mathcal J}(S)$，包括旗标与量子输出。因此同一通道使上述最大值等于 $L$，并在有限深度类中已经取到。这是既有卷命题 3.8 的限制反例。它不排除另加相干关系，但排除了以一个端点的 $S$ 误差代替整个面的论证。$\square$

**引理 6.2（固定相干输入与整个面的 $U_0$ 接口）。** 取单位系统向量及其误差函数

$$
\psi_\star=\frac{e_0+e_1}{2}+\frac{s}{\sqrt2},\qquad
h(\mathcal T)=\|(\widehat{\mathcal J}-\mathcal T)(|\psi_\star\rangle\langle\psi_\star|)\|_1.
\tag{6.3}
$$

则 $h(\mathcal T)\le\|\widehat{\mathcal J}-\mathcal T\|_\diamond$，且

$$
|h(\mathcal T)-h(\mathcal T')|\le\|\mathcal T-\mathcal T'\|_\diamond,
\qquad
h(\mathcal A_t)\ge U_0\quad(0\le t\le1).
\tag{6.4}
$$

中点还满足完整菱形等式 $\|\widehat{\mathcal J}-\mathcal A_{1/2}\|_\diamond=U_0$。这些是既有卷引理 3.9 的接口。

证明。前两个范数比较直接由归一化输入及逆三角不等式得到。令 $F_{\rm sw}$ 交换 $e_0,e_1$ 和 $e_3,e_4$，固定 $s$。变换

$$
(\mathscr R\mathcal T)_j(X)=F_{\rm sw}\mathcal T_{1-j}(F_{\rm sw}XF_{\rm sw})F_{\rm sw}
$$

固定规范目标、交换 $\mathcal A_t$ 与 $\mathcal A_{1-t}$，且固定 $\psi_\star$。所以 $h(\mathcal A_t)=h(\mathcal A_{1-t})$；$h$ 的凸性给出 $h(\mathcal A_t)\ge h(\mathcal A_{1/2})$。

置 $\epsilon=q-1/2>0$。中点的旗标差映射为 $\epsilon(P_jXS+SXP_j)$。对 (6.3) 的输入，正交向量 $P_j\psi_\star$ 与 $S\psi_\star$ 的范数为 $1/2$ 与 $1/\sqrt2$，所以每块两个非零特征值为 $\pm\epsilon/(2\sqrt2)$，每块迹范数为 $\epsilon/\sqrt2$，两块合计 $\sqrt2\epsilon=U_0$，证明整个面的下界。

为核对中点的完整菱形上界，取任意有限参考上的单位纯向量 $\psi$，写 $x_j=(P_j\otimes I)\psi$、$x_S=(S\otimes I)\psi$，令 $p_j=\|x_j\|^2$、$w=\|x_S\|^2$。三向量正交，$p_0+p_1+w=1$。差输出第 $j$ 块是 $\epsilon(|x_j\rangle\langle x_S|+|x_S\rangle\langle x_j|)$，包括零向量的退化情形，其迹范数为 $2\epsilon\sqrt{p_jw}$。求和得

$$
2\epsilon\sqrt w(\sqrt{p_0}+\sqrt{p_1})
\le2\epsilon\sqrt{2w(1-w)}\le\sqrt2\epsilon=U_0.
$$

凸性涵盖混合态。要从所有态涵盖 (1.3) 的所有复测试，对任意复 $X$ 再添加一个只供分析的二值参考并取

$$
Y=\frac12\begin{pmatrix}0&X\\X^\dagger&0\end{pmatrix}.
$$

奇异值分解给出 $\|Y\|_1=\|X\|_1$；差映射保持伴随，故输出具有相同块形和相同范数对应。分解 $Y=Y_+-Y_-$，分别按迹归一化非零部分，使用已经证明的所有参考态界并求和，就得到输出范数至多 $U_0\|X\|_1$。因此完整菱形范数至多 $U_0$，而固定 $\psi_\star$ 达到它，得到等式。参考扩张与分解只是范数论证，不是新的模拟能力。$\square$

**定理 6.3（同一通道的有效联合证书）。** 对每个 $\mathcal T\in\mathcal C$，以该同一通道的 $d=65-F(\mathcal T)$，有

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge\max\left\{L+\frac{2d}{N^2},\ U_0-64d^{1/4}\right\}
\ge L+\frac{(U_0-L)^4}{2^{27}N^2}.
\tag{6.5}
$$

其中末项增量严格大于 $2^{-58}$。

证明。命题 2.3 的同一支撑输入给出

$$
b(\mathcal T)=2\left[1-\frac{65-d}{N^2}\right]=L+\frac{2d}{N^2}.
$$

定理 5.1 给出某个 $\mathcal A_t$，引理 6.2 的 Lipschitz 界给出 $h(\mathcal T)\ge h(\mathcal A_t)-64d^{1/4}\ge U_0-64d^{1/4}$。两个测试的输入可以不同，但都约束同一通道、同一完整菱形误差；不是两个边缘优化值的拼接。因此可取两下界的最大值。

由 (1.4)、$r>1$ 与 $r<3/2$，$41-24r>5>0$，故 $g=U_0-L>0$，且 $0<g<U_0<1$。令

$$
a=\left(\frac g{128}\right)^4.
$$

若 $d\ge a$，支撑证书给出

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge L+\frac{2a}{N^2}
=L+\frac{g^4}{2^{27}N^2}=L+\Delta.
$$

若 $d\le a$，相干证书给出

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge U_0-64\frac g{128}=L+\frac g2\ge L+\Delta.
$$

最后一步因为 $\Delta/g=g^3/(2^{27}N^2)<1/2$；$d=a$ 的边界也已包含。这是完整阈值分拆，无需求解任何最大或最小值。

为给出简单有理量级，平方比较 $2>49/25$ 与 $2<9/4$ 得 $7/5<r<3/2$。因此

$$
r-1>\frac25,\qquad 41-24r>5,\qquad
N^2<77,\qquad rN^2<\frac{231}{2},
$$

故 $g>4/231>1/64$，后一个比较等价于 $256>231$。于是

$$
\Delta=\frac{g^4}{2^{27}N^2}
>\frac1{77\cdot2^{51}}>2^{-58},
$$

其中 $77<128$。这给出未执行的精确符号严格比较，不声明常数或指数尖锐。由于实际类包含于松弛，松弛上统一的下界按正确方向约束原问题。$\square$

## 7. 所有角度、终止与闭包的共同量词

**定义 7.1（原始矩阵与合法坐标）。** 令

$$
\begin{gathered}
u=q(e_0+e_3),\quad v=q(e_1+e_4),\quad z=s,\qquad
u_-=q(e_0-e_3),\quad v_-=q(e_1-e_4),\\
K_0=|u\rangle\langle e_0|+q|v\rangle\langle s|+|z\rangle\langle e_4|,\qquad
K_1=|u\rangle\langle e_1|+q|v\rangle\langle s|+|z\rangle\langle e_3|,\\
A_0(\theta)=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1(\theta)=i\sin\theta K_0+\cos\theta K_1,\qquad
\mathcal J_\theta(X)=\bigoplus_jA_j(\theta)XA_j(\theta)^\dagger,\\
T_0=[u\ \ u_-\ \ v\ \ v_-\ \ z],\qquad
T_1=[u_-\ \ u\ \ v\ \ z\ \ v_-],\qquad
D_\theta=\cos\theta I+i\sin\theta F_{\rm sw}.
\end{gathered}
\tag{7.1}
$$

这些实际矩阵与坐标接口继承既有卷定义 1.2、引理 2.1。

**引理 7.2（全角度的菱形等距与见证转移）。** 对每个实数 $\theta$，原目标与规范目标在三个实际类上等距等价。若 $\mathsf W=\bigoplus_jT_j$，则

$$
\mathcal J_\theta=\operatorname{Ad}_{\mathsf W}\circ\widehat{\mathcal J}\circ\operatorname{Ad}_{D_\theta}.
\tag{7.2}
$$

证明。$F_{\rm sw}^\dagger=F_{\rm sw}$、$F_{\rm sw}^2=I$，且逐基向量可得 $K_0F_{\rm sw}=K_1$、$K_1F_{\rm sw}=K_0$，所以 $D_\theta$ 幺正且 $K_jD_\theta=A_j(\theta)$。每个 $T_j$ 的列是完整五维正交归一基，故幺正；逐列得到 $T_jH_j=K_j$，证明 (7.2)。最前施加 $D_\theta$、最后按已知经典旗标施加 $T_j$ 及其逆，都在实际菜单中并保持停止类型。它们在任意复参考扩张上保持迹范数，因而是菱形等距；连续性将双向对应传到闭包。$\mathsf W$ 只是条件经典控制的记法，不授予相干旗标寄存器。

对原通道 $\mathcal T$，规范通道是 $\widetilde{\mathcal T}=\operatorname{Ad}_{\mathsf W^\dagger}\circ\mathcal T\circ\operatorname{Ad}_{D_\theta^\dagger}$。支撑测试取输入 $(D_\theta^\dagger\otimes I)\psi_\rho$ 与投影 $(\mathsf W\otimes I)\Pi(\mathsf W^\dagger\otimes I)$，相干测试取输入 $D_\theta^\dagger\psi_\star$；逆输出坐标给出的正是前文同一规范通道的读数。因此全部常数对每个实角度一致。$\square$

**引理 7.3（忠实输入的有限截断与完整 CP 残余）。** 有

$$
\mathfrak S_{\rm fin}\subseteq\mathfrak S_{\rm as}\subseteq\mathfrak S_{\rm cl}\subseteq\mathcal C,
\qquad \overline{\mathfrak S_{\rm as}}^{\diamond}=\mathfrak S_{\rm cl}.
\tag{7.3}
$$

到固定目标的距离在三个类上有相同下确界。

证明。沿用既有卷引理 2.2 的忠实输入论证。对几乎必然终止实际协议，令 $R_n$ 为深度 $n$ 尚未停止路径的平均效应。完整结果树给出 $0\le R_n\le I$，且在忠实输入 $I_5/5$ 上的几乎必然终止给出 $\operatorname{Tr}R_n\to0$。在深度 $n$ 立即停止所有残余路径，保留当时寄存器并赋固定旗标，得到合法有限深度 $\mathcal T_n$。

原残余续行与替代残余均为 CP 映射，效应同为 $R_n$。对原续行需核对耗尽性：整体永不停止的残余效应是正的，而其在 $I_5/5$ 上的迹为零，故它为零；因此深度 $n$ 之后所有停止叶的效应恰好耗尽 $R_n$。这里直接使用平均效应，无需对异常经典带或每个条件态另作统一停止假设。引理 2.1 给出

$$
\|\mathcal T-\mathcal T_n\|_\diamond
\le2\|R_n\|_\infty\le2\operatorname{Tr}R_n\longrightarrow0.
\tag{7.4}
$$

有界带积分及可数停止叶求和定义有限维 CP 映射，故其有限 Kraus 表示可用于该范数恒等式，不增加操作。显然有限深度协议几乎必然终止，由此得到前两个包含及闭包等式；命题 2.5 与 $\mathcal C$ 的闭性给出最后包含。连续的距离函数在稠密类与其闭包上有相同下确界，中间类亦然。不要求有限期望时长，也不把非终止无限操作当作协议。由同一包含，(6.5) 对全部几乎必然终止与闭包通道成立。$\square$

**推论 7.4（全协议区间与闭包取到边界）。** 定理 1.3 成立。$\mathfrak S_{\rm cl}$ 上存在某个抽象极小通道，但这不识别 $d_\star$，也不保证有限深度或几乎必然终止实现。

证明。引理 7.2–7.3 把定理 6.3 传至所有角度及三个实际类，并识别共同下确界。严格上界直接引用既有卷定理 7.1 在 $\tau=1/10000$ 的结论，所用实际协议见该卷定义 4.1、4.3、命题 4.2，完整复参考误差公式见定理 6.2。该协议只用完整倾斜 PVM、全五维条件幺正及输入独立的块幺正与旗标交换混合，属于有限深度菜单，故提供 (1.8) 的上界。本文不重述其整套倾斜误差证明，也不声称选定参数或该族全局最优。

归一化带旗标通道的 Choi 矩阵为正、具有固定偏迹及固定迹，形成有限维紧集；经典旗标的对角块限制也是闭条件。非空闭子集 $\mathfrak S_{\rm cl}$ 因而紧，菱形距离连续，故有极小者。引理 7.3 识别其值为 $d_\star$。这个存在性结论只涉及闭包中的通道，不提供停止协议，不证明 $\mathfrak S_{\rm as}=\mathfrak S_{\rm cl}$，也不证明任一实际停止类取到。$\square$

## 8. 来源、新内容与未决边界

**约定 8.1（来源相对的贡献）。** 本文的既有卷指《[AURIC FIB 全输入带旗标仪器的精确支撑面、严格距离间隙与倾斜投影上界](AURIC_FIB_FLAGGED_PROJECTIVE_DISTANCE_IMPROVEMENT.md)》。其 §3 的归一化见证、共同右支撑界、全部秩分拆的支撑上界、紧首次 PVM 松弛、整个极大面、合法中点反例及固定相干测试是本文的来源接口：对应定义 3.1、引理 3.2、定理 3.3、命题 3.6、定理 3.7、命题 3.8、引理 3.9。该卷定理 3.10 已有非有效严格间隙与定性稳定性；本文不把它们改称新增结论。坐标与停止接口来自其引理 2.1–2.2，倾斜实际严格上界来自其定理 7.1。

相对于该既有卷，新增的实质是：以明确的分拆余量、同一实际分支分数、非交换压缩的迹亏损、主角校正及保留全部旗标的 Kraus 残差，得到整个 $\mathcal C$ 上的有效四次根模量；再将该模量与同一通道的两个测试组合，给出 $\Delta=g^4/(2^{27}N^2)>2^{-58}$。所供定量符号论证提供了这一推导路线，本文将其组织为完整条件定理与证明。支撑值仍恰为 $65/N^2$，没有被改小；提升发生于支撑亏损与相干约束的联合使用。

Cauchy–Schwarz、正平方根迹微分、本征值极小极大原理、主角与正交基分解、Choi 正性、Carathéodory 定理、迹范数对偶、凸凹性及有限维紧性均是标准工具。本文的综合不自动取得外部新颖性或优先权，未核验未提供的外部来源，也不以普通符号证明冒充形式核验。

**定义 8.2（仍为 OPEN 的目标）。** 原任务始终是全 $M_5$ 输入、保留经典旗标及五维量子输出、采用任意未读取有限参考的完整菱形距离问题。精确 $d_\star$、匹配的全局最优实际策略、有限深度取到、几乎必然终止取到、实际闭包的完整刻画、$\mathcal C$ 上完整距离及联合证书的精确极小值、最佳稳定指数与常数、尖锐有效间隙，以及所引倾斜族的最佳参数和全局最优性均为 OPEN。已知的精确支撑最大值及其面不属于这些未决优化值。

本文没有把两个测试的最大值等同于完整菱形距离，没有声称 $\Delta$ 为最优间隙，没有用某个松弛可行点替代实际策略。所有首次结果、两个旗标与全部概率质量始终保留；$S$ 上的精确输出反例由同一个合法公平中点给出。有限维紧性只证明闭包的抽象极小者存在，不把它变成有限或几乎必然停止实现。

**约定 8.3（条件数学与资源边界）。** 结论以所定义的理想精确操作菜单与所供来源为条件，证据层级为可出错的、未执行的符号数学，不是 Lean/kernel 证书。参考纯化、主角分析、CP 松弛、Kraus 环境、复测试的额外参考及范数证明中的偏迹均是分析工具，不扩张实际菜单。本文未给出有限精度、校准、控制取得、物理实现或总成本界，也没有经验机器学习结论、普遍机器学习定理、外部优先权或更大全局目标已经完成的主张。

## 追加锚（本行以下为增补区）
