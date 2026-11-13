# 精确三重二次乘积与实际十四次域正纤维的高阶闭合

## 174. 原族中的全部高阶幂与完整纤维余切约化

**定理 174.1（每个预固定实际正纤维的高阶闭合）。** 设 $F$ 为任意特征零域，$D/F$ 为实际可分**域**扩张，$[D:F]=14$。任取本原元 $\theta$，固定非零体积形式，使用原七个连续幂窗口

$$
C=\langle1,\theta,\ldots,\theta^6\rangle_F
$$

及同一个 $D$ 的乘法所给的全部原带符号、带嵌入标签系数。令 $S$ 为该原系数像在 $[P_C]$ 处的局部环，$B$ 为其正规化在唯一上方点的局部环，$\mathscr T=\widehat S$、$\mathscr B=\widehat B$。采用 042，定义 134.1 的任意一组**预先固定**的合法原 $F$ 正枢轴 $s=(s_1,\ldots,s_{21})\subset\mathfrak m_S$，并定义

$$
B_{0,s}=\mathscr B/(s)\mathscr B\simeq F[[Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y},
\qquad
\pi_s:\mathscr T\longrightarrow B_{0,s},
$$

$$
A_s=\operatorname{im}\pi_s=\mathscr T/\ker\pi_s,
\qquad \mathfrak m=\mathfrak m_{A_s},\quad
\mathfrak n=\mathfrak m_{B_{0,s}},\quad \mathfrak q=(Y)\subset F[[Y]].
\tag{174.1}
$$

此处不假设 $A_s=\mathscr T/(s)\mathscr T$。令 $V=F[T]_{\le5}$，按 042，(133.8)--(133.9) 识别负线性坐标空间 $W=\bigwedge^2V$，并置

$$
H_d=\operatorname{Sym}^dW,\qquad
K=\ker\left(H_2\xrightarrow{\wedge}\bigwedge^4V\right),
\qquad
K^r=\operatorname{im}\left(\operatorname{Sym}^rK\xrightarrow{\mathrm{mult}}H_{2r}\right).
\tag{174.2}
$$

$K^r$ 始终是恰好 $r$ 个 $K$ 元素的乘积的 $F$ 线性张成。则 $\dim_FK=105$，且对所有整数 $r\ge3$，有实际代数理想的等式

$$
\boxed{
\pi_s(\mathfrak m_{\mathscr T}^{r})
=\mathfrak m^r=\mathfrak n^r
=B_{0,s}\cap\mathfrak q^{2r}.
}
\tag{174.3}
$$

定义实际四次符号空间

$$
J_4(A_s)=\operatorname{im}\left(
A_s\cap\mathfrak q^4\xrightarrow{\operatorname{in}_4}
\mathfrak q^4/\mathfrak q^6\right)\subseteq H_4.
\tag{174.4}
$$

它只使用实际像中常数项和二次项均为零的元素，不收集任意二次提升的裸四次尾项。存在典范的 $F$ 向量空间短正合列

$$
\boxed{
0\longrightarrow J_4(A_s)/K^2
\longrightarrow\mathfrak m/\mathfrak m^2
\xrightarrow{\operatorname{in}_2}K\longrightarrow0.
}
\tag{174.5}
$$

对 045，(168.1) 的检测器 $\Psi:H_4\to\bigwedge^6V\otimes W$，还成立

$$
J_4(A_s)/K^2\simeq\Psi(J_4(A_s))\subseteq\bigwedge^6V\otimes W,
$$

$$
\operatorname{edim}A_s=105+\dim_F\Psi(J_4(A_s)),
\qquad \boxed{111\le\operatorname{edim}A_s\le120.}
\tag{174.6}
$$

这些量词保持同一个 $D$、$\theta$、原系数源以及已固定的 $s$。本定理是普通数学的 PAPER 陈述与证明，使用下文列明的既有 PAPER 输入；不宣称 Lean kernel 核验。

证明。§175 给原源、局部性和全部二次像的精确接口；§176 由两个实际乘积恒等式证明 $K^3=H_6$ 及全部更高精确幂；§177 将逐次修正在原 $\widehat S$ 中求和，证明 (174.3) 的代数理想成员资格；§178 取二次、四次符号，证明 (174.5)--(174.6)。这些证明均不把实际像换成初始代数 $F[K]$。证毕。

## 175. 同一个原系数源、完成模型与全部二次像

**定义 175.1（带原标签的系数局部环）。** 对实际七维窗口 $C'\subset D$ 的包含帧 $E_{C'}$，令

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{175.1}
$$

$M_x$ 是同一个 $D$ 中的乘法。换帧及换体积只产生公共非零标量，所以使用射影系数像。在有限 Galois 分裂域中暂将原嵌入标签排序，则

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{175.2}
$$

$p_I$ 是实际帧的行子式，$\epsilon_I$ 是互补行序符号，$\alpha$ 来自 $\nu$。令 $U$ 为全部 $p_I\ne0$ 的统一开集。原七幂窗口属于 $U$，因为其最大行子式是非零 Vandermonde 行列式。使用 039，定义 111.1、命题 111.2 的原系数像环 $S_F$、实际乘法商

$$
X_D=U/\bigl((\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m\bigr)
$$

及其 Gale 对合 $\iota$。$S_F$ 的分裂扩底是原带标签比值 $(c_I/c_{I_0})^{\pm1}$ 的像代数。$S=(S_F)_{[P_C]}$ 是这个像的局部环；单个分裂标签函数不被自动视为原 $F$ 函数。

**约定 175.2（局部性、有限性与完成的依据）。** 039，(111.10)--(111.11)、定理 112.1、113.1 给 $S_F$ 有限型、Noetherian，且 $B_F=\mathcal O(X_D)^\iota$ 是其有限正规化；定理 115.1、117.1 和 042，定义 132.2 给本实际固定点的唯一上方点及两边剩余域 $F$。故 $S$ 为 Noetherian 局部 $F$ 代数，$B=(B_F)_y$ 对 $S$ 有限且局部：在 $S$ 处局部化的有限代数只有这一个极大理想。$B/\mathfrak m_SB$ 为有限维局部 $F$ 代数，其极大理想幂零，故对某个 $h$ 有 $\mathfrak m_B^h\subseteq\mathfrak m_SB\subseteq\mathfrak m_B$，两种完成拓扑共尾。有限模完成的正合性与张量公式因此给 $\mathscr T\hookrightarrow\mathscr B=B\otimes_S\mathscr T$，且 $\mathscr B$ 对 $\mathscr T$ 有限；可用 Stacks Project，Lemma 10.97.1，Tag 00MA。$\mathscr T$ 是完备分离的 Noetherian 局部环，剩余域为 $F$。$B_{0,s}$ 是有限 $\mathscr T$ 模的商，作用经 $A_s$ 分解，故亦对 $A_s$ 有限。$A_s$ 是 $\mathscr T$ 的局部商，Noetherian 且完备，剩余域为 $F$。这些是可用的有限正规化依据；§177 的提升证明只用完备源、连续性、分离目标和精确齐次幂，不附加关于 $A_s\subset B_{0,s}$ 的 Artin--Rees 假设或理想闭性假设。

**定义 175.3（实际负坐标与正枢轴）。** 在 042，§133 的实际对合相容横截面中，

$$
\mathscr B=F[[U_1,\ldots,U_{21},Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y}.
\tag{175.3}
$$

令 $e_i=T^i\in V$，$0\le i\le5$；采用固定识别

$$
e_i\wedge e_j\longleftrightarrow
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}).
\tag{175.4}
$$

这里 $Y$ 表示双曲图中对称矩阵模实际 Hankel 轨道方向的补空间，故 $W$ 是其线性坐标空间，而非任意另造矩阵的坐标。设正切空间为 $P_+$，令

$$
J:\mathfrak m_S/\mathfrak m_S^2\longrightarrow
\mathfrak m_B/\mathfrak m_B^2=P_+^\vee\oplus H_2,
\qquad M=\operatorname{im}J.
$$

040，定理 122.1 的 (122.8)、命题 122.2 给原 $F$ 上的耦合像

$$
\operatorname{pr}_{P_+^\vee}M=P_+^\vee,
\qquad M\cap(0\oplus H_2)=0\oplus K.
\tag{175.5}
$$

合法原 $F$ 正枢轴恰为 $s_i\in\mathfrak m_S$，使 $J[s_i]=(\ell_i,q_i)$ 中的 $\ell_i$ 构成 $P_+^\vee$ 的一组基；“正”表示对合的正特征空间，不要求 $F$ 有序。令 $L(U)=(\ell_i(U))_i$、$q_s=(q_i)_i$。042，定义 134.1 的实际消元给

$$
U=\phi_s(Y),\qquad \phi_s(-Y)=\phi_s(Y),\qquad
\phi_s=O(Y^2),\quad (\phi_s)_2=-L^{-1}q_s.
\tag{175.6}
$$

这来自等变形式可逆换元 $(U,Y)\mapsto(s,Y)$；所以 (174.1) 的 $B_{0,s}$ 是真实方程的商，不是将原 $U$ 直接置零。$A_s=\mathscr T/\mathfrak L_s$ 仍取实际核 $\mathfrak L_s=\ker\pi_s$，只知 $(s)\mathscr T\subseteq\mathfrak L_s$。

**引理 175.4（全部二次符号与原源中的共同提升）。** 对每个合法 $s$，有

$$
\operatorname{in}_2(\mathfrak m)=K,\qquad\dim_FK=105.
\tag{175.7}
$$

可以在原 $\mathfrak m_S$ 中一次选定 $\gamma_1,\ldots,\gamma_{105}$，以及 $K$ 的一组 $F$ 基 $k_1,\ldots,k_{105}$，使

$$
J[\gamma_i]=(0,k_i),\qquad
g_i:=\pi_s(\gamma_i)=k_i+O(Y^4)
\quad\text{对每组合法 }s.
\tag{175.8}
$$

证明。这是 042，引理 134.2 和 045，引理 170.1 的原族接口。为明确其范围，若源余切类为 $(\ell,q)\in M$，则实际纤维二次符号恰为

$$
R_s(\ell,q)=q-\ell L^{-1}q_s.
\tag{175.9}
$$

枢轴类张成的 $H_s$ 满足 $M=H_s\oplus(0\oplus K)$；$R_s$ 在前项为零，在后项为恒等。正规化极大理想平方限制到纤维后至少四阶，源完成不改变有限维余切空间，故该计算给**全部**实际二次像。由 (175.5)，每个 $(0,k_i)$ 都有原 $\mathfrak m_S$ 中的代表，且 (175.9) 对它的值不随 $s$ 改变。这就是共同提升。最后 $\dim W=15$，$H_2\to\bigwedge^4V$ 满射，因为每个基四向量可写成两个基二向量的外积；因此 $\dim K=\dim H_2-\dim\bigwedge^4V=120-15=105$。证毕。

**引理 175.5（实际局部像与目标滤过）。** $\pi_s$ 保持常数，且

$$
\mathfrak m=\pi_s(\mathfrak m_{\mathscr T})=A_s\cap\mathfrak n,
\qquad
\mathfrak n^r=B_{0,s}\cap\mathfrak q^{2r}\quad(r\ge1).
\tag{175.10}
$$

映射 $\pi_s$ 对源极大理想拓扑和目标 $\mathfrak n$ 拓扑连续，目标对该拓扑完备分离。

证明。$A_s$ 含 $F$。若一个实际像元素的常数项非零，则其源代表也有非零剩余类，故在 $\mathscr T$ 中可逆，其逆的像仍在 $A_s$；零常数元素在 $B_{0,s}$ 中不可能可逆。这直接给局部性、剩余域 $F$ 及第一个等式。

偶形式级数的极大理想由有限多个二次单项式 $Y_iY_j$ 生成。一个总次数至少 $2r$ 的偶单项式可取一个次数 $2r$ 的单项式因子，它是 $r$ 个二次单项式之积。为全部这样的有限多个因子固定一个次序，将每项分配给第一个可除它的因子。于是任意偶级数的全部单项式分成有限组；每组除去该因子后仍为偶形式级数。这给一个有限代数理想和，证明第二式的反向包含；正向包含由阶数相加得到。故 $\mathfrak n$ 拓扑与偶级数的 $Y$ 阶数拓扑相同，完备且分离。局部性给 $\pi_s(\mathfrak m_{\mathscr T}^j)\subseteq\mathfrak n^j$，从而连续。证毕。

## 176. 两个实际乘积恒等式、交错消元与精确齐次幂

**引理 176.1（两个有确定因子数的恒等式）。** 暂取 $V$ 的任意有序基 $v_1,\ldots,v_6$，记 $z_{ij}=v_i\wedge v_j\in W$。这是本节的基记号，不改动 (175.4) 的原坐标识别。置

$$
a=z_{12},\quad b=z_{34},\quad c=z_{56},\quad
x=z_{13},\quad y=z_{24},\quad u=z_{15},\quad v=z_{26},
$$

$$
q=ab+xy,\qquad t=ac+uv.
\tag{176.1}
$$

在 $\operatorname{Sym}(W)$ 中，

$$
a^3b=(a^2)q-(ax)(ay)\in K^2,
\tag{176.2}
$$

$$
\boxed{
a^4bc=(a^2)qt-(au)(av)q-(ax)(ay)t+(a^2)(xu)(yv)\in K^3.
}
\tag{176.3}
$$

每个括号和 $q,t$ 各是一个 $K$ 因子；这些式子不是乘以任意齐次余因子的理想归属。

证明。$a\wedge b=v_{1234}$、$x\wedge y=-v_{1234}$，故 $q\in K$；同样 $a\wedge c=v_{1256}$、$u\wedge v=-v_{1256}$，故 $t\in K$。两个基二向量若共享一个指标，其外积为零；因此 $a^2,ax,ay,au,av,xu,yv\in K$，其中 $xu$ 共用指标 $1$，$yv$ 共用指标 $2$。

右侧 (176.2) 展开为 $a^2(ab+xy)-a^2xy=a^3b$。在 (176.3) 中，前三项和最后一项分别展开为

$$
\begin{aligned}
a^2qt&=a^4bc+a^3buv+a^3cxy+a^2xyuv,\\
-(au)(av)q&=-a^3buv-a^2xyuv,\\
-(ax)(ay)t&=-a^3cxy-a^2xyuv,\\
+(a^2)(xu)(yv)&=+a^2xyuv.
\end{aligned}
$$

除 $a^4bc$ 外各项相消。第二式的每一项恰有三个 $K$ 因子，第一式恰有两个。将三个基向量对换位得到相同类型的式子。证毕。

**引理 176.2（任意二向量的原域交错正规形）。** 对任意 $w\in\bigwedge^2V$，存在 $V$ 的一组 $F$ 基及 $\lambda,\mu,\rho\in F$，使

$$
w=\lambda z_{12}+\mu z_{34}+\rho z_{56}.
\tag{176.4}
$$

证明。$w$ 在 $V^*$ 上定义交错双线性型 $\beta(\alpha,\delta)=(\alpha\wedge\delta)(w)$。若 $\beta=0$，则 $w=0$，任取基并取三个系数为零即可。否则取 $\alpha,\delta$ 使 $h=\beta(\alpha,\delta)\ne0$。对任意 $\eta\in V^*$，置

$$
\eta'=\eta+\frac{\beta(\delta,\eta)}h\alpha
-\frac{\beta(\alpha,\eta)}h\delta.
\tag{176.5}
$$

逐项代入得 $\beta(\alpha,\eta')=\beta(\delta,\eta')=0$。故分出非退化二维块 $\langle\alpha,\delta\rangle$，余下为其交错正交补；直和性由该二维块非退化保证。在补空间重复，六维至多三块，剩余根基补成一组基。取对偶基回到 $V$ 即得 (176.4)，允许某些系数为零。每一步只在原 $F$ 中作线性消元，不要求代数闭域、平方根或复数下降。证毕。

**定理 176.3（精确三重像及全部更高精确幂）。** 在每个特征零六维 $V$ 上，

$$
K^3=H_6,\qquad K^r=H_{2r}\quad(r\ge3).
\tag{176.6}
$$

证明。先证对每个 $w\in W$ 都有 $w^6\in K^3$。按引理 176.2，$w=\lambda a+\mu b+\rho c$。展开后的单项式形如 $a^ib^jc^k$，$i+j+k=6$；系数始终在 $F$ 中。若三个指数全偶，该项是三个平方的乘积，属于 $K^3$。否则总和为偶强制恰有两个奇指数。

若其中一个奇指数至少三，重命名三对后可设 $i\ge3$、$j\ge1$ 均奇，而 $k$ 偶。提取 $a^3b$，余下的指数 $i-3,j-1,k$ 全偶且和为二；余因子是一个属于 $K$ 的平方。引理 176.1 将所提因子写成两个 $K$ 因子的乘积之和，故整项恰在 $K^3$ 中。这也包括奇指数为三、三而第三指数为零的情形。

若两个奇指数都为一，第三个指数只能为四；换名后该项就是 $a^4bc$，由 (176.3) 得到恰有三个 $K$ 因子的表达式。以上穷尽 $w^6$ 中的奇偶情形，故 $w^6\in K^3$。换基不影响 $K$，因为外乘与线性同构交换。

特征零极化将纯六次幂推广到整个 $H_6$。对任意 $w_1,\ldots,w_6\in W$，在对称代数中有

$$
6!\,w_1\cdots w_6
=\sum_{I\subseteq\{1,\ldots,6\}}(-1)^{6-|I|}
\left(\sum_{i\in I}w_i\right)^6.
\tag{176.7}
$$

展开右侧时，一个未使用全部六个位置的项在包含其支撑的子集间交错相消；使用全部六个位置且总次数为六的项只有各用一次，系数为 $6!$。这个推导也允许 $w_i$ 相同。$6!$ 在 $F$ 中可逆，乘积 $w_1\cdots w_6$ 张成 $H_6$，所以 $H_6\subseteq K^3$；反向包含由次数得到。

最后，对每个 $d\ge2$，有

$$
K H_d=H_{d+2},
\tag{176.8}
$$

左侧指这两个齐次子空间的乘法像。一个基单项式有 $d+2\ge4$ 个基二向量因子，故至少八次指标出现，而可用指标只有六个。每个因子内部指标不同，所以必有两个不同因子共享指标，允许它们作为二向量相同。其乘积属于 $K$，余下恰有 $d$ 个因子，属于 $H_d$。单项式张成给反向包含，正向包含由次数。于是从 $K^3=H_6$ 出发，结合实际乘法像的结合律，

$$
K^{r+1}=K K^r=K H_{2r}=H_{2r+2}.
$$

这里每步恰增加一个 $K$ 因子；(176.8) 只在已知 $K^r=H_{2r}$ 后用于这个等式，不将一般理想分量误认成精确幂。证毕。

## 177. 原完成源中的无穷修正与代数理想幂

**引理 177.1（源内形式代入及有限分组）。** 设 $R$ 为完备分离局部 $F$ 代数，$\gamma_1,\ldots,\gamma_N\in\mathfrak m_R$。形式代入 $T_i\mapsto\gamma_i$ 给连续同态 $F[[T_1,\ldots,T_N]]\to R$。固定整数 $r\ge1$。若 $P_j(T)$ 为次数恰 $j$ 的齐次多项式，$j\ge r$，则

$$
P(T)=\sum_{j\ge r}P_j(T)
=\sum_{|\beta|=r}T^\beta H_\beta(T)
\tag{177.1}
$$

可写成右侧的有限和，$H_\beta\in F[[T]]$，从而

$$
P(\gamma)=\sum_{|\beta|=r}\gamma^\beta H_\beta(\gamma)
\in(\gamma_1,\ldots,\gamma_N)^r\subseteq\mathfrak m_R^r.
\tag{177.2}
$$

证明。$T$ 次数至少 $j$ 的多项式代入后在 $\mathfrak m_R^j$ 中。因此按次数截断的代入和为 Cauchy 系列，完备性给极限，分离性保证唯一；有限截断的加法、乘法恒等式经连续性保持，给出同态。对任意次数至少 $r$ 的单项式 $T^\alpha$，从有限多个 $|\beta|=r$ 且 $\beta\le\alpha$ 的因子中固定选择一个，按所选因子分组系数即得 (177.1)。每一组剩余项形成形式级数，组数有限。代入所得 (177.2) 是有限代数乘积和，不以任何理想的预先闭性为理由。证毕。

**定理 177.2（实际高阶理想幂的相等）。** 对定理 174.1 的每组固定 $s$，并令 $I=(g_1,\ldots,g_{105})A_s$，对所有 $r\ge3$ 有

$$
I^r=\mathfrak m^r=\mathfrak n^r=B_{0,s}\cap\mathfrak q^{2r}.
\tag{177.3}
$$

证明。固定 $r\ge3$ 和 $f\in B_{0,s}\cap\mathfrak q^{2r}$。逐次构造齐次多项式 $P_j(T_1,\ldots,T_{105})$，其 $T$ 次数恰为 $j$，$j\ge r$。若当前余项 $f_j$ 属于 $B_{0,s}\cap\mathfrak q^{2j}$，令 $h_j\in H_{2j}$ 为其 $2j$ 次齐次项。由定理 176.3，$K^j=H_{2j}$，可取

$$
P_j(k_1,\ldots,k_{105})=h_j.
\tag{177.4}
$$

这只是在满射 $\operatorname{Sym}^jK\twoheadrightarrow H_{2j}$ 下选择 $F$ 上的一个原像。由 $g_i=k_i+O(Y^4)$，在一个长为 $j$ 的乘积中将一个二次首项换为尾项会将 $Y$ 次数至少增加二。因此

$$
P_j(g)=h_j+O(Y^{2j+2}),\qquad
f_{j+1}=f_j-P_j(g)\in B_{0,s}\cap\mathfrak q^{2j+2}.
\tag{177.5}
$$

从 $f_r=f$ 开始，得到

$$
f-\sum_{j=r}^N P_j(g)\in\mathfrak n^{N+1}.
\tag{177.6}
$$

无穷和在**原完成源**中有真正见证。将引理 177.1 用于 $R=\mathscr T=\widehat S$ 和 (175.8) 的原 $\gamma_i$。每项 $P_j(\gamma)$ 的源阶数至少 $j$，所以

$$
Q=\left(\sum_{j\ge r}P_j\right)(\gamma)
\in(\gamma_1,\ldots,\gamma_{105})^r\subseteq\mathfrak m_{\mathscr T}^r.
\tag{177.7}
$$

由 (177.2)，此成员资格有有限和 $Q=\sum_{|\beta|=r}\gamma^\beta H_\beta(\gamma)$ 作为代数见证。连续性使 $\pi_s(Q)$ 等于 (177.6) 中有限部分和的极限，分离目标使该极限恰为 $f$。故 $f\in I^r$。反向 $I\subseteq\mathfrak m\subseteq\mathfrak n$ 给 $I^r\subseteq\mathfrak m^r\subseteq\mathfrak n^r$，而引理 175.5 已给 $\mathfrak n^r=B_{0,s}\cap\mathfrak q^{2r}$，因此全部相等。

由于 $\mathfrak m=\pi_s(\mathfrak m_{\mathscr T})$ 且 $\pi_s$ 满射到其实际像，有限代数乘积和还给 $\pi_s(\mathfrak m_{\mathscr T}^r)=\mathfrak m^r$。这证明 (174.3)。证明未在目标中取极限后直接宣称属于 $A_s$，而是先在原 $\mathscr T$ 中构造 $Q$；也未使用 $\mathfrak L_s=(s)\mathscr T$。证毕。

**推论 177.3（拓扑与固定完成局部导子）。** 对这个固定完成局部包含 $A_s\subset B_{0,s}$，诱导的 $\mathfrak n$ 拓扑与内在的 $\mathfrak m$ 拓扑相同。其导子

$$
\mathfrak c_s=\{b\in B_{0,s}:bB_{0,s}\subseteq A_s\}
$$

满足 $\mathfrak n^3\subseteq\mathfrak c_s$。

证明。对 $r\ge3$，$A_s\cap\mathfrak n^r=\mathfrak n^r=\mathfrak m^r$，故两组邻域从三次幂起逐项一致。又 $\mathfrak n^3\subseteq A_s$，且 $\mathfrak n^3$ 是 $B_{0,s}$ 的理想，所以 $b\in\mathfrak n^3$ 蕴含 $bB_{0,s}\subseteq\mathfrak n^3\subseteq A_s$。证毕。

这两项后果服务于 §§178--179 的有限阶约化：六阶目标尾项不仅已有原源见证，乘以任意目标级数后仍有实际像成员资格；比较余切或改变四次代表时可以安全丢掉这些尾项。导子仅为这个指定完成局部扩张中的包含，不计算导子等号、未完成局部导子或全局导子；拓扑一致是定理的后果，不是无穷修正的前提。

## 178. 精确余切短列、忠实检测与嵌入维数

**定理 178.1（没有六阶及更高纤维余切残差）。** 定义 $C_4=A_s\cap\mathfrak n^2=A_s\cap\mathfrak q^4$。则四次符号给

$$
C_4/\mathfrak n^3=J_4(A_s),\qquad
\mathfrak m^2/\mathfrak n^3=K^2\subseteq H_4,
\tag{178.1}
$$

并诱导 (174.5) 的典范短正合列。

证明。引理 175.4 给二次符号满射 $\mathfrak m\to K$，而 $\mathfrak m^2$ 中每个乘积至少四阶，所以它下降为 $\mathfrak m/\mathfrak m^2\twoheadrightarrow K$，核是 $C_4/\mathfrak m^2$。定理 177.2 给

$$
\mathfrak n^3=\mathfrak m^3\subseteq\mathfrak m^2\subseteq C_4.
\tag{178.2}
$$

四次符号在 $C_4$ 上的核恰为 $\mathfrak n^3$：偶性排除五次项，而每个六阶目标尾项已在 $A_s$ 中。其像按定义就是 $J_4(A_s)$。

再看 $\mathfrak m^2$。任意元素是有限个 $a_ib_i$ 之和，其中 $a_i,b_i\in\mathfrak m$。每个乘积的四次符号恰为 $\operatorname{in}_2(a_i)\operatorname{in}_2(b_i)$，故属于精确两重像 $K^2$。反过来，每个 $K$ 元素都有实际提升，因此任意有限个两重 $K$ 乘积之和都由真实 $\mathfrak m^2$ 元素的四次符号实现。结合公共核 (178.2)，得到第二个等式。于是

$$
\ker(\mathfrak m/\mathfrak m^2\to K)
=C_4/\mathfrak m^2
\simeq(C_4/\mathfrak n^3)/(\mathfrak m^2/\mathfrak n^3)
=J_4(A_s)/K^2.
\tag{178.3}
$$

具体地，一个实际四次符号的类送到任意实际零二次提升在 $\mathfrak m/\mathfrak m^2$ 中的类。两个这样的提升若四次符号相同，其差在 $\mathfrak n^3=\mathfrak m^3\subseteq\mathfrak m^2$；改变符号一个 $K^2$ 元素可由有限两重实际乘积相消，余差仍至少六阶。因此该注入不依赖选择。若一个实际零二次元素的四次符号在 $K^2$，同样相消后剩余六阶尾项已属 $\mathfrak m^2$，故其余切类为零。这也直接排除了漏掉高阶余切残差的可能。只断言典范短列，不断言典范分裂。证毕。

**推论 178.2（全部剩余余切方向均由四次检测读取）。** 定义

$$
\Psi(\xi_1\xi_2\xi_3\xi_4)
=\sum_{i=1}^4\left(\bigwedge_{j\ne i}\xi_j\right)\otimes\xi_i,
\qquad \xi_i\in W.
\tag{178.4}
$$

则 (174.6) 成立。

证明。045，定理 168.2 给所有特征零域上的 $\ker\Psi=K^2$，这里直接限制到 $J_4(A_s)$。由引理 175.4 的实际乘积提升，$K^2\subseteq J_4(A_s)$；因此限制检测器诱导同构 $J_4(A_s)/K^2\simeq\Psi(J_4(A_s))$。这不是只在一个评价子族上成立的检测结论，也不再留下检测器不可见而非乘积的四次余项。

当前 $\dim V=6$，所以 $\dim(\bigwedge^6V\otimes W)=15$。044，定理 157.1 的六个原函数对每个已固定 $s$ 均常数、二次项为零，四次检测值为六个线性独立张量，故

$$
6\le\dim_F\Psi(J_4(A_s))\le15.
$$

由 (174.5) 和 $\dim K=105$ 即得 (174.6)。六个方向在同一固定纤维中同时实现，没有合并不同枢轴下分别可达的值。证毕。

**注记 178.3（源余切与纤维余切的边界）。** 对次数十四，045，(172.4) 中的 $F^6Q_s$ 现在为零，因而其四次滤过商成为本卷短列的全部核。但 045，(172.1)--(172.3) 中的高阶**源**类仍是另一个问题：一个原 $g\in\mathfrak m_S$ 限制到纤维后至少六阶，只推出 $\pi_s(g)\in\mathfrak m^3$，不能推出 $g\in\mathfrak m_S^2$。源到纤维的商映射可以消去非零源余切类。本卷未计算完整源余切、完整评价源余切或其高阶关系；对更高次数 $[D:F]>14$ 也未证明 $K^3=H_6$ 或纤维尾闭合。

## 179. 有限实际源判据与固定纤维的准确剩余问题

**命题 179.1（一般实际四次像的有限源公式）。** 固定同一个 $s$。取原极大理想 $\mathfrak m_S$ 的任意有限理想生成元 $u_1,\ldots,u_N$，这些是完整原源的生成元，不只是 $K$ 的基提升。写其实际消元后的纤维展开为

$$
\pi_s(u_i)=d_i+e_i+O(Y^6),\qquad d_i\in K,\quad e_i\in H_4.
\tag{179.1}
$$

定义 $F$ 线性映射

$$
D_2:F^N\longrightarrow K,\quad D_2(\alpha)=\sum_i\alpha_i d_i,
\qquad
D_4:F^N\longrightarrow H_4,\quad D_4(\alpha)=\sum_i\alpha_i e_i.
$$

则 $D_2$ 满射，并且

$$
\boxed{J_4(A_s)=K^2+D_4(\ker D_2),}
\qquad
\Psi(J_4(A_s))=\Psi D_4(\ker D_2).
\tag{179.2}
$$

因此

$$
\operatorname{edim}A_s
=105+\operatorname{rank}_F\bigl((\Psi\circ D_4)|_{\ker D_2}\bigr).
\tag{179.3}
$$

证明。完成后 $u_i$ 仍生成 $\mathfrak m_{\mathscr T}$；这是有限模完成公式在 $\mathfrak m_S$ 上的应用。其像生成 $\mathfrak m$。任意源 $h\in\mathfrak m_{\mathscr T}$ 可写成有限和 $h=\sum_i u_i h_i$。令 $\alpha_i=h_i(0)\in F$，$h_i'=h_i-\alpha_i\in\mathfrak m_{\mathscr T}$。于是

$$
\pi_s(h)=\sum_i\alpha_i\pi_s(u_i)
+\sum_i\pi_s(u_i)\pi_s(h_i').
\tag{179.4}
$$

右侧第二项二次符号为零，故 $\operatorname{in}_2\pi_s(h)=D_2(\alpha)$；引理 175.4 保证 $D_2$ 满射。若 $\pi_s(h)$ 的二次符号为零，则 $\alpha\in\ker D_2$，而第二项的四次符号是 $\sum_i d_i\operatorname{in}_2\pi_s(h_i')\in K^2$。第一项四次符号为 $D_4(\alpha)$，得到正向包含。

反向，若 $\alpha\in\ker D_2$，原函数 $\sum_i\alpha_i u_i\in\mathfrak m_S$ 的实际二次项为零，四次符号就是 $D_4(\alpha)$；另外 $K^2$ 的全部元素都有实际两重乘积提升。因此两项都在 $J_4(A_s)$ 中。对等式应用 $\Psi$，再用 $\ker\Psi=K^2$ 和 (174.6)，得到其余公式。证毕。

这里的 $e_i$ 是代入**实际** $U=\phi_s(Y)$ 后的完整四次项，已经包含一般原函数中的 $U^2$、$UY^2$ 及正变量的二次、四次补偿。单个 $e_i$ 不必属于 $J_4(A_s)$；必须先满足 $D_2(\alpha)=0$。公式 (179.2) 将剩余问题化成有限实际源四次数据的线性像，没有提供这些数据的完整值，也不将任意选定的四次多项式当作原源元素。

**问题 179.2（预固定纤维的完整四次像，open）。** 对任意事先给定且不改变的合法原 $F$ 枢轴 $s$，确定

$$
E_s:=\Psi(J_4(A_s))=\Psi D_4(\ker D_2)
\subseteq\bigwedge^6V\otimes W.
\tag{179.5}
$$

令 $\Omega=e_0\wedge\cdots\wedge e_5$。044，(157.5) 的共同六维空间可写为

$$
\begin{aligned}
L_6=\langle\,&2z_{14}-z_{05}-z_{23},\quad 2z_{13}-z_{04},\quad
3z_{12}-z_{03},\quad 2z_{24}-z_{15},\quad
3z_{34}-z_{25},\quad z_{05}+z_{14}-8z_{23}\,\rangle_F.
\end{aligned}
\tag{179.6}
$$

这些向量依次是 044，(155.5)、(156.6) 的 $v_0,v_1,v_2,v_3,v_4,w$。已知 $\Omega\otimes L_6\subseteq E_s$。第一处未解的扩张是：对每个给定 $s$，找一个 $\alpha\in\ker D_2$ 使

$$
\Psi D_4(\alpha)\notin\Omega\otimes L_6,
\tag{179.7}
$$

等价地，找一个常数和实际二次项均为零的原函数，在这个同一纤维中的四次检测值超出该六维空间。更完整的问题是确定 $E_s$ 是否、以及何时达到十五维目标。检测器核已由 045 支付，故这里不再附加一个检测不可见四次商；由 (174.5)--(174.6)，精确 $E_s$ 就确定本纤维的嵌入维数。

044，定理 159.1 已把整个互素二元三次有理评价族的检测像限定为 $\Omega\otimes L_6$，所以 (179.7) 需要该族之外的实际原函数或原系数关系。044，定理 163.2 的任意检测目标需要改变枢轴，不能把它们拼成原固定 $s$ 的新方向。本卷不宣称对每个固定 $s$ 有第七方向或全十五方向，也不计算 $\mathfrak L_s$ 与 $(s)\mathscr T$ 是否相等。

## 180. 完整中文普通语言表述与解释

**定理 180.1（原十四次域中全部高阶纤维信息的归属）。** 在任意特征零域上，给定一个实际十四次可分域扩张，任选本原元，使用它从零次到六次的七个连续幂作为原窗口，保留同一个乘法行列式的全部原符号和原嵌入标签系数。对任意一组事先固定的合法原域正枢轴，把实际正规化里的正方向按这些真实系数方程消去，再取原完成系数局部环映入该纤维的实际像。这个实际像中极大理想的每一个三次及更高次幂，都恰好等于正规化纤维中相应的幂；换成负变量的普通次数说，就是所有从六次、八次、十次依次开始的偶级数，分别都是真正原源元素的三重、四重、五重乘积之有限和。

这个实际纤维的余切空间由两部分通过一个典范短正合列联系起来：可见的全部二次信息有一百零五维；其余部分恰是实际原源在常数和二次项都为零时产生的四次首项，模掉两个可见二次信息的乘积。没有另外隐藏的六次及更高余切残差。045 的忠实检测又把这个四次商无遗漏地读成一个至多十五维的外积张量像。044 已在每个同一固定纤维中提供六个独立实际方向，因此整个实际纤维的嵌入维数介于一百一十一与一百二十之间。

证明与解释。二次信息的“两块相乘”和“三块相乘”有实质区别：两块不能填满四次空间，但三块已经填满六次空间。将任意二向量在原域中化为至多三对交错标准块，六次展开中的全偶指数项都是平方的乘积；有两个奇指数时，两个明确恒等式分别处理三加一和四加一加一的障碍。极化从所有纯六次幂得到整个六次空间。此后任意至少四个基二向量因子中，六个指标必有重复，共用指标的两因子已经是一块合法二次信息，所以可以逐步增加恰好一块，覆盖所有更高偶次空间。

实际二次提升带有高阶尾巴，不能把齐次结论直接当成完整级数结论。先用恰好三块原提升消去六次项，误差从八次开始；再用四块消去八次项，依次继续。第 $j$ 次修正不只在目标里有高阶数，它在原完成源里也至少属于第 $j$ 次极大理想幂，因此修正和能在原源中收敛。把形式和按有限多个固定长度单项式因子分组，还给出了真正的代数理想幂表达式。连续性与目标分离性保证其像就是所需目标级数，故不需要假定“目标里的极限自然还来自原源”。

取余切就是模掉两个零常数实际元素的乘积。全部六次及更高尾项已是三重乘积，所以在这里消失；四次层的两重乘积首项又恰为两个实际二次符号的乘积。于是剩余部分精确集中在真实的零二次四次首项上，而不是任意二次提升带着的四次尾巴。忠实检测将这个商变成有限的张量像，有限原源公式 (179.2) 则写明要计算哪些真实系数取消关系。

尚未确定的是：每个预固定纤维中，六个已知方向之外还有哪些实际四次方向。改变正枢轴得到的其他纤维不能为原固定纤维补方向。一个函数在纤维中成为高阶乘积，也不表示它在完整原系数源中已是乘积；因此完整源余切及高阶源类仍未计算。上述全部结论只针对指定十四次域的实际完成正纤维，不给完整形式芽分类、全局导子、算术可判定性、H10 或物理结论。证毕。

## 181. 精确文献对应、有限重叠与结论范围

**约定 181.1（钉版原族输入）。** 以下既有结果仅按所列范围作为接受的 PAPER 输入；它们不因在本卷引用而成为 Lean 真值。

| 固定来源 | 本卷复用的精确内容 |
| --- | --- |
| [039，e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，定义 111.1、命题 111.2、定理 112.1、113.1、115.1、117.1](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | 原带符号标签系数像、实际乘法商、有限正规化、实际剩余域、固定点及横截面的形式模型。 |
| [040，f32f2d3b8219fae2014e5db4ab3c31575edf0672，定理 122.1 的 (122.8)、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | 原域完整耦合余切像及其纯负部分 $K$；不是原源嵌入维数的等式。 |
| [042，fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，定义 132.1--132.2、§133、定义 134.1、引理 134.2](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | 实际 $A_s=\operatorname{im}(\widehat S\to B_{0,s})$、实际消元及全部二次像 $K$，保留每组合法原域枢轴量词。 |
| [044，74b08723d9c5fb45657df8015bfd47a366f7b199，定理 157.1、159.1、163.2 及问题 165.3](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 每个固定纤维的共同六方向、整个互素有理三次族的六维检测上限、改变枢轴的量词边界和固定纤维缺口。 |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，定理 168.2、引理 170.1 及 §172](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 通用忠实检测 $\ker\Psi=K^2$、同一原源的共同纯负基提升，以及须区分的高阶源类与纤维滤过商。 |

**注记 181.2（经典 apolar 理想与精确幂的区别）。** 取 $0\ne\omega^*\in(\bigwedge^6V)^*$，在 $W$ 上定义 Pfaffian 三次型

$$
p(w)=\frac16\omega^*(w\wedge w\wedge w).
$$

用 $\operatorname{Sym}(W)$ 作 $W$ 上的常系数方向微分算子，则对 $q\in H_2$，

$$
(D_qp)(w)=\omega^*((\wedge q)\wedge w).
\tag{181.1}
$$

由于 $\bigwedge^4V$ 与 $\bigwedge^2V$ 的外乘配对非退化，$\operatorname{Ann}(p)_2=K$。这明确了本卷二次空间与泛六阶斜矩阵 Pfaffian 的对应，而不是仅凭同一个名称识别它们。Masoumeh Sepideh Shafiei，[*Apolarity for determinants and permanents of generic matrices*，arXiv:1212.0515v2，Lemma 4.6、Lemma 4.7、Theorem 4.11](https://arxiv.org/html/1212.0515v2#S4.Thmthm11)，分别描述四阶 Pfaffian 空间的二次消去空间、将其接到大 Pfaffian 的导数空间，并证明泛偶阶斜矩阵 Pfaffian 的 apolar ideal 由二次式生成。这些是 `literature-attested` 的精确对应；其理想生成结论在 $2r$ 次给 $K H_{2r-2}$，不是 $K^r$。特别地，$K H_2=H_4$ 不推出 $K^2=H_4$。本卷的两个实际乘积恒等式专门支付精确因子数，原族提升还须另用原完成源。

**注记 181.3（经典实际乘法规则的重叠）。** Thomas J. Enright、Nolan R. Wallach，[*A Pieri rule for Hermitian symmetric pairs II*，Pacific Journal of Mathematics 216(1)，51--61，Theorem 1，p.53，式 (2.1)，及 §3 的 Case 2，p.59](https://msp.org/pjm/2004/216-1/pjm-v216-n1-p03-s.pdf)，DOI [10.2140/pjm.2004.216.51](https://doi.org/10.2140/pjm.2004.216.51)，给的是 $S(\mathfrak p^-)$ 中**实际乘法像**的 Pieri 等式，不只是张量积中允许出现的分量。其 Case 2 是 $SO^*(2n)$、复化紧群 $GL_n$ 的斜矩阵情形；取 $n=6$，配对分拆记号中的 $[2,0,0]$ 对应最高权 $(2,2,0,0,0,0)$ 的二次空间，即这里的 $K$（按原文对偶约定转到 $\operatorname{Sym}(\bigwedge^2V)$）。因此抽象精确乘积问题有经典实际乘法理论的直接覆盖，不主张 $K^3=H_6$ 为全球新结果。本卷不调用这条表示论路线：§176 在任意原 $F$ 上直接给实际乘积证明，既不需要表示分解，也不需要从 $\mathbb C$ 向 $\mathbb Q$ 下降。该文不涉及本卷的原域系数源、预固定枢轴或原源内的无穷修正。

**约定 181.4（完成工具与有限重叠）。** [Stacks Project，Lemma 10.97.1，Tag 00MA](https://stacks.math.columbia.edu/tag/00MA) 的有限模完成正合性及张量公式，仅用于 §175 说明已有有限正规化的完成依据。其一般证明使用 Artin--Rees；本卷 §177 的源内逐次提升不需再假设或证明一个 $A_s\subseteq B_{0,s}$ 的 Artin--Rees 比较式。

仓内对应范围限定为上述五个固定来源及固定版本 a5a20d82984bbb32282adccee504bbcd41fc7ac1 中 AURIC_R5_030--045 的精确乘积、apolar 与尾闭合相关文字。该有限范围中，039/040 支付正规化与耦合二次像，042 支付实际纤维与全二次桥，044 支付固定纤维六方向，045 支付忠实四次检测及共同源提升。本卷的 `repo-derived` 综合是：用精确齐次乘积在原完成源中实现全部六阶及以上尾项，得到实际理想幂相等、完整纤维余切短列及有限实际源四次像判据。此对应不声称穷尽仓库或文献，不将经典抽象乘法包装成新的原族源桥。

一般评价文献或 043 的参数若写 $d=m-4$，则 $\dim V=m-1=d+3$；这里固定 $[D:F]=14$、$m=7$，所以 $d=3$、$\dim V=6$。本卷嵌入维数上下界不用把 $d$ 当作 $\dim V$ 的任何数值代换。剩余结论严格限于 (179.5) 的未知实际像、完整源和评价源余切的未解边界；不宣称完整实际四次像、统一第七方向、源理想等式、完整形式芽或全局后果。

## 追加锚（本行以下为增补区）
