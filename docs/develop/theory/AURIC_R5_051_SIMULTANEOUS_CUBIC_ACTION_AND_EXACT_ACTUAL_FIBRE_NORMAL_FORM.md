# 同时三次坐标作用与实际十四次完成纤维的精确正规形

## 221. 原域、实际源与带行列式线的坐标作用

**定义 221.1（固定的原系数纤维）。** 令 $F$ 为任意特征零域，$D/F$ 为次数十四的实际可分域扩张。固定本原元 $\theta$、非零体积形式 $\nu:\det_FD\to F$ 和窗口

$$
C_{\mathrm{win}}=\langle1,\theta,\ldots,\theta^6\rangle_F.
\tag{221.1}
$$

对于同一个 $D$ 的七维窗口 $C'$，其包含帧为 $E_{C'}$，$M_x$ 表示 $D$ 中乘以 $x$ 的算子。原系数来自

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{221.2}
$$

在有限 Galois 分裂域中，保持原嵌入标签及次序，写成

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{221.3}
$$

$p_I$ 为实际帧的递增行子式，$\epsilon_I$ 为互补行序符号，$\alpha$ 来自 $\nu$。令 $S$ 为这个原带符号、带标签射影系数像在 $[P_{C_{\mathrm{win}}}]$ 处的原 $F$ 局部环，$\mathscr T=\widehat S$。分裂后单个标签函数不因此成为原 $F$ 函数。

沿用 046，§175 和 049，§202 的实际正规化及对合相容横截面：

$$
\mathscr B=F[[U_1,\ldots,U_{21},Y_1,\ldots,Y_{15}]]^{Y\mapsto-Y}.
\tag{221.4}
$$

这里的实际负线性坐标采用原域识别

$$
V=F[T]_{\le5},\quad e_i=T^i,\quad W=\bigwedge^2V,
\qquad
e_i\wedge e_j\longleftrightarrow
Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}).
\tag{221.5}
$$

任意一组合法原 $F$ 正枢轴 $s=(s_1,\ldots,s_{21})\subset\mathfrak m_S$ 在以下论证之前已经固定。合法指其原余切像的正分量构成二十一维正余切空间的一组基；“正”是对合特征方向，不要求 $F$ 有序。真实枢轴方程消去正变量，给出 $U=\phi_s(Y)=O(Y^2)$。记

$$
B_s=\mathscr B/(s)\mathscr B\simeq R^{\sigma},
\qquad R=\widehat{\operatorname{Sym}}_F(W)=F[[z_1,\ldots,z_{15}]],
\qquad \sigma(z_p)=-z_p,
$$

$$
\pi_s:\mathscr T\longrightarrow B_s,
\qquad A_s=\operatorname{im}\pi_s,
\qquad \mathfrak q=(z_1,\ldots,z_{15})\subset R,
\quad \mathfrak n=\mathfrak m_{B_s}.
\tag{221.6}
$$

$z_p$ 是 (221.5) 的十五个基坐标的简写。始终取这个实际像 $A_s$，不将其替换为 $\mathscr T/(s)\mathscr T$，也不直接将原 $U$ 置零。046，约定 175.2、引理 175.5 说明 $A_s$ 是剩余域为 $F$ 的完备 Noetherian 局部环，$\pi_s$ 保持常数，且

$$
\mathfrak n^r=B_s\cap\mathfrak q^{2r}.
\tag{221.7}
$$

**定义 221.2（对称幂、二次核与唯一四次检测器）。** 在抽象线性部分，只要求 $\dim_FV=6$，置

$$
L=\det(V)=\bigwedge^6V,\qquad W=\bigwedge^2V,
\qquad H_d=\operatorname{Sym}^dW,
$$

$$
\mu:H_2\longrightarrow\bigwedge^4V,\quad \mu(ab)=a\wedge b,
\qquad K=\ker\mu,
\qquad K^2=\operatorname{im}\bigl(\operatorname{Sym}^2K\to H_4\bigr).
\tag{221.8}
$$

$K^2$ 是恰好两个 $K$ 元素相乘的线性张成。$\mu$ 满射，因为每个基四向量都可拆成两个基二向量；故 $\dim K=120-15=105$。定义

$$
\Psi:H_4\longrightarrow L\otimes W,
\qquad
\Psi(x_1x_2x_3x_4)=
\sum_{i=1}^4\left(\bigwedge_{j\ne i}x_j\right)\otimes x_i.
\tag{221.9}
$$

二向量的外乘交换，故此式为对称四线性式。所用检测接口是 045，定理 168.2 和 (169.4)：

$$
\ker\Psi=K^2,\qquad
\Psi\bigl(j_6(\Omega)x\bigr)=18\Omega\otimes x.
\tag{221.10}
$$

其中 $\Omega\in L$，$x\in W$，$j_6:L\to H_3$ 为 045 的归一化交替映射，即

$$
j_6(v_1\wedge\cdots\wedge v_6)
=\frac1{48}\sum_{\gamma\in\mathfrak S_6}\operatorname{sgn}(\gamma)
\prod_{a=1}^3(v_{\gamma(2a-1)}\wedge v_{\gamma(2a)}).
\tag{221.11}
$$

特别地，$\Psi$ 满射。对任意 $F$ 子空间 $E\subseteq W$，定义

$$
J_E=\Psi^{-1}(L\otimes E),
\qquad
\overline\Psi_E:H_4/J_E\xrightarrow{\sim}L\otimes(W/E).
\tag{221.12}
$$

$L$ 始终是一维向量空间；此商同构不需要选定 $L\simeq F$。同样，$W$ 是 $R$ 的线性生成元空间，其对偶为 $W^\vee$，两者没有被识别。下文 $\operatorname{Sym}^d(W^\vee)$ 是辅助向量 $x\in W$ 上的多项式函数空间。

**定义 221.3（整个二次空间上的同时三次作用）。** 取 $W$ 的基 $z_1,\ldots,z_{15}$ 及其对偶基 $\alpha_1,\ldots,\alpha_{15}$。对 $\alpha\in W^\vee$，$\iota_\alpha$ 是 $\operatorname{Sym}(W)$ 上由 $\iota_\alpha(z)=\alpha(z)$ 决定的导子。例如

$$
\iota_\alpha(uv)=\alpha(u)v+\alpha(v)u.
\tag{221.13}
$$

一个元组 $f=(f_p)_{p=1}^{15}\in(H_3)^{15}$ 内在地表示映射 $W\to H_3$，$z_p\mapsto f_p$。置

$$
\delta_f=\sum_{p=1}^{15}f_p\iota_{\alpha_p},
\qquad
G:(H_3)^{15}\longrightarrow\operatorname{Hom}_F(H_2,L\otimes W),
\quad G(f)(q)=\Psi(\delta_fq),
$$

$$
D_E:(H_3)^{15}\longrightarrow\operatorname{Hom}_F(K,H_4/J_E),
\qquad D_E(f)(k)=\delta_fk+J_E.
\tag{221.14}
$$

这些是同一个齐次三次导子在全体二次式上的作用，而非对不同 $k$ 分别选择的操作。

## 222. 同时作用满射与全部对偶障碍的消失

**定理 222.1（任意原域上的同时三次作用）。** 对任意特征零域 $F$ 和任意六维 $F$ 空间 $V$，(221.14) 的 $G$ 满射，且

$$
\ker G^\vee=0.
\tag{222.1}
$$

因此对每个 $F$ 子空间 $E\subseteq W$，包括 $E=0,W$，$D_E$ 满射并满足

$$
\ker D_E^\vee=0.
\tag{222.2}
$$

也就是说，给定任意 $\tau:K\to H_4/J_E$，存在原 $F$ 上的一组十五个齐次三次式 $f$，使 $D_E(f)(k)=\tau(k)$ 对全部 $k\in K$ 同时成立。

证明。以下在这一个定理的证明内建立所需的 Pfaffian Hessian、无穷小迹与对称延拓结论。Hessian 相对不变量方法的经典背景见 Fox，Theorem 1.5 及 §3 的 Pfaffian 例；导子伴随方法见 Jelisiejew，Proposition 2.10、Corollary 2.12、Proposition 2.18。这里逐一给出所需的原 $F$ 论证。

第一步，固定配对和伴随常数。暂选 $0\ne\eta\in L^\vee$，定义三次多项式

$$
P(x)=\frac16\eta(x\wedge x\wedge x),\qquad x\in W.
\tag{222.3}
$$

对 $h=v_1\cdots v_d\in H_d$ 和 $Q\in\operatorname{Sym}^d(W^\vee)$，用归一化完美配对

$$
\langle h,Q\rangle_d=\frac1{d!}D_{v_1}\cdots D_{v_d}Q.
\tag{222.4}
$$

在对偶单项式基上非零对角系数为 $\mathbf a!/d!$，故特征零保证配对完美，且 $\langle x^d,Q\rangle_d=Q(x)$。乘以 $v:H_3\to H_4$ 的伴随恰为 $D_v/4$。由

$$
\Psi(x^4)=4(x\wedge x\wedge x)\otimes x
$$

得到

$$
\Psi^\vee(\eta\otimes\ell)=24P\ell,
\qquad \ell\in W^\vee.
\tag{222.5}
$$

从对角到整个对称幂所用的极化可直接写为

$$
d!\,v_1\cdots v_d
=\sum_{I\subseteq\{1,\ldots,d\}}(-1)^{d-|I|}
\left(\sum_{i\in I}v_i\right)^d.
\tag{222.6}
$$

展开右侧，缺少某个指标的项由包含排除抵消；每个指标都出现的次数 $d$ 项恰为 $d!v_1\cdots v_d$。因此 (222.5) 是完整伴随公式。

第二步，在原域证明 Hessian 恒等式。令

$$
A_x(u,v)=d^2P_x(u,v)=\eta(x\wedge u\wedge v).
\tag{222.7}
$$

固定 $W$ 的一组基，记其矩阵行列式为 $h(x)=\det A_x$。我们将证明

$$
h(x)=cP(x)^5\quad\text{对某个 }c\in F^\times.
\tag{222.8}
$$

先取 $V$ 的一组基 $v_1,\ldots,v_6$，分为三个二平面 $U_1,U_2,U_3$，令

$$
a_1=v_1\wedge v_2,\quad a_2=v_3\wedge v_4,\quad
a_3=v_5\wedge v_6,\quad x_0=a_1+a_2+a_3,
\quad t=\eta(a_1\wedge a_2\wedge a_3)\ne0.
$$

有直和

$$
W=\langle a_1,a_2,a_3\rangle
\oplus(U_1\wedge U_2)\oplus(U_1\wedge U_3)\oplus(U_2\wedge U_3).
\tag{222.9}
$$

这四项对 $A_{x_0}$ 两两正交：不同混合项外乘后在某个二平面中的次数已超过二，或者再乘任一 $a_i$ 后超过二；面积项与混合项的外乘也如此。在前三维上，矩阵为

$$
t\begin{pmatrix}0&1&1\\1&0&1\\1&1&0\end{pmatrix},
$$

行列式为 $2t^3$。在每个 $U_i\wedge U_j$ 上，若该两平面按顺序的基为 $a,b$ 和 $c,d$，采用 $a\wedge c,a\wedge d,b\wedge c,b\wedge d$，矩阵为

$$
t\begin{pmatrix}
0&0&0&-1\\
0&0&1&0\\
0&1&0&0\\
-1&0&0&0
\end{pmatrix}.
\tag{222.10}
$$

这是将混合二向量的完美外乘配对再乘剩余面积向量所得，行列式为 $t^4$。所以 $A_{x_0}:W\to W^\vee$ 可逆；同时 $P(x_0)=t\ne0$。

现取 $g\in\operatorname{GL}(V)(F)$，记 $b=\bigwedge^2g$、$\chi=\det g$。外乘直接给出

$$
P(bx)=\chi P(x),\qquad
A_{bx}(bu,bv)=\chi A_x(u,v).
\tag{222.11}
$$

还有 $\det b=\chi^5$。确切地，在对角矩阵上，$\bigwedge^2g$ 的特征对角项为 $g_{ii}g_{jj}$，每个 $g_{ii}$ 出现五次。对于初等加行矩阵，可按被替换的两个指标重排基，使它和其外平方均为对角全一的三角矩阵，行列式都为一。域上的消元将任意可逆矩阵写成这些矩阵与对角矩阵的乘积；行交换也可由加行矩阵和对角矩阵组成。因此该行列式公式对所有原 $F$ 上的 $g$ 成立。对 (222.11) 的 Hessian 矩阵取行列式，得

$$
\det(b)^2h(bx)=\chi^{15}h(x),
\qquad h(bx)=\chi^5h(x).
\tag{222.12}
$$

为把这条协变性用于每个 $P(x)\ne0$ 的原域点，给出所需交错正规形。$x\in\bigwedge^2V$ 在 $V^\vee$ 上给交错配对 $\beta_x(\alpha,\beta)=(\alpha\wedge\beta)(x)$。若配对非零，选 $a,b$ 使 $\beta_x(a,b)=1$，只需把一个非零配对值除掉。对任意 $\gamma$，向量

$$
\gamma_0=\gamma-\beta_x(\gamma,b)a+\beta_x(\gamma,a)b
$$

与 $a,b$ 都正交。这将 $V^\vee$ 分为非退化二平面与其正交补；在补空间递归。在对偶的 $V$ 基中，$x$ 成为若干互不相交面积向量之和。$x^{\wedge3}\ne0$ 当且仅当有三个非零块。因此每个 $P(x)\ne0$ 的 $x$ 都是 $x=bx_0$，其中 $b=\bigwedge^2g$ 且 $g\in\operatorname{GL}(V)(F)$。此过程不要求平方根或扩域。

取 $c=h(x_0)/P(x_0)^5\in F^\times$，(222.11)--(222.12) 使 $Q=h-cP^5$ 在所有 $P(x)\ne0$ 的 $F$ 点为零。于是 $PQ$ 在每个 $F$ 点均为零。$F$ 无限；多元多项式在 $F$ 的所有点为零则恒为零，这可将其视为最后一个变量的多项式，用一元根数界及变量数归纳证明。故 $PQ=0$ 为多项式恒等式。多项式环为整环且 $P\ne0$，所以 $Q=0$。这证明 (222.8)，并支付了所用主开集的原域稠密性。

第三步，取得准确的无穷小迹条件。设任意 $H\in\operatorname{End}_F(W)$ 和 $\lambda\in F$ 满足

$$
dP_x(Hx)=\lambda P(x)
\tag{222.13}
$$

作为多项式恒等式。在 $F[\varepsilon]/(\varepsilon^2)$ 中令 $b=I+\varepsilon H$，则

$$
P(bx)=(1+\varepsilon\lambda)P(x).
$$

对 $x$ 求两次导数后取行列式，得到

$$
\det(b)^2h(bx)=(1+\varepsilon\lambda)^{15}h(x).
$$

将 (222.8) 代入，并用 $\det(I+\varepsilon H)=1+\varepsilon\operatorname{tr}_WH$，可比较 $\varepsilon$ 系数：

$$
2\operatorname{tr}_WH+5\lambda=15\lambda,
\qquad \boxed{\operatorname{tr}_WH=5\lambda.}
\tag{222.14}
$$

这里可消去非零多项式 $h$，等价地逐项比较其非零系数。此论证只用 (222.13)，无需保持者的完整分类。作为外平方表示的常数对应，若 $H=\rho(M)$，其中

$$
\rho(M)(u\wedge v)=Mu\wedge v+u\wedge Mv,
$$

则在 $\det V$ 上的作用给 $dP_x(\rho(M)x)=\operatorname{tr}_V(M)P(x)$，每个矩阵对角项在外平方中出现五次给 $\operatorname{tr}_W\rho(M)=5\operatorname{tr}_VM$。这与 (222.14) 的因子五一致；以下对一般 $H$ 直接使用 (222.14)。

第四步，写出并计算 $G$ 的全部伴随障碍。有限维对偶的典范识别为

$$
\operatorname{Hom}_F(H_2,L\otimes W)^\vee
=H_2\otimes L^\vee\otimes W^\vee.
$$

因此任意潜在障碍可写为 $T=\sum_aq_a\otimes\eta\otimes\ell_a$，其中 $q_a\in H_2$、$\ell_a\in W^\vee$。它在映射 $C$ 上的值为 $\sum_a(\eta\otimes\ell_a)(C(q_a))$。对 $\alpha\in W^\vee$ 定义线性算子

$$
H_\alpha:W\longrightarrow W,
\qquad H_\alpha x=\sum_a\ell_a(x)\iota_\alpha q_a.
\tag{222.15}
$$

由 (222.4)--(222.5)，$G^\vee T$ 的第 $p$ 个三次多项式分量恰为

$$
6\sum_aD_{\iota_{\alpha_p}q_a}(P\ell_a).
\tag{222.16}
$$

这个因子六来自 $24/4$。故 $T\in\ker G^\vee$ 当且仅当，对每个 $\alpha\in W^\vee$ 都有

$$
\sum_aD_{\iota_\alpha q_a}(P\ell_a)=0.
$$

展开，并用秩一算子 $v\otimes\ell:x\mapsto\ell(x)v$ 的迹为 $\ell(v)$，得到准确方程

$$
dP_x(H_\alpha x)+\operatorname{tr}_W(H_\alpha)P(x)=0.
\tag{222.17}
$$

在 (222.13) 中取 $\lambda_\alpha=-\operatorname{tr}_WH_\alpha$，(222.14) 给

$$
\operatorname{tr}_WH_\alpha=5\lambda_\alpha,
\qquad 6\lambda_\alpha=0.
$$

所以每个 $\alpha$ 都满足

$$
\operatorname{tr}_WH_\alpha=0,
\qquad dP_x(H_\alpha x)=0.
\tag{222.18}
$$

这个六来自迹方程，与 (222.16) 的伴随归一化六分别承担不同步骤。

第五步，消去所需的对称一阶延拓。对于普通转置 $H_\alpha^\vee:W^\vee\to W^\vee$，二次张量的对称性给

$$
\beta(\iota_\alpha q)=\alpha(\iota_\beta q),
\qquad
H_\alpha^\vee\beta=H_\beta^\vee\alpha.
\tag{222.19}
$$

后一个等式可在任意 $x\in W$ 上评价，再用 (222.15) 逐项核对。这是转置作用于协向量的等式；没有把 $H_\alpha$ 作用于 $W^\vee$，也没有引入带负号的逆变 Lie 作用。

固定 $x\in W$，令 $\xi=dP_x\in W^\vee$。由 (222.18)--(222.19)，对任意 $\beta\in W^\vee$ 有

$$
\beta(H_\xi x)=\xi(H_\beta x)=0,
\qquad\text{故 }H_\xi x=0.
\tag{222.20}
$$

将 $\xi$ 保持为这个固定协向量，对恒等式 $dP_y(H_\xi y)=0$ 在 $y=x$ 处沿 $v$ 微分：

$$
A_x(v,H_\xi x)+\xi(H_\xi v)=0.
$$

由 (222.20)，第一项为零，故 $H_\xi^\vee\xi=0$。因此二次多项式映射

$$
\mathcal B:W^\vee\longrightarrow W^\vee,
\qquad \mathcal B(\alpha)=H_\alpha^\vee\alpha
$$

满足

$$
\mathcal B(dP_x)=0\quad\text{作为 }x\text{ 的多项式恒等式}.
\tag{222.21}
$$

为从梯度像上消失推出 $\mathcal B=0$，在原域逐系数构造局部形式梯度逆。令 $\xi_0=dP_{x_0}$，

$$
\Gamma(u)=dP_{x_0+u}-\xi_0=A_{x_0}u+\Gamma_2(u),
\tag{222.22}
$$

其中 $\Gamma_2$ 齐次二次，$A_{x_0}:W\to W^\vee$ 已由 (222.9)--(222.10) 证明可逆。对独立形式变量向量 $y\in W^\vee$，构造 $u(y)=\sum_{r\ge1}u_r(y)$，每个 $u_r$ 齐次 $r$ 次。先取 $u_1=A_{x_0}^{-1}y$。若次数小于 $r$ 的项已使 $\Gamma(u_{<r})-y$ 从 $r$ 次开始，记其 $r$ 次项为 $R_r$，取

$$
u_r=-A_{x_0}^{-1}R_r.
\tag{222.23}
$$

因为 $\Gamma_2$ 没有常数、一次项，加入 $u_r$ 在 $r$ 次层的唯一贡献是 $A_{x_0}u_r$。这证明存在且逐次唯一的 $\Gamma(u(y))=y$。同样的递推给另一侧的逆；或将 $y=\Gamma(u)$ 代入，利用首次可能不同次数上 $A_{x_0}$ 的可逆性，得到 $u(\Gamma(u))=u$。所有系数都在 $F$ 中。

在 (222.21) 中代入 $x=x_0+u(y)$，有 $\mathcal B(\xi_0+y)=0$ 为形式恒等式。左侧本身是一个多项式，故每个系数为零；平移可逆，因而 $\mathcal B=0$。再极化并使用 (222.19)：

$$
0=\mathcal B(\alpha+\beta)-\mathcal B(\alpha)-\mathcal B(\beta)
=H_\alpha^\vee\beta+H_\beta^\vee\alpha
=2H_\alpha^\vee\beta.
\tag{222.24}
$$

所以所有 $H_\alpha$ 为零。这证明了本问题实际需要的一阶延拓消失：一个线性族若满足 (222.18) 的严格 Pfaffian 保持条件和 (222.19) 的转置对称条件，就只能是零族。

第六步，返回原障碍与任意商。对每个 $x\in W$，令 $Q_x=\sum_a\ell_a(x)q_a\in H_2$。所有 $\iota_\alpha Q_x=H_\alpha x$ 均为零，所以二次齐次张量 $Q_x$ 为零。例如在任意对偶基上，所有一次偏导都为零，特征零迫使每个二次系数为零。因此映射 $x\mapsto Q_x$ 为零；等价地 $\sum_aq_a\otimes\ell_a=0$，故 $T=0$。这计算出全部 $\ker G^\vee=0$，有限维线性对偶遂给出 $G$ 满射。

最后给定 $\tau:K\to H_4/J_E$，用 (221.12) 将其看作 $K\to L\otimes(W/E)$。在原 $F$ 上选线性截面，将值提升到 $L\otimes W$，再以基延拓将该映射从 $K$ 扩为 $H_2\to L\otimes W$。$G$ 的满射给一整个元组 $f$，限制及投影后正好是 $D_E(f)=\tau$。若记限制及投影为

$$
\mathcal R_E:\operatorname{Hom}(H_2,L\otimes W)
\twoheadrightarrow\operatorname{Hom}(K,H_4/J_E),
$$

则 $D_E=\mathcal R_EG$，$\mathcal R_E^\vee$ 单射。任何 $D_E$ 的对偶障碍经此单射进入刚算出的零空间 $\ker G^\vee$，故该障碍也恰为零。临时的 $\eta$ 只用于书写配对；定理、所有提升及所得元组均在原 $F$ 上，且结论保留 $L$ 的线类型。证毕。

## 223. 实际纯四次空间、代表无关的图与双向源见证

**定义 223.1（完整实际检测像及有限图接口）。** 返回定义 221.1 的一个固定实际纤维，$a_d$ 表示偶级数 $a$ 的普通次数 $d$ 齐次项。定义

$$
J=J_4(A_s)=\{a_4:a\in A_s,\ a_0=a_2=0\}\subseteq H_4,
\qquad T_s=\Psi(J)\subseteq L\otimes W,
$$

$$
E_s=\operatorname{im}\bigl(L^\vee\otimes T_s\to W\bigr),
\qquad T_s=L\otimes E_s.
\tag{223.1}
$$

最后一个等式因为 $L$ 是一条线而成立：用任意非零 $\eta\in L^\vee$ 暂时取像，换另一个 $\eta$ 只把像乘非零标量，不改变子空间。046、048、050 中的张量值记号 $E_s\subseteq L\otimes W$ 在这里记为 $T_s$；本文的 $E_s$ 是 $W$ 的子空间。

现在明确复用的实际源接口及其见证含义。045，引理 170.1、046，引理 175.4 给原 $F$ 线性提升 $u:K\to\mathfrak m_S$，且完整二次像为 $K$。046，定理 177.2 给

$$
\pi_s(\mathfrak m_{\mathscr T}^3)
=\mathfrak m_{A_s}^3=\mathfrak n^3=B_s\cap\mathfrak q^6.
\tag{223.2}
$$

所以对每个完整尾项 $h\in\mathfrak n^3$ 都存在 $Q_s(h)\in\mathfrak m_{\mathscr T}^3$，满足 $\pi_s(Q_s(h))=h$。不要求这些选择典范或线性。

实际二次提升的乘积给 $K^2\subseteq J$。若 $v\in H_4$ 的检测值在 $T_s$ 中，取 $j\in J$ 使 $\Psi(v)=\Psi(j)$，则 $v-j\in\ker\Psi=K^2\subseteq J$。反向包含由定义直接成立，因此复得 048，定理 193.1 的完整预像接口

$$
J=J_{E_s}=\Psi^{-1}(L\otimes E_s).
\tag{223.3}
$$

这里只用实际零二次元素定义 $J$；某个二次提升的四次尾项不必属于 $J$。

写 $\pi_s(u(k))=k+t_s(k)+h_s(k)$，其中 $t_s(k)\in H_4$、$h_s(k)\in\mathfrak n^3$。定义

$$
\tau_s:K\longrightarrow H_4/J_{E_s},
\qquad \tau_s(k)=t_s(k)+J_{E_s}.
\tag{223.4}
$$

两个实际零常数提升若二次项相同，它们的差是实际零二次元素，故四次差在 $J$。所以 (223.4) 允许任意实际提升，且不依赖代表选择；取线性 $u$ 即见 $\tau_s$ 为 $F$ 线性。它仍相对于固定覆盖坐标定义。

049，定理 203.2 已给精确实际图。为了将其用于坐标作用，写全两个方向所需的源见证。先对 $K$ 的一组基选 $h_s(k_i)$ 的 (223.2) 见证并减去，再线性延拓，得到 $\widetilde u:K\to\mathscr T$，使

$$
\pi_s(\widetilde u(k))=k+t_s(k).
\tag{223.5}
$$

另一方面，任意 $j\in J$ 按定义有 $v_j\in\mathscr T$ 使 $\pi_s(v_j)=j+h_j$，$h_j\in\mathfrak n^3$；于是 $\widetilde v_j=v_j-Q_s(h_j)$ 映到齐次多项式 $j$ 本身。因而不只是 $j$ 的符号，而是 $j\in A_s$。

对任意 $b=c+q_2+q_4+h$，$c\in F$、$q_d\in H_d$、$h\in\mathfrak n^3$，成员资格精确为

$$
b\in A_s\quad\Longleftrightarrow\quad
q_2\in K,\qquad q_4+J_{E_s}=\tau_s(q_2).
\tag{223.6}
$$

正向，若 $b=\pi_s(a)$，在源中减去 $c+\widetilde u(q_2)$。余像的常数、二次项都为零，故 $q_4-t_s(q_2)\in J$；余下部分属于 $\mathfrak n^3$。反向，若右侧成立，置 $j=q_4-t_s(q_2)\in J$，则一个精确源见证为

$$
b=\pi_s\bigl(c+\widetilde u(q_2)+\widetilde v_j+Q_s(h)\bigr).
\tag{223.7}
$$

这适用于任意指定的完整 $h$，没有只在目标里取闭包。因此，作为 $B_s$ 中的实际子集，

$$
A_s=F+\{k+t_s(k):k\in K\}+J_{E_s}+\mathfrak n^3.
\tag{223.8}
$$

把 $t_s$ 换成同一 $\tau_s$ 的任意线性代表，只改变一个 $J_{E_s}$ 值映射，不改变这个等式。这些是 049 的实际图及源见证在 (223.1) 的行列式线约定下的复用；它们本身尚未消去 $\tau_s$。

## 224. 一次奇三次代换与整个完成代数的等式

**定理 224.1（每个固定实际纤维的精确相对正规形）。** 对定义 221.1 的每个 $F,D,\theta$ 及每个事先固定的合法原 $F$ 枢轴 $s$，令 $E_s$ 为 (223.1) 的整个实际检测子空间。存在一组 $f_{s,p}\in H_3$，其系数在这个原 $F$ 中，使

$$
\varphi_s:R\longrightarrow R,
\qquad \varphi_s(z_p)=z_p+f_{s,p}
\tag{224.1}
$$

为连续奇形式自同构，限制为 $B_s$ 的自同构，并有

$$
\boxed{\quad
\varphi_s(A_s)=N_{E_s}:=F+K+J_{E_s}+\mathfrak n^3.
\quad}
\tag{224.2}
$$

此等式是整个完成子代数的等式。代换保持 $\mathfrak n^3$ 以及实际纯四次符号空间 $J_{E_s}$ 的符号，给出完备局部 $F$ 代数同构 $A_s\simeq N_{E_s}$。正向代换除一次项和三次项外没有更高项；其逆允许有更高奇次项。同一组十五个三次式同时处理该固定纤维内每个 $k\in K$。

证明。由定理 222.1 一次选择整个元组 $f_s$ 满足

$$
D_{E_s}(f_s)=-\tau_s.
\tag{224.3}
$$

先说明形式自同构。对一般向量形式映射 $F_0(z)=z+f_s(z)$，递推寻找逆 $g(w)=w+\sum_{r\ge2}g_r(w)$。若低于 $r$ 次的逆项已确定，$F_0(g(w))-w$ 的 $r$ 次项中，新未知项的系数恰是恒等算子；因为 $f_s$ 从三次开始，新项进入 $f_s(g)$ 只会影响更高次数。取 $g_r$ 为已有误差的负值便消去该层。此递推在 $F$ 中逐系数完成，形式完备性给 $F_0\circ g=\operatorname{id}$。同样的递推可构造左逆；结合左右逆的复合，二者相同。这给出 (224.1) 的连续环逆。

由于 $f_s$ 齐次三次，$F_0(-z)=-F_0(z)$，故 $\varphi_s$ 与 $\sigma$ 交换。逆也由唯一性与 $\sigma$ 交换，因而为奇映射。两者限制在 $R^\sigma=B_s$，并因线性项为恒等而保持每个 $\mathfrak q^r$。结合 (221.7)，得到准确尾项等式

$$
\varphi_s(\mathfrak n^3)=\mathfrak n^3.
\tag{224.4}
$$

对 $k\in H_2$，将两个一次因子代入 (224.1)，一次三次替换给 $\delta_{f_s}k$，两次替换从六次开始，所以

$$
\varphi_s(k)=k+\delta_{f_s}k\pmod{\mathfrak n^3}.
\tag{224.5}
$$

对任意 $v\in H_4$，一次替换已从六次开始，因此

$$
\varphi_s(v)=v\pmod{\mathfrak n^3}.
\tag{224.6}
$$

由 (224.3)，每个实际图元素 $k+t_s(k)$ 满足

$$
\delta_{f_s}k+t_s(k)\in J_{E_s},
\qquad
\varphi_s(k+t_s(k))-k\in J_{E_s}+\mathfrak n^3.
\tag{224.7}
$$

这里的负号由环代换 (224.1) 的定义决定。结合 (223.8)、(224.4)、(224.6)，先得

$$
\varphi_s(A_s)\subseteq F+K+J_{E_s}+\mathfrak n^3.
\tag{224.8}
$$

再证明反向包含。整个 $\mathfrak n^3\subseteq A_s$，所以 (224.4) 给 $\mathfrak n^3\subseteq\varphi_s(A_s)$。每个齐次 $j\in J_{E_s}$ 在 (223.5)--(223.7) 中已有真正源见证；而 $\varphi_s(j)-j\in\mathfrak n^3$，故 $j\in\varphi_s(A_s)$。最后 $k+t_s(k)\in A_s$，(224.7) 的差已属于刚取回的 $J_{E_s}+\mathfrak n^3\subseteq\varphi_s(A_s)$，所以每个 $k\in K$ 也属于 $\varphi_s(A_s)$。常数被固定，反向包含成立。

右侧确为子代数：两个二次项的乘积属于 $K^2\subseteq J_{E_s}$；二次与四次、两个四次以及任何正次数项与尾项的乘积均属于 $\mathfrak n^3$。有限喷射条件将 $N_{E_s}$ 表示为 $B_s/\mathfrak n^3$ 中一个子空间的完整逆像，故它在诱导拓扑下闭且完备。$\varphi_s$ 及其逆在环境形式拓扑下连续；046，推论 177.3 又给 $A_s$ 的内在极大理想拓扑与诱导拓扑相同。其限制是局部环同构，遂也保持内在极大理想各幂，得到所述完备局部同构。

对于实际纯四次符号的不变性，若 $a\in A_s$ 的常数和二次项为零，(224.6) 说明 $\varphi_s(a)$ 的四次项仍为 $a_4$。反向应用奇逆映射，其一次项仍为恒等，也不改变零二次元素的四次符号，故 $J_4(\varphi_s(A_s))=J_4(A_s)$，相应检测像为同一个 $L\otimes E_s$。

全部成员资格仍有原完成源见证。准确的变换后源映射是 $\pi'_s=\varphi_s\circ\pi_s$。例如 $h\in\mathfrak n^3$ 的见证可取 $Q_s(\varphi_s^{-1}h)$；$j$ 和 $k$ 的见证由上面的反向包含逐次减去已取得见证的四次差与完整尾差得到。正向包含则适用于每个 $\pi'_s(a)$，$a\in\mathscr T$。因此等式没有用环境中不存在来源的级数替代实际源像。证毕。

## 225. 嵌入图、覆盖等价与完成局部同构的范围

**定义 225.1（所用坐标等价及量词）。** 此处允许的操作是 $R$ 上线性项为恒等、与 $z\mapsto-z$ 交换的连续形式自同构，以及它在 $B_s$ 上的限制。定理 224.1 实际使用其中特殊的一次加齐次三次代换。对于固定的 $E$ 和实际图 $\tau$，它对四阶数据的作用为

$$
J_E\longmapsto J_E,
\qquad \tau\longmapsto\tau+D_E(f).
\tag{225.1}
$$

这由 (224.5)--(224.6) 给出，不是把一般无穷小轨道自动当成完整形式轨道；整个完整环等式另由尾项与两个包含得到。

在原负坐标中，$\tau_s$ 是实际嵌入图的一部分，并没有被定义为零。定理 224.1 证明它在上述覆盖坐标等价下可消去，所以它不再贡献相对于固定 $W,K,E_s$ 的额外完成局部同构数据。$N_{E_s}$ 是相对于整个实际子空间 $E_s$ 的完整代表；这不判定不同 $E_s$ 之间的任意抽象局部同构，也不把未经任何等价关系的字面子空间宣称为完整抽象分类不变量。

满射定理的量词是

$$
\forall F,V,E\ \forall\tau\ \exists f\ \forall k\in K,
\qquad D_E(f)(k)=\tau(k).
\tag{225.2}
$$

实际应用是每个已固定的 $F,D,\theta,s$ 及其实际 $\tau_s$ 各自存在一个 $f_s$。同一纤维的全部一百零五个二次方向共用这一组十五个三次式；元组可以随纤维而变。这里没有一组元组同时适用于所有正枢轴或所有 $\tau$ 的结论。

$\pi'_s=\varphi_s\pi_s$ 与 $\pi_s$ 有同一实际核，因为 $\varphi_s$ 可逆。但这没有计算该核，没有给出 $\ker\pi_s=(s)\mathscr T$，也没有提供 $\mathscr T$ 的自同构来实现 $\varphi_s$。原带符号标签系数、七幂窗口以及预固定正枢轴都没有被更换。覆盖坐标等价与原系数源的合法操作是不同问题。

## 226. 完整的普通中文数学解释

**定义 226.1（同时去掉四次图的含义）。** 从同一个原特征零域、一个真实十四次可分域扩张和任一本原元开始，使用它的零次至六次幂这七个连续幂，保留原来的全部符号和嵌入标签系数，并预先固定二十一条合法正枢轴。研究对象是原完成系数环映到这个纤维后的实际像。它的正规化纤维由十五个负变量的全部偶形式级数组成；这里没有把实际像改成原源除以枢轴生成的理想。

已有二次理论给出全部实际二次方向，组成空间 $K$。已有尾项理论又保证，所有普通次数至少六的偶级数都有原完成源中的真实见证。因此剩余问题准确集中在四次层，且可以真实地在源中减去整个高阶尾项。

四次层有两种信息。第一种来自那些常数和二次项都已经消失的实际函数，它们的四次项组成纯四次空间 $J_4$。第二种来自非零二次方向的提升：一个二次方向虽然能提升成实际函数，却一般附带四次项。改变提升时，四次项的差属于第一种空间。因此，每个二次方向附带的四次项在模掉 $J_4$ 后有确定的余类，这些余类合起来就是线性图 $\tau_s$。不能把任意一个二次提升的裸四次尾巴直接算进 $J_4$。

忠实检测器把四次式送到“行列式线乘负线性空间”中，其核恰是两个 $K$ 元素乘积的空间。这个整个核本来就在真实纯四次空间内，所以 $J_4$ 恰由它的完整实际检测子空间 $E_s$ 决定。行列式在这里仍是一条线，没有偷偷选成标量。$E_s$ 是实际源给出的整个空间，不是为了正规形而任选的一组四次项；它还没有算出。

真正的共同困难是：十五个负坐标只能统一改一次，必须同时照顾全部一百零五个二次方向。逐个二次方向可以调整，并不保证这些调整来自同一组坐标变化。定理 222.1 将一切可能阻止共同解的线性关系写成对偶障碍。准确的伴随公式带有一个迹项；Pfaffian 的 Hessian 行列式恒等式给出另一个因子五的迹关系，二者合起来迫使该迹为零。随后利用二次对称性、一个在原域上可逆的局部形式梯度及极化，证明余下的整个障碍也为零。这就证明同一组十五个三次式确实存在，且全部系数都在原域。

给每个负坐标加上这组齐次三次式，就一次取消整个 $\tau_s$。这个代换是奇的，线性项为恒等，逐次解系数可得形式逆，所以保留偶级数环及全部六阶以上尾项。二次项在代换下产生的四次变化正好取消图；纯四次项只多出六阶以上误差，而那些完整误差已有实际源见证。先证明代换后的实际像都落在所写正规形里，再反向取回全部尾项、全部纯四次元素和每个二次方向，得到整个代数的精确等式，不只是首项相同。正向换元不需要五次或更高修正，逆换元可以有更高奇次项。

所以，这张四次图在原覆盖坐标中确实存在，却可通过本定理证明的坐标等价消去；留下的结构是尚未计算的实际 $E_s$。这是相对于该子空间的完整完成纤维正规形，并没有分类不同子空间何时给出抽象同构的环。每个固定纤维可以使用自己的元组，同一元组处理该纤维的全部二次方向。原带标签源上的操作没有因此得到，正枢轴没有因此改变；实际检测的第七方向或全十五方向、完整原源核、完整原源芽、未完成及全局问题也没有因此解决。

## 227. 数学来源、精确重叠与实际未定子空间

**定义 227.1（原始文献的对应与使用条件）。** 下列经典工具均在定理 222.1 或 224.1 的证明内部使用或比较，不作为独立新增的项目定理提出。其文献状态为 `literature-attested`，所需的原域对应如表中所列。

| 原始来源 | 精确内容、对应与适用边界 |
| --- | --- |
| Masoumeh Sepideh Shafiei，*Apolarity for determinants and permanents of generic matrices*，[arXiv:1212.0515v2，Definition 4.5、Lemmas 4.6--4.8、Theorem 4.11](https://arxiv.org/html/1212.0515v2#S4) | 四行 Pfaffian 的二次消去子、Pfaffian 导数与低阶 Pfaffian 空间，以及泛交错矩阵 Pfaffian 消去理想的二次生成。对六阶矩阵，本文的对应是 $D_qP(x)=\eta(\mu(q)\wedge x)$，由完美外乘配对得 $\operatorname{Ann}(P)_2=K$。该文的二次空间记号 $W$ 与本文 $W=\bigwedge^2V$ 不同。理想生成讨论的是 $K H_2$ 等理想分量，不是恰好两个因子的 $K^2$，也不提供 $G$ 的同时满射。 |
| Joachim Jelisiejew，*Classifying local Artinian Gorenstein algebras*，[arXiv:1511.08007v3，§2.2、Proposition 2.10、Corollary 2.12、Proposition 2.18](https://arxiv.org/html/1511.08007v3#S2.SS2) | 导子的转置为 $D^\vee f=\sum_i x_i(D(\alpha_i)\mathbin{\lrcorner}f)$；特征零普通多项式字典及形式代换伴随公式含阶乘；Proposition 2.18 给单个逆系统多项式的切轨道及其正交条件。其幂级数环对应本文覆盖 $R$，不是原带标签系数源 $S$。本文采用 (222.4) 的次数归一化配对，故乘法伴随为 $D_v/4$，并在 (222.16) 重新导出完整常数。 |
| 同上，[§2.4、§3.1，Proposition 3.3、Corollary 3.4](https://arxiv.org/html/1511.08007v3#S3.SS1) | 形式正规形的经典先例是用切作用消去首个差异。该文 §2 起设基域代数闭，§2.4 限于复数并截断自同构群，§3 假设代数闭且特征零或足够大。单生成元轨道及 Artinian Gorenstein 结论不直接给本文 $\operatorname{Hom}(H_2,L\otimes W)$ 的满射。本文没有使用从代数闭域轨道返回原域的结论；原域上的线性解、形式逆及整个子代数等式分别由 §§222--224 证明。 |
| Daniel J. F. Fox，*Functions dividing their Hessian determinants and affine spheres*，[arXiv:1307.5394v4，Theorem 1.5 与 §3 的实交错矩阵 Pfaffian 例 (4)](https://arxiv.org/html/1307.5394v4)，[DOI:10.4310/ajm.2016.v20.n3.a5](https://doi.org/10.4310/ajm.2016.v20.n3.a5) | 正则不可约复预齐性向量空间的相对不变量及其实形式给 Hessian 幂恒等式；该例为实 $2n$ 阶交错矩阵，作用 $X\mapsto gXg^t$，特征标 $\det g$，不变量为 Pfaffian。这提供相对不变量背景，不提供任意原域上的同时 $G$ 定理。(222.9)--(222.12) 以外乘块、原域交错正规形和无限域多项式恒等式直接支付本文的原域恒等式。 |

上述 apolar 对应也可不依赖任何消去理想生成定理而直接验证：由 (222.3) 求两次方向导数有 $D_uD_vP(x)=\eta(x\wedge u\wedge v)$，再线性延拓到 $q\in H_2$。因此它的核正是 $\ker\mu$。相应的泛矩阵坐标局部导数为 $\partial_{12}\operatorname{Pf}(X)=\operatorname{Pf}(X_{\widehat1\widehat2})$；第一行展开中其余项不含 $x_{12}$，导数为零。本文的归一化采用这一直接方向导数恒等式。

**定义 227.2（既有仓内接口与新增同时关系）。** 仓内比较范围为下列钉版正文以及基于 $e526f0f5e3a1e84b05f05c0c009eab920bc3a06f$ 的 030--050 理论卷。该范围内的数学分工为：

| 数学来源 | 直接复用的内容与本卷的区别 |
| --- | --- |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，§§168--170](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 检测器的核 $K^2$、因子十八的满射接口和共同原源提升。它的评价族关系不是整个实际像上的三次覆盖坐标作用。 |
| [046，9b1e19f102fb2f399677cae4b720d631afcc1245，§§174--179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) | 全部实际二次像、整个 $\mathfrak n^3$ 的完成源见证、实际纯四次定义与有限源公式。本卷直接使用这些结论，没有重新证明尾项定理。 |
| [047，§§182、186--187](https://github.com/the-omega-institute/trureturing/blob/e526f0f5e3a1e84b05f05c0c009eab920bc3a06f/docs/develop/theory/AURIC_R5_047_EXACT_QUADRATIC_POWERS_AND_UNIFORM_ACTUAL_FIBRE_CUTOFF.md) | 一般偶数次数的实际截断在 $m=7$ 专化为相同的三次理想阈值；它不消去本卷的二次到四次图。 |
| [048，f9991f7bf7c5b5c48d7c46c4c78272154eb81617，Theorem 193.1 与 §§195--199](https://github.com/the-omega-institute/trureturing/blob/f9991f7bf7c5b5c48d7c46c4c78272154eb81617/docs/develop/theory/AURIC_R5_048_FINITE_AFFINE_QUARTIC_DETECTION_AND_SIX_DIRECTION_PIVOTS.md) | 已给整个实际检测预像及改变正枢轴的有限仿射相容性问题。该作用的定义域是实际原源关系；本卷固定正枢轴，改变负覆盖坐标，定义域为三次导子。定理 222.1 不判定该卷正枢轴相容方程。 |
| [049，f55d41e85ca1cda3fc32def4df3702dbb47dc928，§203](https://github.com/the-omega-institute/trureturing/blob/f55d41e85ca1cda3fc32def4df3702dbb47dc928/docs/develop/theory/AURIC_R5_049_EXACT_COMPLETED_FIBRE_CONDUCTOR_AND_SIX_DIRECTION_WEDGE_SURJECTIVITY.md) | 已定义代表无关的实际 $\tau_s$，证明精确有限图、双向原源见证及完整逆像；§223 按所需类型复用。其导子与六方向外乘结论没有提供 $\tau_s$ 的共同三次消去元组。 |
| [050，9e37dc9c4531a321252200a60fff42c145985861，§§212--220](https://github.com/the-omega-institute/trureturing/blob/9e37dc9c4531a321252200a60fff42c145985861/docs/develop/theory/AURIC_R5_050_ACTUAL_NORMALIZATION_DEFECT_ACTION_AND_BUCHSBAUM_CRITERION.md) | 已给实际缺陷模的完整作用、局部上同调与 Buchsbaum 判据；其 (215.4) 是模截面的线性表示，并未将 $A_s\subset B_s$ 齐次分裂，也没有证明本卷的同时 $G$。 |

030--038 的窗口几何与系数商、039--040 的正规化和耦合二次像、041 的次数十与十二正规形、042--044 的实际提升与评价方向构成上述接口的早先来源。该有界比较中尚需支付的关系是定理 222.1 的整个同时坐标作用及定理 224.1 的实际应用，而非再述检测或尾项。本文将这两项记为 `repo-derived` 的综合推导；Pfaffian、apolar 对偶及形式正规形方法归于上表经典来源，不据此主张全局文献原创。

**定义 227.3（仍未求出的实际空间）。** 对给定而保持不变的 $F,D,\theta,s$，剩余实际数据仍是

$$
T_s=\Psi(J_4(A_s))=L\otimes E_s.
\tag{227.1}
$$

046，§179 已给同一纤维内六个共同原方向，所以 $6\le\dim_FE_s\le15$；本文没有求出 $E_s$ 或其秩，没有推出第七方向或全十五方向。对所有抽象子空间 $E$ 的线性满射不等于这些子空间均可由实际原系数源实现。不同实际 $E_s$ 的抽象同构分类、原源上的坐标提升、完整原源核与完整芽、未完成及全局结构均不包含在 (224.2) 中。这里的“完整”准确指相对于实际 $E_s$ 的整个完成代数等式。

## 追加锚（本行以下为增补区）
