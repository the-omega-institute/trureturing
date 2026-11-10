# 原共轭 CM 临界过滤的共振乘积、覆盖与联合能量

## 24. 原有限端、任意同阶段整数片与真实纤维

**定义 24.1（固定来源与连续同阶段片）。** 固定 [UPPM-RG 002](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md) 定义 20.1、21.1、22.1 的实际 CM 数据、实方向 $\alpha\in\mathbb T^2$、全部原有限地方过滤 $U_v$、完整有限目标同胚 $\eta$ 及整数 $M\ge1,a_0\in\mathbb Z$。沿用

$$
\begin{gathered}
\mathbb T=\mathbb R/\mathbb Z,\qquad
A=\{n\ge1:n\equiv a_0\pmod M\},\qquad
C_M=a_0+M\widehat{\mathbb Z},\\
Y=C_M\times\mathbb T^2,\qquad
\nu=\lambda_{C_M}\otimes m_{\mathbb T^2},\\
c_0>0,\quad\beta,\gamma\ge0,\quad\beta+\gamma>0,\quad c_0^2+2\beta=1,\\
h(n)=\max\left(2,\left\lfloor c_0\sqrt{\log(n+2)}\right\rfloor\right),\qquad
\rho(n)=(n+2)^{-\beta}(\log(n+2))^{-\gamma},\\
q_H=q(H,H;M),\qquad q_n=q_{h(n)}.
\end{gathered}
\tag{24.1}
$$

两因子上的测度均为归一化 Haar 测度。$q_H$ 始终是原全部有限地方的共同周期；$M\mid q_H$，且 $H\le H'$ 时 $q_H\mid q_{H'}$。取整数 $0\le A_0<B_0$，令

$$
\begin{gathered}
I=(A_0,B_0]\cap\mathbb Z,\qquad h(n)=H\quad(n\in I),\qquad Q=q_H,\\
J=\#(I\cap A)
=\left\lfloor\frac{B_0-a_0}{M}\right\rfloor
 -\left\lfloor\frac{A_0-a_0}{M}\right\rfloor>0,\\
D=Q/M,\qquad K=J/D=\frac{MJ}{Q}>0,\qquad
0<r<\frac14,\\
d=Kr^2,\qquad m=4Kr^2,\qquad a=\lfloor K\rfloor,\qquad\tau=K-a.
\end{gathered}
\tag{24.2}
$$

这里 $d$ 是下述对偶格的协体积，不是原定义 21.1 中的 $d_H=q_H/M$。不要求 $K\ge1$ 或 $d\ge1$；$I$ 可为一个阶段的任意非空连续整数片，片内 $J=0$ 的情形则所有事件均为空。

**定义 24.2（同一整数与同一首中心）。** 对任意比较实方向 $\omega\in\mathbb T^2$，仅替换实端，保留定义 24.1 的有限端。令

$$
\begin{aligned}
\mathcal B_r(w)&=\{z\in\mathbb T^2:\|z_j-w_j\|_{\mathbb T}<r\ (j=1,2)\},\\
F_{n,I,r}(\omega)&=
\begin{cases}
(n+Q\widehat{\mathbb Z})\times\mathcal B_r(n\omega),&n\in I\cap A,\\
\varnothing,&n\notin I\cap A,
\end{cases}\\
V(u,z;\omega)&=\sum_{n\in I}\mathbf1_{F_{n,I,r}(\omega)}(u,z),\\
B(\omega)&=\{(u,z)\in Y:V(u,z;\omega)>0\},\qquad b(\omega)=\nu(B(\omega)),\\
\mathcal E(\omega)&=\int_Y V(u,z;\omega)^2\,d\nu,\qquad
T(\omega)=\frac{\mathcal E(\omega)}{m^2},\qquad
P(\omega)=\frac{\sup_{(u,z)\in Y}V(u,z;\omega)}m,\\
N(u)&=\#\{n\in I\cap A:u\equiv n\pmod Q\}.
\end{aligned}
\tag{24.3}
$$

若 $\bar u\in\{0,\ldots,Q-1\}$ 表示 $u\bmod Q$，则

$$
N(u)=\left\lfloor\frac{B_0-\bar u}{Q}\right\rfloor
     -\left\lfloor\frac{A_0-\bar u}{Q}\right\rfloor.
\tag{24.4}
$$

因 $u\in C_M$，该剩余类已包含 $n\equiv a_0\pmod M$。当 $N(u)>0$ 时，令 $n_0(u)$ 为片内此剩余类的最小整数；准确允许项为

$$
n_0(u)+\ell Q,\qquad 0\le\ell<N(u).
\tag{24.5}
$$

在 $N(u)=0$ 的纤维上约定 $n_0(u)=0$、$V(u,z;\omega)=0$。$N,n_0$ 均只依赖有限余类 $u\bmod Q$，因而可测。对每个 $u$ 记

$$
\begin{gathered}
b(u;\omega)=m_{\mathbb T^2}\{z:V(u,z;\omega)>0\},\qquad
 e(u;\omega)=\int_{\mathbb T^2}V(u,z;\omega)^2\,dm_{\mathbb T^2}(z),\\
m(u)=4r^2N(u),\qquad
\zeta=1+\frac{\tau(1-\tau)}{K^2}.
\end{gathered}
\tag{24.6}
$$

有限端与两个实端始终共用同一个 $n$。$\omega=\alpha$ 时且 $r\le\rho(n)$ 时，$F_{n,I,r}(\alpha)$ 是原事件 $E_n$ 的子事件；其他 $\omega$ 沿用原定义 22.1 的比较意义，不被解释成原 CM 点。

**定义 24.3（三条截断共振长度）。** 固定 $\omega$ 的任一实提升，置

$$
\begin{gathered}
\Lambda=\left\{\left(\frac\ell K,\frac{\ell Q\omega-b}{r}\right):
\ell\in\mathbb Z,\ b\in\mathbb Z^2\right\},\\
L=\Lambda^*=\{(K(a'-Qk\cdot\omega),rk):a'\in\mathbb Z,\ k\in\mathbb Z^2\}.
\end{gathered}
\tag{24.7}
$$

星号是整数内积对偶，范数取欧氏范数。对三维满秩格 $L$ 定义

$$
\begin{gathered}
\lambda_i=\lambda_i(L)
=\min\{t>0:\dim_{\mathbb R}\operatorname{span}(L\cap\overline B(0,t))\ge i\},
\qquad 1\le i\le3,\\
p=\min(1,\lambda_1)\min(1,\lambda_2),\qquad
p_3=\prod_{i=1}^3\min(1,\lambda_i),\\
\mathfrak r=\dim_{\mathbb R}\operatorname{span}\{v\in L:\|v\|_2<1\}.
\end{gathered}
\tag{24.8}
$$

离散性使极小值取得，$0<\lambda_1\le\lambda_2\le\lambda_3$。共振秩用严格阈值 $1$，长度恰为 $1$ 的向量不计入。换实提升只重新编号 $b,a'$，不改变格、极小值或乘积。

## 25. 全参数乘积控制准确覆盖、能量与逐点计数

**定理 25.1（任意真实同阶段片的三因子尺度）。** 对定义 24.1–24.3 的每个 $I,r,\omega$，没有 $K$ 或 $d$ 的额外下界，有

$$
\begin{gathered}
N(u)\in\{\lfloor K\rfloor,\lceil K\rceil\}\quad(u\in C_M),\\
\lambda_{C_M}(N=a)=1-\tau,\qquad
\lambda_{C_M}(N=a+1)=\tau,\\
\int_{C_M}N\,d\lambda_{C_M}=K,\qquad
\int_Y V\,d\nu=m,\qquad
\int_{C_M}m(u)^2\,d\lambda_{C_M}=m^2\zeta,\\
\det\Lambda=d^{-1},\qquad\det L=d,\qquad
 d\le\lambda_1\lambda_2\lambda_3\le\frac6\pi d<2d,\\
\min(d,p)\le p_3\le2\min(d,p).
\end{gathered}
\tag{25.1}
$$

当 $\tau=0$ 时只有 $N=a$。每个目标及每个有限端纤维均满足

$$
\begin{gathered}
V(u,z;\omega)\le\min\left\{N(u),\frac{108m}{p_3}\right\},\\
\frac{p_3}{108}\frac{N(u)}K\le b(u;\omega)\le\min(1,m(u)),\\
m(u)^2\le e(u;\omega)\le\frac{108m}{p_3}m(u).
\end{gathered}
\tag{25.2}
$$

在完整目标空间上，有

$$
\boxed{\frac{p_3}{108}\le b(\omega)\le\min(1,m,12p,12p_3),}
\tag{25.3}
$$

$$
\boxed{
\max\left\{\zeta,\frac1{b(\omega)}\right\}
\le T(\omega)\le P(\omega)\le\frac{108}{p_3},\qquad
\frac1{12p_3}\le T(\omega).
}
\tag{25.4}
$$

若 $0<K\le1$，还有准确等式 $b(\omega)=\mathcal E(\omega)=m$、$T(\omega)=P(\omega)=1/m$，对每个方向均成立。

大质量特殊后果为：若 $d\ge1$，则 $\lambda_3\ge d^{1/3}\ge1$、$p_3=p$、$\mathfrak r\le2$，且

$$
b(u;\omega)\le\min(1,12p),\qquad
e(u;\omega)\ge\frac{m(u)^2}{\min(1,12p)},\qquad
T(\omega)\ge\frac\zeta{\min(1,12p)}.
\tag{25.4a}
$$

**证明（真实整数分配与严格窗）。** 写 $u=a_0+Mv$。片内 $n\in A$ 对应连续的 $J$ 个整数 $t=(n-a_0)/M$，而 $u\equiv n\pmod Q$ 等价于 $t\equiv v\pmod D$。以

$$
J=aD+s,\qquad 0\le s<D,\qquad s/D=\tau
$$

分配连续整数：有 $s$ 个类各含 $a+1$ 项，其余类各含 $a$ 项，每类的 Haar 概率为 $1/D$。这证明 (25.1) 的真实 floor/ceil 分布，包括所有 $N=0$ 的类。每个严格实盒面积为 $4r^2$，故

$$
\begin{gathered}
\int_{\mathbb T^2}V(u,z;\omega)\,dm_{\mathbb T^2}(z)=4r^2N(u)=m(u),\\
\int_Y V\,d\nu=4r^2K=m,\\
\int_{C_M}m(u)^2\,d\lambda_{C_M}
=(4r^2)^2\bigl((1-\tau)a^2+\tau(a+1)^2\bigr)
=m^2\zeta.
\end{gathered}
\tag{25.5}
$$

当 $N=N(u)>0$ 时，取 $z$ 的实提升，令 $\xi=(0,(n_0(u)\omega-z)/r)$。准确计数式是

$$
V(u,z;\omega)=\#\left((\xi+\Lambda)\cap
 \bigl([0,(N-1)/K]\times(-1,1)^2\bigr)\right).
\tag{25.6}
$$

时间端点准确选出 $\ell=0,\ldots,N-1$；后两坐标的严格不等式保留原开盒。每个命中整数唯一对应一个空间整数提升，因为 $2r<1$。若 $N=0$，只使用 $V=0$，不使用 (25.6) 的时间窗。对全部 $K>0$ 都有

$$
N-1\le\lceil K\rceil-1\le K\qquad(N>0).
\tag{25.7}
$$

因此实际命中点均在 $[0,1]\times[-1,1]^2$ 内，进而在以 $c=(1/2,0,0)$ 为中心、半径 $3/2$ 的闭球内。

**证明（经典格论输入在本窗中的应用）。** $\Lambda$ 的基矩阵可取

$$
\mathsf A=
\begin{pmatrix}
1/K&0&0\\
Q\omega_1/r&-1/r&0\\
Q\omega_2/r&0&-1/r
\end{pmatrix}.
$$

行列式绝对值为 $1/d$；解与三列的整数配对条件即得 (24.7) 的 $L$，所以 $\det L=d$。以下一般格论均为经典中间输入，不另立新定理。

Freyer–Lucas，*Interpolating between volume and lattice point enumerator with successive minima*，[arXiv:2105.13090v2 原文](https://arxiv.org/pdf/2105.13090v2)，第 1 页 (1.1) 后以 $\operatorname{cs}(C)=(C-C)/2$ 定义非对称凸体的逐次极小，第 3 页 Corollary 1.2 给出：对任意有非空内部的紧凸体 $C\subset\mathbb R^n$，

$$
\#(C\cap\mathbb Z^n)
\le\prod_{i=1}^n\left(\frac2{\lambda_i(C,\mathbb Z^n)}+n\right).
\tag{25.8}
$$

不要求 $C$ 关于原点对称。同文第 1 页 (1.2) 的 Minkowski 第二定理上界，按格基变换用于三维欧氏单位球，给出 $\prod_i\lambda_i\le(6/\pi)d$。另一方面，取长度依次不超过 $\lambda_i$ 的独立格向量，它们生成的子格指数至少为 $1$；Hadamard 不等式给 $d\le\prod_i\lambda_i$。这里仅需该整数行列式比较，不把协体积 $d$ 当作任一长度的下界。

记 $a_i=\lambda_i(\Lambda)$。经典整数配对互反下界为 $a_i\lambda_{4-i}\ge1$：两组相应独立向量的张成维数和为 $4$，必有非零整数配对，其绝对值至少为 $1$，再用 Cauchy–Schwarz。对偶与欧氏约定可参见 Banaszczyk，*New bounds in some transference theorems in the geometry of numbers*，Math. Ann. **296** (1993)，625–635，[DOI:10.1007/BF01445125](https://doi.org/10.1007/BF01445125)，[原文印刷页 625–626 的定义](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0296/LOG_0038.pdf)；这里不使用该文的覆盖半径上界。

将包住实际点的闭球平移 $-\xi$，再以 $\mathsf A^{-1}$ 送到整数格，得

$$
C=\mathsf A^{-1}(\overline B(c,3/2)-\xi),\qquad
\operatorname{cs}(C)=\mathsf A^{-1}\overline B(0,3/2).
$$

其逐次极小为 $2a_i/3$，故 (25.8) 与互反下界给出

$$
\begin{aligned}
V(u,z;\omega)
&\le\prod_{i=1}^3(3/a_i+3)
\le27\prod_{i=1}^3(1+\lambda_i)\\
&\le216\prod_{i=1}^3\max(1,\lambda_i)
=216\frac{\prod_i\lambda_i}{p_3}
\le\frac{432d}{p_3}=\frac{108m}{p_3}.
\end{aligned}
\tag{25.9}
$$

$N=0$ 时此界也成立。球只上包命中点；未把球内额外点计作命中，也未使用任意平移窗的正格点下界。

若 $\lambda_3<1$，则 $p_3=\prod_i\lambda_i\in[d,2d]$，且 $p\ge p_3\ge d$。若 $\lambda_3\ge1$，则 $p_3=p\le\prod_i\lambda_i\le2d$。两种情形分别给出 (25.1) 中的 $\min(d,p)\le p_3\le2\min(d,p)$。

**证明（同首中心条带与相关投影的整数楔积）。** 先有 $b\le\int_Y V\,d\nu=m=4d$。为补上 $b\le12p$，按前两条长度分情形。

若 $\lambda_1\ge1$，则 $p=1$，由 $b\le1$ 即可。若 $\lambda_1<1\le\lambda_2$，取最短非零向量

$$
v_1=(t_1,rk_1),\qquad
t_1=K(a_1-Qk_1\cdot\omega),\qquad a_1\in\mathbb Z,\ k_1\in\mathbb Z^2.
$$

当 $k_1=0$ 时，$a_1\ne0$，故 $K\le\lambda_1$，于是

$$
b\le m=4Kr^2\le K\le\lambda_1=p.
\tag{25.10}
$$

当 $k_1\ne0$ 时，对任一 $N(u)>0$ 的纤维及其任一命中项 $n_0(u)+\ell Q$，有

$$
\begin{aligned}
\|k_1\cdot(z-n_0(u)\omega)\|_{\mathbb T}
&\le r\|k_1\|_1+(N(u)-1)|a_1-Qk_1\cdot\omega|\\
&\le\sqrt2\,r\|k_1\|_2+|t_1|
\le\sqrt3\,\lambda_1.
\end{aligned}
\tag{25.11}
$$

第二步使用真实的 (25.7)，最后一步是二元 Cauchy–Schwarz。非零整数 character $z\mapsto k_1\cdot z$ 是到圆的满射，故把 Haar 推为圆 Haar；于是该纤维覆盖不超过 $\min(1,2\sqrt3\lambda_1)$。空纤维覆盖为零。对 $u$ 积分，即有 $b\le2\sqrt3\lambda_1<12p$。

余下 $\lambda_2<1$ 时，取独立 $v_i=(t_i,rk_i)$，使 $\|v_i\|_2=\lambda_i$，其中 $t_i=K(a_i-Qk_i\cdot\omega)$，$i=1,2$。这样的选择包括 $\lambda_1=\lambda_2$ 的情形：先取最短向量，再在半径 $\lambda_2$ 内避开其直线。

若 $k_1,k_2$ 独立，则每个被覆盖的 $z$ 同时满足两条 (25.11)，且两条带都围绕当前这个 $u$ 的同一首中心 $n_0(u)\omega$。以 $k_1,k_2$ 为行的整数矩阵 $\mathsf K$ 行列式非零，故环面同态 $z\mapsto\mathsf Kz$ 满射：对任一目标实提升 $y$，$\mathsf K^{-1}y$ 给出原像。其 Haar 推前为两圆的乘积 Haar，不要求 $|\det\mathsf K|=1$。因此对每个 $u$，

$$
b(u;\omega)\le\prod_{i=1}^2\min(1,2\sqrt3\lambda_i)
\le\min(1,12\lambda_1\lambda_2)=\min(1,12p).
\tag{25.12}
$$

空纤维仍满足此式。这里的乘积来自同一空间 Haar 同态，不是两个阶段或两条轨道的概率独立假设。

若 $k_1,k_2$ 相关，允许其中一个为零。此时

$$
(k_1\cdot\omega)k_2-(k_2\cdot\omega)k_1=0,
$$

而 $v_1\wedge v_2$ 的两个时间与空间混合分量组成

$$
t_1rk_2-t_2rk_1=Kr(a_1k_2-a_2k_1).
\tag{25.13}
$$

纯空间分量为零。因 $v_1,v_2$ 独立，括号内是非零整数向量，其欧氏长度至少为 $1$。于是

$$
p=\lambda_1\lambda_2
\ge\|v_1\wedge v_2\|_2\ge Kr,
\qquad
b\le m=4Kr^2\le4rp<p.
\tag{25.14}
$$

不必从相关投影求矛盾；准确总质量已足以支付覆盖上界。特别地，此分支保留所有零命中与单命中纤维，无须 $Kr>1$。至此所有情形都有 $b\le12p$。结合 $b\le4d$ 与 (25.1)，

$$
b\le\min(4d,12p)\le12\min(d,p)\le12p_3.
\tag{25.15}
$$

相关投影分支的 (25.14) 和纯时间分支的 (25.10) 是全 $Y$ 的质量估计；它们不提供 $b(u;\omega)\le12p_3$ 之类的逐纤维结论。

**证明（积分闭合与小质量端点）。** 固定 $u$，在覆盖外 $V=0$，在覆盖内使用 (25.9)，由 (25.5) 得

$$
m(u)\le\frac{108m}{p_3}b(u;\omega).
$$

这给出 (25.2) 的覆盖下界，包括 $N=0$ 的等号情形；对 $u$ 积分，得到 $b\ge p_3/108>0$。逐纤维的并集界给 $b(u;\omega)\le\min(1,m(u))$；Cauchy–Schwarz 给 $m(u)^2\le e(u;\omega)$；以 (25.9) 乘 $V$ 再积分给出 $e$ 的上界。

同一 Cauchy–Schwarz 在全支集上给 $m^2\le b\mathcal E$，故 $T\ge1/b$。逐纤维 $e\ge m(u)^2$ 积分给 $T\ge\zeta$。此外

$$
\mathcal E\le(\sup_{u,z}V)\int_Y V\,d\nu=m^2P,
$$

结合逐点上界与 $b\le12p_3$，即得 (25.4)。一般情形只得到 $T\ge\max\{\zeta,1/(12p_3)\}$，不能把这两个下界相乘。

若 $0<K\le1$，真实分配使 $N(u)\in\{0,1\}$，因此 $V\in\{0,1\}$，$\mathbf1_B=V=V^2$。积分给 $b=\mathcal E=m$。$J>0$ 保证至少一个事件非空，故 $\sup V=1$，从而 $T=P=1/m$。

**证明（大质量特殊后果）。** 若 $d\ge1$，(25.1) 与极小值排序给 $d\le\lambda_3^3$，故 $\lambda_3\ge1$，$p_3=p$、$\mathfrak r\le2$。此时 $K=d/r^2>16$，纯时间非零向量不可能短于 $1$。若 $\lambda_2<1$ 而两短向量的空间投影相关，(25.14) 会给 $\lambda_1\lambda_2\ge Kr=d/r>4$，与 $\lambda_1\lambda_2<1$ 矛盾。因此前述覆盖上界在此范围完全由单条带、双独立条带或概率不超过 $1$ 的逐纤维估计给出，即 $b(u;\omega)\le\min(1,12p)$。支集上的 Cauchy–Schwarz 给 $m(u)^2\le b(u;\omega)e(u;\omega)$，再用 (25.5) 积分，便得 (25.4a)，无需重做格点计数或总覆盖证明。

用白话说，三因子乘积同时记录实端的窄带重叠与有限端中真正有允许整数的比例。一条共振可以是一条空间条带，也可以是只有少数有限余类被访问的纯时间约束。两条共振的空间投影独立时，两条带的共同面积按宽度相乘；投影相关时，整数楔积迫使长度乘积至少为 $Kr$，而原总质量已比它更小。格计数限制每个目标可重复命中的次数，再对真实命中积分，才得到覆盖下界。整个论证不要求每个纤维非空，也不要求任意平移窗含格点。常数 $12,108$ 均不取最优。$\square$

## 26. 原大质量好阶段中的一条与两条共振

**定理 26.1（原临界好阶段的两因子后果）。** 沿用原定义 21.1 的 $\mathcal H_-,X_H,Q_H=q_H,J_H,K_H,r_H$，取 $I=(X_H,2X_H]\cap\mathbb Z$、$r=r_H$，并将本卷各量加下标 $H$。在 $H\in\mathcal H_-$ 的充分大尾部，原定理 21.2 保证

$$
h(n)=H\ (n\in I),\qquad r_H\to0,\qquad
\Delta_H:=K_Hr_H^2\to\infty,\qquad K_H\to\infty.
\tag{26.1}
$$

对任意方向 $\omega$，此尾部有 $\lambda_{3,H}\ge1$、$p_{3,H}=p_H$、$\mathfrak r_H\le2$，并且

$$
\begin{gathered}
\frac{p_H}{108}\frac{N_H(u)}{K_H}
\le b_H(u;\omega)\le\min(1,12p_H),\\
\frac{m_H(u)^2}{\min(1,12p_H)}
\le e_H(u;\omega)\le\frac{108m_H}{p_H}m_H(u),\\
\frac{p_H}{108}\le b_H(\omega)\le\min(1,12p_H),\qquad
\frac{\zeta_H}{\min(1,12p_H)}
\le T_H(\omega)\le P_H(\omega)\le\frac{108}{p_H}.
\end{gathered}
\tag{26.2}
$$

严格共振秩恰有以下三种情形：

$$
\begin{array}{c|c|c}
\mathfrak r_H&\text{长度条件}&p_H\\ \hline
0&1\le\lambda_{1,H}&1\\
1&\lambda_{1,H}<1\le\lambda_{2,H}&\lambda_{1,H}\\
2&\lambda_{2,H}<1&\lambda_{1,H}\lambda_{2,H}
\end{array}
\tag{26.3}
$$

因此覆盖分别与 $1,\lambda_{1,H},\lambda_{1,H}\lambda_{2,H}$ 同阶，能量比与峰值分别与它们的倒数同阶，常数可统一取 (26.2) 中的 $12,108$。

对任意无界阶段序列 $H_j\in\mathcal H_-$ 和任意方向序列 $\omega_j$，各量在 $(H_j,\omega_j)$ 取值。若 $\lambda_2\ge c>0$，记 $c'=\min(1,c)$、$s_1=\min(1,\lambda_1)$，则

$$
\frac{c's_1}{108}\le b\le\min(1,12s_1),\qquad
\frac1{12s_1}\le T\le P\le\frac{108}{c's_1}.
\tag{26.4}
$$

若 $\lambda_2\to0$，则

$$
\frac b{\lambda_1}\to0,\qquad
\lambda_1T\to\infty,\qquad\lambda_1P\to\infty.
\tag{26.5}
$$

在这些大质量阶段序列上，还有

$$
b\to0\ \Longleftrightarrow\ p\to0\ \Longleftrightarrow\ \lambda_1\to0
\ \Longleftrightarrow\ T\to\infty\ \Longleftrightarrow\ P\to\infty.
\tag{26.6}
$$

**证明。** (26.1) 直接复用原定理 21.2 的准确质量结论，不重证原阶段构造。取尾部使 $\Delta_H\ge1$，定理 25.1 的大质量特殊后果给出 (26.2)。严格小于 $1$ 的极小值个数就是 $\mathfrak r_H$，故得 (26.3)。将三种 $p_H$ 代入同一个双边界即可；$\zeta_H\ge1$，秩零时尤其有 $1\le T_H\le P_H\le108$。

若 $\lambda_2\ge c$，则 $c's_1\le p\le s_1$，即得 (26.4)。若 $\lambda_2\to0$，尾部为秩二，因而

$$
\frac b{\lambda_1}\le12\lambda_2\to0,\qquad
\lambda_1T\ge\frac1{12\lambda_2}\to\infty,\qquad P\ge T,
$$

即得 (26.5)。最后 $s_1^2\le p\le s_1$，结合 (26.2) 的双边界给出 (26.6)。这些两因子比较只在 $\lambda_3\ge1$ 的范围使用；任意短片的尺度仍是 $p_3$。

本节的 $\mathcal E_H(\alpha)$ 正是原定理 21.3 的准确联合能量，其真实 floor/ceil 零频项仍为 $m_H^2\zeta_H$。若 $p_H<1/12$，(26.2) 还给出每个 $u$ 中未命中目标的面积至少为 $1-12p_H>0$，所以逐点计数上界不能补成对全部目标准确为正的下界。

用白话说，原好阶段的大质量排除了第三条短共振，剩下的两条长度决定覆盖的速度。第二长度有正下界时，第一长度就给出正确尺度；第二长度也趋零时，覆盖还要再乘这个小量，能量还要再除以它。所有结论可取 $\omega=\alpha$，但没有估计实际 $p_H(\alpha)$ 的行为。单个好阶段子族的覆盖趋零，也不能反推完整原 $R(\alpha)$ 零测；完整事件所需的结论在定理 28.1 中另由完整分块推出。$\square$

## 27. 全参数精确实例与逐纤维边界

**定理 27.1（零比较方向的准确三因子尺度）。** 对任意定义 24.1 的真实片段与半径，取比较方向 $\omega=(0,0)$。则三条逐次极小是 $K,r,r$ 的递增重排，并有

$$
\begin{gathered}
L(0)=K\mathbb Z\times r\mathbb Z^2,\qquad
p_3(0)=\min(1,K)r^2,\\
V(u,z;0)=N(u)\mathbf1_{\mathcal B_r(0)}(z),\qquad
b(u;0)=4r^2\mathbf1_{\{N(u)>0\}},\\
b(0)=4\min(1,K)r^2=4p_3(0),\\
T(0)=\frac{\zeta}{4r^2},\qquad
P(0)=\frac{\lceil K\rceil}{4Kr^2}.
\end{gathered}
\tag{27.1}
$$

当 $0<K<1$ 时，

$$
T(0)p_3(0)=P(0)p_3(0)=\frac14,
\qquad b(u;0)=4r^2\quad\text{在所有 }N(u)=1\text{ 的纤维上}.
\tag{27.2}
$$

当 $K\ge1$ 时，

$$
T(0)p_3(0)=\frac\zeta4,\qquad
P(0)p_3(0)=\frac{\lceil K\rceil}{4K}.
\tag{27.3}
$$

特别地，任意真实片段上的 $b(u;\omega)\le C p_3(\omega)$ 不存在统一常数 $C$；一般能量下界也不能改成 $T\ge\zeta/(C p_3)$。原好阶段上则有

$$
\lambda_{1,H}=\lambda_{2,H}=r_H,\quad\lambda_{3,H}=K_H,\quad
\frac{b_H(0)}{\lambda_{1,H}(0)}\to0,\quad
T_H(0)p_H(0)\to\frac14,\quad P_H(0)p_H(0)\to\frac14.
\tag{27.4}
$$

因而即使只在大质量原好阶段，统一的覆盖下界 $c\min(1,\lambda_1)$ 或能量、峰值上界 $C/\min(1,\lambda_1)$ 仍均不成立。

**证明。** 正交直积格的坐标向量分别达到 $K,r,r$；任意短于某一阈值的格向量只能使用坐标长度不超过该阈值的坐标，故极小值就是所列重排。因 $r<1$，截断乘积立即为 $\min(1,K)r^2$，不能在 $K<1$ 时删去时间因子。

所有允许整数的实中心同为 $0$，有限端仍准确保留 $N(u)$，所以 $V$ 与逐纤维覆盖如 (27.1)。由真实分配，$\lambda_{C_M}(N>0)=\min(1,K)$，得全 $Y$ 覆盖公式。又

$$
\mathcal E(0)=4r^2\bigl(K^2+\tau(1-\tau)\bigr),
$$

除以 $m^2$ 得 $T(0)$。至少一个有限余类达到 $N=\lceil K\rceil$，且 $\mathcal B_r(0)$ 非空，所以所列 $P(0)$ 是实际峰值。若 $K<1$，则 $a=0,\tau=K,\zeta=1/K$；代入即得 (27.2)。$K\ge1$ 时 $p_3=r^2$，给出 (27.3)。

为在同一原过滤中检验逐纤维统一界，取任意大的 $H$，在一个真实的 $h=H$ 阶段中只选一项 $n\in A$，并令 $I=\{n\}$。这样的项对充分大 $H$ 存在：原阶段由 $e^{H^2/c_0^2}\le n+2<e^{(H+1)^2/c_0^2}$ 给出，长度趋于无穷，最终超过 $M+1$。此时 $J=1,K=M/q_H$；原定理 16.7 的 $\log q_H=H^2+o(H^2)$ 保证 $K\to0$。取 $r=\rho(n)<1/4$（$H$ 充分大），在非空纤维上

$$
\frac{b(u;0)}{p_3(0)}=\frac4K\to\infty,\qquad
\frac{\zeta/(C p_3(0))}{T(0)}=\frac4{CK}\to\infty.
\tag{27.5}
$$

因此任何固定 $C$ 都被同一原有限端上的真实片段排除。这里的空纤维比例为 $1-K$；非空纤维在全 $Y$ 覆盖率中的权重仍为 $K$。

在原好阶段，$K_H\to\infty$、$r_H\to0$，最终 $K_H>16>r_H$，所以极小值排序如 (27.4)。又

$$
0\le\zeta_H-1\le\frac1{4K_H^2},\qquad
1\le\frac{\lceil K_H\rceil}{K_H}<1+\frac1{K_H},
$$

得到乘积极限。覆盖除以 $\lambda_{1,H}$ 等于 $4r_H\to0$，而

$$
T_H(0)\lambda_{1,H}=\frac{\zeta_H}{4r_H}\to\infty,\qquad
P_H(0)\lambda_{1,H}=\frac{\lceil K_H\rceil}{4K_Hr_H}\to\infty,
$$

证明最后所述替代界均不成立。

用白话说，所有实中心重合时，多一个允许整数只会多重复一次同一方块。若平均允许项数小于一，只有比例 $K$ 的有限余类实际访问这个方块；若平均数很大，每个余类都访问，却仍只覆盖两条短空间宽度的乘积。这个实例保留原 $Q,J,K$ 和原目标来源，但零比较方向不代表原指定 CM 方向。$\square$

## 28. 完整 dyadic 事件的几何判据与共同移位

**定理 28.1（保留全部真实片段的完整零测与满测判据）。** 固定定义 24.1 的全部数据及方向 $\omega$，沿用原定义 22.1 的完整事件

$$
E_n(\omega)=
\begin{cases}
(n+q_n\widehat{\mathbb Z})\times\mathcal B_{\rho(n)}(n\omega),&n\in A,\\
\varnothing,&n\notin A,
\end{cases}
\qquad
R(\omega)=\limsup_{n\to\infty}E_n(\omega).
\tag{28.1}
$$

令 $X_j=2^j$。对充分大的 $j\ge j_0$，按原 $h$ 的实际值将 $(X_j,2X_j]\cap\mathbb Z$ 准确切成连续整数片 $I_{jt}$；非空片最多两片。仅略去 $J_{jt}=\#(I_{jt}\cap A)=0$ 的片，其全部原事件为空。每个保留片都使用自己的

$$
\begin{gathered}
H_{jt}=h|_{I_{jt}},\qquad Q_{jt}=q_{H_{jt}},\qquad
K_{jt}=\frac{MJ_{jt}}{Q_{jt}}>0,\\
r_j^-=\rho(2X_j),\qquad r_j^+=\rho(X_j),\qquad
c_j=\frac{r_j^+}{r_j^-},\qquad C_\rho=2^{\beta+\gamma},\\
p_{3,jt}^{\pm}
=\prod_{i=1}^3\min\left(1,\lambda_i\bigl(L(I_{jt},r_j^{\pm},\omega)\bigr)\right),\\
g_j=\max_t p_{3,jt}^-,\qquad
U_j(\omega)=\bigcup_{X_j<n\le2X_j}E_n(\omega).
\end{gathered}
\tag{28.2}
$$

空最大值约定为 $0$，$L(I,r,\omega)$ 即 (24.7) 的格。取 $j_0$ 足够大使 $r_j^+<1/4$；不删除任何 $K_{jt}<1$ 或 $K_{jt}(r_j^-)^2<1$ 的片。则

$$
\begin{gathered}
\lambda_i(L(I_{jt},r_j^+,\omega))
\le c_j\lambda_i(L(I_{jt},r_j^-,\omega))\quad(i=1,2,3),\\
p_{3,jt}^+\le c_j^3p_{3,jt}^-\le C_\rho^3p_{3,jt}^-,\\
\boxed{\frac{g_j}{108}\le\nu(U_j(\omega))
\le\min(1,24C_\rho^3g_j).}
\end{gathered}
\tag{28.3}
$$

完整无限命中集合满足

$$
\begin{gathered}
R(\omega)=\limsup_{j\to\infty}U_j(\omega),\qquad
\nu(R(\omega))\ge\frac1{108}\limsup_{j\to\infty}g_j,\\
\sum_{j\ge j_0}g_j<\infty\quad\Longrightarrow\quad\nu(R(\omega))=0,\\
\nu(R(\omega))=0\quad\Longrightarrow\quad g_j\to0.
\end{gathered}
\tag{28.4}
$$

若再有 $1,\omega_1,\omega_2$ 在 $\mathbb Q$ 上线性无关，则对同一完整原比较事件序列，

$$
\nu(R(\omega))\in\{0,1\},\qquad
\limsup_{j\to\infty}g_j>0\quad\Longrightarrow\quad\nu(R(\omega))=1.
\tag{28.5}
$$

这些结论均不要求不同 $U_j$ 或不同片的事件独立；$g_j\to0$ 且 $\sum_jg_j=\infty$ 的区域不由本判据裁定。

**证明（真实切片与半径伸缩）。** 原 $h$ 单调，且

$$
c_0\bigl(\sqrt{\log(2X+2)}-\sqrt{\log(X+2)}\bigr)\to0.
$$

故充分大的 dyadic 块中 $h$ 最多取相邻两个整数值，每个水平集均为连续整数片。这只依赖原取整，完全保留跳点两侧的整数。半径单调给

$$
0<r_j^-\le\rho(n)\le r_j^+<1/4\quad(X_j<n\le2X_j),
$$

并且

$$
1\le c_j=
\left(\frac{2X_j+2}{X_j+2}\right)^\beta
\left(\frac{\log(2X_j+2)}{\log(X_j+2)}\right)^\gamma
\le2^{\beta+\gamma}=C_\rho.
\tag{28.6}
$$

最后一界用 $2X+2\le2(X+2)$ 及 $2X+2\le(X+2)^2$，对 $X\ge1$ 成立。

固定一个保留片，$Q_{jt},K_{jt}$ 与有限纤维均不变，增大半径只把对偶格作线性变换

$$
L(I_{jt},r_j^+,\omega)
=\operatorname{diag}(1,c_j,c_j)L(I_{jt},r_j^-,\omega).
\tag{28.7}
$$

该变换保独立且欧氏算子范数为 $c_j$。把达到第 $i$ 极小的独立向量送过去，长度至多乘 $c_j$，即得 (28.3) 的极小值比较。对 $x>0,c\ge1$，$\min(1,cx)\le c\min(1,x)$，三因子相乘给出 $p_3$ 比较；不需要假设极小向量在两个半径下相同。

令 $B_{jt}^{\pm}$ 为在片 $I_{jt}$ 中统一使用半径 $r_j^{\pm}$ 得到的 (24.3) 的覆盖事件。所有有限端柱集仍逐整数使用原 $q_n=Q_{jt}$，严格开盒的嵌套给

$$
\bigcup_t B_{jt}^-\ \subseteq\ U_j(\omega)\ \subseteq\ \bigcup_t B_{jt}^+.
\tag{28.8}
$$

如果没有保留片，则三者均为空。否则定理 25.1 适用于每个片，包括任意小的 $K_{jt}$；于是

$$
\begin{aligned}
\nu(U_j)&\ge\max_t\nu(B_{jt}^-)
\ge\frac1{108}\max_t p_{3,jt}^- =\frac{g_j}{108},\\
\nu(U_j)&\le\sum_t\nu(B_{jt}^+)
\le12\sum_t p_{3,jt}^+
\le12C_\rho^3\sum_t p_{3,jt}^-
\le24C_\rho^3g_j.
\end{aligned}
\tag{28.9}
$$

这是对完整块的上下估计，下界没有把两片的覆盖错误地相加，上界没有忽略任何小质量片。

**证明（完整尾与零测方向）。** dyadic 块两两不交，覆盖所有充分大正整数，且每块仅含有限个整数。因此属于无穷多个 $E_n$ 当且仅当属于无穷多个 $U_j$，即得完整的 $R=\limsup_jU_j$。概率测度的上连续性给

$$
\begin{aligned}
\nu(R)&=\lim_{J\to\infty}\nu\left(\bigcup_{j\ge J}U_j\right)
\ge\lim_{J\to\infty}\sup_{j\ge J}\nu(U_j)
\ge\frac1{108}\limsup_jg_j.
\end{aligned}
\tag{28.10}
$$

所以 $\nu(R)=0$ 必有 $g_j\to0$。若 $\sum_jg_j<\infty$，则同一尾并集又满足

$$
\nu\left(\bigcup_{j\ge J}U_j\right)
\le24C_\rho^3\sum_{j\ge J}g_j\to0,
$$

故 $\nu(R)=0$。这就是收敛 Borel–Cantelli 的并集论证，不需独立性。

**证明（原共同移位与满测方向）。** 假设 $1,\omega_1,\omega_2$ 有理线性无关。原定理 20.2 的共同移位论证在这里逐项适用，核对如下。令

$$
\mathcal T_\omega(u,z)=(u+M,z+M\omega).
$$

因原 $q_n\mid q_{n+M}$、$\rho(n+M)\le\rho(n)$，对每个 $n\ge1$ 均有

$$
\mathcal T_\omega^{-1}E_{n+M}(\omega)\subseteq E_n(\omega).
\tag{28.11}
$$

有限端同减 $M$，实中心同减 $M\omega$；两端仍由同一个整数承担。删除有限前缀及重编号得 $\mathcal T_\omega^{-1}R\subseteq R$。该平移可逆且保 $\nu$，所以 $R$ 模零不变。

以 $(a_0,a_0\omega)$ 为原点，将 $Y$ 识别为 $G=M\widehat{\mathbb Z}\times\mathbb T^2$，平移向量为 $(M,M\omega)$。在任意非空基本窗的有限端，CRT 把允许整数写成一个共同类 $t\pmod\ell$，其中 $\ell$ 是 $M$ 与该窗模数的最小公倍数。对每个非零 $k\in\mathbb Z^2$，$\ell k\cdot\omega\notin\mathbb Z$；经典 Kronecker 定理使 $(t+\ell m)\omega$ 的每条正尾在两圆中稠密。因此同一批共同中心 $(n,n\omega)$ 在 $Y$ 中尾稠密，等价地 $(M,M\omega)$ 生成的子群在 $G$ 中稠密。

复用原定理 20.2 证明中的经典稠密平移遍历性：一个 $L^2(G)$ 函数若在该生成元下不变，则因平移的 $L^2$ 强连续性而在所有平移下不变，故几乎处处为常数。将此用于 $\mathbf1_R$，得到 $\nu(R)\in\{0,1\}$。结合 (28.10)，$\limsup_jg_j>0$ 给出 $\nu(R)>0$，从而为 $1$。这里只对完整 $R$ 使用零一律，不假定单块或其切片的 limsup 平移不变。

本卷使用的 Freyer–Lucas 格点计数、Minkowski 第二定理、整数配对互反、Haar 推前、Kronecker、二阶矩与共同移位遍历性均为已知中间方法（literature-attested）。共同移位的文献先例及原过滤适用桥见原定理 20.2，其所引 Fayad，*Two Remarks on the Shrinking Target Property*，[arXiv:math/0501205v1](https://arxiv.org/pdf/math/0501205v1)，Remark 1.4；正向中心下的逆平移先例见 Tseng，*On Circle Rotations and the Shrinking Target Properties*，[arXiv:math/0702853v2](https://arxiv.org/pdf/math/0702853v2)，§3.2 首段。本卷的新增综合（repo-derived）是任意真实同阶段片中的三因子几何、准确 floor/ceil 计数与完整原事件链；不主张一般格论或零一律的原创性，也不依赖新的预印本格点下界。

用白话说，每个完整二倍块至多分成两个真实阶段片。只要其中较大的三因子乘积保持正比例，整块就覆盖正比例目标；若这些乘积的总和有限，所有块的尾覆盖就趋零。中间的乘积趋零而总和发散时，同一目标会怎样反复落入各块仍缺联合信息，不能从一阶发散补成满测。

对原 $\omega=\alpha$，有理独立性由原定理 11.3 的联合实方向结论提供，所以 (28.4)–(28.5) 是原临界问题的充分或必要接口。然而本卷未判定实际 $g_j(\alpha)$ 的可求和性、上极限或中间区域的行为，仍不裁定 $\nu(R(\alpha))$。比较方向的精确实例、全测结论或反模型均不替代这项原 CM 算术义务。$\square$

## 追加锚（本行以下为增补区）

## 29. 原嵌套有限端的跨片交能量与晚参数消去

**定义 29.1（同源双片与早半径预算）。** 保持定义 24.1–24.2 的原有限过滤、实际周期、完整目标空间与测度。固定一个方向 $\omega\in\mathbb T^2$，假设存在 $A_*>0,\mu>0$，使

$$
\|k\cdot\omega\|_{\mathbb T}\ge A_*\|k\|_\infty^{-\mu}
\qquad(0\ne k\in\mathbb Z^2).
\tag{29.1}
$$

可缩小常数使 $A_*\le1/2$。对 $\omega=\alpha$，原定理 17.2 的 (17.5) 已供应这项假设。取两个定义 24.1 的真实连续同阶段片，记

$$
\begin{gathered}
I_\ell=(A_\ell,B_\ell]\cap\mathbb Z,\qquad
h|_{I_\ell}=H_\ell,\qquad Q_\ell=q_{H_\ell},\qquad
J_\ell=\#(I_\ell\cap A)>0,\\
0<r_\ell<1/4,\qquad
V_\ell=V(I_\ell,r_\ell;\omega),\qquad
m_\ell=\int_YV_\ell\,d\nu=4r_\ell^2\frac{MJ_\ell}{Q_\ell}
\quad(\ell=i,j),\\
Q_i\mid Q_j,\qquad T_j=B_j-A_j\ge2M,\\
\mathfrak t(T,r)=\max\left\{\frac1T,(A_*Tr^\mu)^{-1/(\mu+1)}\right\},
\qquad \Theta_{ij}=Q_i\mathfrak t(T_j,r_i),\\
\mathcal C_{ij}=\int_YV_iV_j\,d\nu.
\end{gathered}
\tag{29.2}
$$

这里 $V(I,r;\omega)$ 是 (24.3) 的计数。称 $i$ 为早片、$j$ 为晚片；估计本身只要求所列模数整除，不另要求两片不交、$r_j\le r_i$、$J_i$ 增长或 $K_i\ge1$。临界阶段消费者中的两片则按原时间先后排列。$T_j$ 是晚片的真实整数长度，不是其模 $Q_j$ 允许项数。

**定理 29.2（准确交核及归一交能量的单侧几何误差）。** 在定义 29.1 下，令 $f_r=\mathbf1_{\mathcal B_r(0)}$，并定义同一个差变量上的交核

$$
\begin{aligned}
\mathsf h_{ij}(t)
&=\int_{\mathbb T^2}f_{r_i}(z)f_{r_j}(z-t)\,dm_{\mathbb T^2}(z)\\
&=\prod_{a=1}^2
\min\left\{2\min(r_i,r_j),
  \bigl(r_i+r_j-\|t_a\|_{\mathbb T}\bigr)_+\right\}.
\end{aligned}
\tag{29.3}
$$

对每个 $m\in I_i\cap A,n\in I_j\cap A$，有

$$
\begin{gathered}
\nu(F_{m,I_i,r_i}(\omega)\cap F_{n,I_j,r_j}(\omega))
=\mathbf1_{\{Q_i\mid n-m\}}\frac M{Q_j}
   \mathsf h_{ij}((n-m)\omega),\\
\mathcal C_{ij}
=\frac M{Q_j}\sum_{m\in I_i\cap A}
  \sum_{\substack{n\in I_j\\n\equiv m\pmod{Q_i}}}
       \mathsf h_{ij}((n-m)\omega).
\end{gathered}
\tag{29.4}
$$

若 $\Theta_{ij}\le1/3$，则保留真实 $J_j$ 的误差为

$$
\boxed{
\begin{aligned}
\left|\frac{\mathcal C_{ij}}{m_im_j}-\frac{T_j}{MJ_j}\right|
&\le48\frac{T_j}{MJ_j}\Theta_{ij},\\
\left|\frac{\mathcal C_{ij}}{m_im_j}-1\right|
&\le\frac{|T_j-MJ_j|+48T_j\Theta_{ij}}{MJ_j}
\le98\Theta_{ij}.
\end{aligned}}
\tag{29.5}
$$

故归一误差只涉及早片的实际 $Q_i,r_i$ 和晚片的长度 $T_j$，不含 $Q_j,r_j,J_i$；没有将晚片的有限条件改成较早过滤，也没有以较大消去数替换实际周期。

**证明（有限交核、严格窗与真实整数）。** 两个有限柱集相交恰当且仅当 $Q_i\mid n-m$，此时交集就是 $n+Q_j\widehat{\mathbb Z}$，在 $C_M$ 中的质量为 $M/Q_j$。这是原 (20.6) 在当前两片中的准确应用。空间部分平移 $-m\omega$ 后为 (29.3) 的积分。因 $r_i+r_j<1/2$，原 (20.7) 的一维弧交计算可对较大、较小半径分别代入，给出该乘积式；无需预先规定哪一片半径更大。严格端点只影响零弧长的边界，不改变积分。

展开有限和即得 (29.4)；其中 $n\equiv m\pmod{Q_i}$ 已蕴含 $n\in A$，因为 $m\in A$ 且 $M\mid Q_i$。晚片中这个较早剩余类的真实项数以及原 $M$ 剩余类的真实项数仍分别为

$$
\begin{gathered}
N_j(m)=\left\lfloor\frac{B_j-m}{Q_i}\right\rfloor
       -\left\lfloor\frac{A_j-m}{Q_i}\right\rfloor,
\qquad \left|N_j(m)-\frac{T_j}{Q_i}\right|<1,\\
J_j=\left\lfloor\frac{B_j-a_0}{M}\right\rfloor
    -\left\lfloor\frac{A_j-a_0}{M}\right\rfloor,
\qquad |MJ_j-T_j|<M.
\end{gathered}
\tag{29.6}
$$

这些是准确 floor 差；不把 $N_j(m)$ 或 $J_j$ 定义为相应的实数长度。

**证明（复用等体积胞误差并对晚窗平均）。** 原 (19.9)–(19.16) 对任意整数模数、剩余类、起点与中心给出固定半径计数。其关于方向的算术输入仅为 $\|qk\cdot\omega\|_{\mathbb T}\ge A_*(q\|k\|_\infty)^{-\mu}$，由 (29.1) 对整数向量 $qk$ 应用即得。因此直接复用 (19.16)，取其尺度 $X=T_j$、模数 $q=Q_i$、半径 $r=r_i$，不重证一般 Voronoi 或覆盖转移定理。前件正是 $Q_i\mathfrak t(T_j,r_i)\le1/3$。对每个 $m\in I_i\cap A$ 和每个 $y\in\mathbb T^2$，令

$$
\begin{aligned}
\mathcal N_{j,m}(y)
&=\#\{n\in I_j:n\equiv m\pmod{Q_i},
        n\omega\in\mathcal B_{r_i}(m\omega-y)\},\\
\left|\mathcal N_{j,m}(y)-\frac{4T_jr_i^2}{Q_i}\right|
&\le192T_jr_i^2\mathfrak t(T_j,r_i).
\end{aligned}
\tag{29.7}
$$

此处主项是体积 $4T_jr_i^2/Q_i$；$N_j(m)$ 的整数误差和所有时间半开、空间严格端点均已由 (19.16) 支付。对晚窗的 Haar 平移平均有准确恒等式

$$
\begin{aligned}
\sum_{\substack{n\in I_j\\n\equiv m\pmod{Q_i}}}
\mathsf h_{ij}((n-m)\omega)
&=\int_{\mathcal B_{r_j}(0)}\mathcal N_{j,m}(y)\,dm_{\mathbb T^2}(y),\\
\left|\sum_{\substack{n\in I_j\\n\equiv m\pmod{Q_i}}}
\mathsf h_{ij}((n-m)\omega)
 -\frac{(4r_j^2)(4r_i^2)T_j}{Q_i}\right|
&\le(4r_j^2)192T_jr_i^2\mathfrak t(T_j,r_i).
\end{aligned}
\tag{29.8}
$$

第一式只用 $\mathsf h_{ij}(t)=\int_{\mathcal B_{r_j}(0)}f_{r_i}(t+y)\,dm(y)$；因此每个空间参数仍对应原同一差 $n-m$。第二式由 (29.7) 的全中心一致性积分得到，不要求两半径之比有界。

再对准确的 $J_i$ 项求和并乘 $M/Q_j$，得到

$$
\left|\mathcal C_{ij}
 -\frac M{Q_j}J_i(4r_j^2)(4r_i^2)\frac{T_j}{Q_i}\right|
\le\frac M{Q_j}J_i(4r_j^2)192T_jr_i^2\mathfrak t(T_j,r_i).
\tag{29.9}
$$

除以 (29.2) 的准确 $m_im_j$，即得 (29.5) 第一式，晚模数、晚半径和早项数均为同一个乘法因子而准确相消。最后由 (29.6)、$T_j\ge2M$ 得 $MJ_j>T_j/2$，所以归一 floor 成本小于 $2M/T_j\le2\Theta_{ij}$，其余误差不超过 $96\Theta_{ij}$，给出第二式。

一般卷积与经典胞计数在这里均只是中间方法；新增综合是原嵌套有限端交核在同一目标实现上与原 (19.16) 的相接，以及 (29.5) 的晚参数消去。用白话说，固定早片的一把允许钥匙，晚片中与它相容的整数只按早模数排列；把晚实窗写成早实窗的平移平均，计数误差就只需支付早半径。晚过滤的稀少比例和晚窗的面积在交能量与两个单块质量中相同，归一后同时消去。$\square$

## 30. 原临界尺度的跨块间隙与趋零覆盖的加权满测

**定理 30.1（两个增长原阶段的统一交能量区域）。** 假设 (29.1)，沿用原定义 21.1 和定理 26.1 的充分大好阶段，令 $Q_H=q_H$、$I_H=(X_H,2X_H]\cap\mathbb Z$、$r=r_H$，并保持所有 $V_H,B_H,m_H,p_H$ 的原定义。置

$$
\chi_{\mathrm{geom}}=(\mu+1)c_0^2+\mu\beta
=\mu+1-(\mu+2)\beta.
\tag{30.1}
$$

任取 $\kappa>\max(1,\chi_{\mathrm{geom}})$ 和
$0<\eta<(\kappa-\chi_{\mathrm{geom}})/(\mu+1)$。存在 $H_0$，使全部 $H_i,H_j\in\mathcal H_-$、$H_0\le H_i<H_j$ 且 $X_{H_j}\ge X_{H_i}^{\kappa}$ 同时满足

$$
\Theta_{ij}\le X_{H_i}^{-\eta}\le\frac13,\qquad
\left|\int_Y\frac{V_{H_i}}{m_{H_i}}\frac{V_{H_j}}{m_{H_j}}\,d\nu-1\right|
\le98X_{H_i}^{-\eta}.
\tag{30.2}
$$

这里 $\Theta_{ij}$ 取 (29.2) 的 $T_j=X_{H_j}$；$H_0$ 对全部这样的晚阶段统一，而非先固定 $H_i$ 再分别取晚端极限。

**证明。** 原定理 16.7、(22.15) 的参数桥和原定义 21.1 给出实际尺度

$$
Q_H=X_H^{c_0^2+o(1)},\qquad r_H=X_H^{-\beta+o(1)},\qquad
\log X_H\sim\frac{H^2}{c_0^2}.
$$

特别地，这里使用实际共同周期的渐近式，不将 (21.4) 中的上界充当等式。将 (29.2) 写成

$$
\Theta_{ij}
=\max\left\{\frac{Q_{H_i}}{X_{H_j}},
 A_*^{-1/(\mu+1)}
 \left(\frac{Q_{H_i}^{\mu+1}r_{H_i}^{-\mu}}{X_{H_j}}\right)^{1/(\mu+1)}\right\},
$$

则在 $X_{H_j}\ge X_{H_i}^{\kappa}$ 的整个区域，两个候选项分别至多为

$$
X_{H_i}^{c_0^2-\kappa+o(1)},\qquad
X_{H_i}^{-(\kappa-\chi_{\mathrm{geom}})/(\mu+1)+o(1)}.
$$

两个 $o(1)$ 只依赖早阶段；固定 $A_*$ 也可吸收入其中。因为

$$
\kappa-c_0^2-\frac{\kappa-\chi_{\mathrm{geom}}}{\mu+1}
=\frac{\mu(\kappa+\beta)}{\mu+1}>0,
$$

所选 $\eta$ 使这两项最终都不超过 $X_{H_i}^{-\eta}$，且该界对晚阶段统一。原模数嵌套给 $Q_{H_i}\mid Q_{H_j}$；原好阶段是真实恒 $h$ 整块，长度 $T_j=X_{H_j}\ge2M$ 最终成立。定理 29.2 因而给出 (30.2)。临界等式 $c_0^2+2\beta=1$ 给出 (30.1) 的第二种写法。$\square$

**定理 30.2（允许 $p_H$ 趋零的原子事件直接满测）。** 在定理 30.1 的同一固定方向下，若存在严格递增的原好阶段序列 $H_\ell\in\mathcal H_-$ 和某个 $\kappa>\max(1,\chi_{\mathrm{geom}})$，使

$$
X_{H_{\ell+1}}\ge X_{H_\ell}^{\kappa}\quad\text{最终成立},\qquad
\sum_{\ell=1}^{\infty}p_{H_\ell}(\omega)=\infty,
\tag{30.3}
$$

则所选原子事件的 limsup 本身满测，从而完整原事件也满测：

$$
\nu\left(\limsup_{\ell\to\infty}B_{H_\ell}(\omega)\right)=1,
\qquad \nu(R(\omega))=1.
\tag{30.4}
$$

不要求 $p_{H_\ell}$ 有正下界；特别地，若 (30.3) 的发散与 $p_{H_\ell}\to0$ 同时成立，则 (26.2) 给出 $\nu(B_{H_\ell})\to0$，而 (30.4) 仍成立。本结论不假定子事件的 limsup 平移不变，也不借完整 $R$ 的零一律将正测升级。

**证明。** 删去有限初段，使原大质量结论、相邻间隙及 (30.2) 同时适用。简记

$$
W_\ell=V_{H_\ell}/m_{H_\ell},\qquad w_\ell=p_{H_\ell},\qquad
\varepsilon_\ell=98X_{H_\ell}^{-\eta},\qquad
\delta_L=\sup_{\ell\ge L}\varepsilon_\ell\longrightarrow0.
$$

对每个 $j>i$，有 $X_{H_j}\ge X_{H_{i+1}}\ge X_{H_i}^{\kappa}$。定理 26.1 与 (30.2) 共同给出原目标空间上的实际矩关系

$$
\int_YW_\ell\,d\nu=1,\qquad
\int_YW_\ell^2\,d\nu\le\frac{108}{w_\ell},\qquad
\int_YW_iW_j\,d\nu\le1+\varepsilon_i\quad(i<j).
\tag{30.5}
$$

其中 $0<w_\ell\le1$，且 $\{W_\ell>0\}=B_{H_\ell}$。对固定尾部 $L$ 和 $N\ge L$，在这些原计数上应用加权二阶法，置

$$
F_{L,N}=\sum_{\ell=L}^Nw_\ell W_\ell,\qquad
a_{L,N}=\sum_{\ell=L}^Nw_\ell.
$$

于是 $\int F_{L,N}\,d\nu=a_{L,N}\to\infty$，且

$$
\begin{aligned}
\int_YF_{L,N}^2\,d\nu
&\le108a_{L,N}
 +2(1+\delta_L)\sum_{L\le i<j\le N}w_iw_j\\
&\le108a_{L,N}+(1+\delta_L)a_{L,N}^2.
\end{aligned}
\tag{30.6}
$$

这里每个对角项的成本为 $w_\ell^2(108/w_\ell)=108w_\ell$；因此只需 $\sum w_\ell$ 发散，无须 $\sum w_\ell^2$ 发散。Cauchy–Schwarz 在 $F_{L,N}>0$ 的支集上给出

$$
\begin{aligned}
\nu\left(\bigcup_{\ell\ge L}B_{H_\ell}\right)
&\ge\nu(F_{L,N}>0)\\
&\ge\frac{a_{L,N}^2}{\int_YF_{L,N}^2\,d\nu}
\ge\frac1{1+\delta_L+108/a_{L,N}}.
\end{aligned}
\tag{30.7}
$$

先让 $N\to\infty$，再让 $L\to\infty$，尾并集的测度上连续性及 $\delta_L\to0$ 得到第一项 (30.4)。所用二阶支集不等式是原定理 20.2 的经典中间方法；趋近 $1$ 的下界由原跨块误差在早指标尾部的一致趋零提供。

最后，原 $r_H=\rho(2X_H)\le\rho(n)$ 对 $X_H<n\le2X_H$ 成立，所以每个 $B_H$ 都是该原块事件并集的子集。$X_{H_\ell}\to\infty$，属于无穷多个这些 $B_H$ 就产生无界的原成功整数，且每次仍由同一个整数满足全部有限端和两个实端。因此 $\limsup_\ell B_{H_\ell}(\omega)\subseteq R(\omega)$，得到第二项 (30.4)。它是目标空间的几乎处处无限命中结论，不是每个目标逐点命中结论。

用白话说，单块覆盖虽可缩小，单块计数的重复成本却至多与 $1/p_H$ 同阶。给每块乘 $p_H$ 权重，累积对角成本便只是权重和；足够隔开的原块又在同一目标空间中渐近不相关，使每条足够晚的尾并集覆盖比例趋于一。$\square$

## 31. 原好阶段几何分箱的凝聚满测判据

**定理 31.1（按 $H$ 凝聚的原临界满测充分条件）。** 保持定理 30.1 的方向与原参数。任取 $s>1$，对原好阶段充分大尾部以前的有限初段约定 $p_H=0$，定义

$$
b_k(s;\omega)=\max\{p_H(\omega):H\in\mathcal H_-\cap[s^k,s^{k+1})\},
\qquad k=0,1,2,\ldots,
\tag{31.1}
$$

空最大值为 $0$。每个非空箱只含有限个整数，故最大值取得；初段的任何有界有限赋值均不影响以下级数的敛散性。若对某个 $s>1$ 有

$$
\sum_{k=0}^{\infty}b_k(s;\omega)=\infty,
\tag{31.2}
$$

则可从每个所选非空箱中取一个原好阶段，得到定理 30.2 的发散间隙子族，且该子族 $B_H(\omega)$ 的 limsup 满测。因而

$$
\begin{gathered}
\left(\exists s>1:\sum_kb_k(s;\omega)=\infty\right)
\ \Longrightarrow\ \nu(R(\omega))=1,\\
\nu(R(\omega))=0
\ \Longrightarrow\ \left(\forall s>1:\sum_kb_k(s;\omega)<\infty\right).
\end{gathered}
\tag{31.3}
$$

在本节的有限型方向范围内，存在无界子族满足 $p_H\ge\epsilon>0$ 的旧充分条件蕴含 (31.2)，故也包含于此判据。条件 (31.2) 同样容许全部 $p_H\to0$；这里不从凝聚和收敛推出完整 $R$ 零测。

**证明。** 固定 $\kappa>\max(1,\chi_{\mathrm{geom}})$，取整数 $D\ge2$ 使

$$
s^{2(D-1)}>\kappa.
\tag{31.4}
$$

将箱指标 $k$ 按模 $D$ 作有限分色。由 (31.2)，至少一色的 $b_k$ 和发散。仅在该色的 $b_k>0$ 箱中取达到最大值的 $H_k$，则 $p_{H_k}=b_k$，所选权重和发散。若 $k'>k$ 是其中相邻的箱指标，$k'-k\ge D$，所以

$$
\frac{H_{k'}}{H_k}>s^{D-1},\qquad
\frac{\log X_{H_{k'}}}{\log X_{H_k}}
\ge(1-o(1))s^{2(D-1)}>\kappa
\quad(k\to\infty).
\tag{31.5}
$$

最后一个 $o(1)$ 对全部 $H_{k'}\ge s^{D-1}H_k$ 统一：原准确 $X_H=\lfloor\exp((H+1/2)^2/c_0^2)\rfloor$ 给出 $\log X_H=(H+1/2)^2/c_0^2+o(1)$，分子与分母的相对误差均可由早阶段的趋零界控制。由 (31.4) 的严格余量，(31.5) 最终给 $X_{H_{k'}}\ge X_{H_k}^{\kappa}$。去掉有限箱便符合 (30.3) 的全部条件，定理 30.2 直接给出所选子事件的满测，继而得到 (31.3)。有限分色只用于取得满足原时间间隙的共同实现子族，不另作一般分色或 Borel–Cantelli 定理。

若 $p_H\ge\epsilon>0$ 在无界子族成立，则对每个固定 $s>1$，无穷多个不同箱满足 $b_k\ge\epsilon$，所以 (31.2) 成立。由 (26.6)，无穷多个 $\lambda_{1,H}\ge\delta>0$ 的旧非塌缩条件也蕴含这一情形。另一方面，证明只使用权重和发散，完全没有使用权重的正下界；$b_k\to0$ 与级数发散在标量条件上相容。这不声称某个给定的趋零标量序列已由原格 $L_H(\omega)$ 实现。

本条的新增综合是将 (29.5) 的原共同实现误差、(30.1) 的临界时间指数和定理 26.1 的原 $p_H$ 对角成本接成凝聚判据（repo-derived）；一般卷积、二阶法与有限分色均是经典中间方法。局部计数、有限交核、原阶段和单块输入分别复用原 (19.16)、(20.6)、原定义 21.1–定理 21.2 以及本卷定理 25.1、26.1，临界参数桥复用原定理 16.7 与 (22.15)。

对指定 $\omega=\alpha$，原 (17.5) 已支付有限型前提，因此 (29.5)、(30.2) 及以上条件性消费者均适用；仍未证明实际 $p_H(\alpha)$ 满足 (31.2)，也未证明存在满足 (30.3) 的发散子族。因此没有据此裁定实际 $\nu(R(\alpha))$。新的算术充分接口是实际前两条截断极小乘积在这些原 $H$ 箱中的最大值是否具有发散总和，而非要求每块覆盖保持正比例。原定理 23.1 的有限型完整零测比较方向必使 (31.3) 中的全部凝聚和收敛；这与其一阶质量发散相容，也不把该必要条件倒置为零测充分条件。$\square$

## 追加锚（本行以下为增补区）

## 32. 原周期的交替坐标与统一有限型比较方向

**定义 32.1（与实半径无关的原周期子序列）。** 保持原卷 [UPPM-RG 002](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md) 定义 20.1、21.1 及本卷定义 24.1 的全部有限地方、原过滤、$M,a_0,A,Y,\nu$ 与实际共同周期 $q_H=q(H,H;M)$。以下取原对数端点

$$
\beta=0,\qquad c_0=1,\qquad
h(n)=\max(2,\lfloor\sqrt{\log(n+2)}\rfloor),\qquad
\rho(n)=(\log(n+2))^{-\gamma},\quad\gamma>0.
\tag{32.1}
$$

由原 (16.27)，可先固定一个整数 $H_0\ge7$，使 $q_{H_0}\ge4$ 且

$$
\frac9{10}H^2\le\log q_H\le\frac{11}{10}H^2
\qquad(H\in\mathbb Z,\ H\ge H_0).
\tag{32.2}
$$

这个选择不涉及 $\gamma$。令

$$
H_s=2^sH_0,\qquad Q_s=q_{H_s},\qquad
\iota(s)=\begin{cases}1,&s\text{ 偶},\\2,&s\text{ 奇},\end{cases}
\qquad(s\ge0).
\tag{32.3}
$$

原整除嵌套和 (32.2) 给出

$$
Q_s\mid Q_{s+1},\qquad Q_s^3\le Q_{s+1}\le Q_s^5,
\qquad Q_s^9\le Q_{s+2}\le Q_s^{25}.
\tag{32.4}
$$

事实上，$\log Q_{s+1}\ge(18/5)H_s^2\ge3\log Q_s$，而 $\log Q_{s+1}\le(22/5)H_s^2\le5\log Q_s$。以通常实数级数定义固定提升

$$
w_i=\sum_{\substack{s\ge0\\\iota(s)=i}}\frac1{Q_s},\qquad
\omega_i=w_i\pmod1,\qquad \omega=(\omega_1,\omega_2).
\tag{32.5}
$$

由 $Q_0\ge4$ 与 (32.4)，这些级数绝对收敛。$H_s,Q_s$ 只定义此比较方向；每个实际事件仍使用自身的 $q_{h(n)}$，不以此子序列替换原过滤。

**定理 32.2（全部整数频率的有限型下界与有理独立）。** 定义 32.1 的同一个 $\gamma$ 无关方向满足

$$
\|k\cdot\omega\|_{\mathbb T}\ge c_\omega\|k\|_\infty^{-125}
\qquad(0\ne k\in\mathbb Z^2),\qquad
c_\omega=\frac1{2C^{25}}>0,\quad C=\max(Q_0,4^5).
\tag{32.6}
$$

因而 $1,w_1,w_2$ 在 $\mathbb Q$ 上线性无关；更换实提升也保持这一性质。指数 $125$ 不主张最优。

**证明。** (32.4) 使每个相邻比值至少为 $16$，所以对每个 $v\ge0$，经典有理级数的几何尾估计在这里给出

$$
\sum_{t>v}\frac1{Q_t}\le\frac2{Q_{v+1}}.
\tag{32.7}
$$

固定任意 $k\ne0$，置 $B=\|k\|_\infty\ge1$。取最小的 $s\ge0$ 使 $Q_s\ge4B$，并写

$$
P_s=\sum_{t=0}^s\frac{k_{\iota(t)}}{Q_t}\in Q_s^{-1}\mathbb Z,
\qquad T_s=\sum_{t>s}\frac{k_{\iota(t)}}{Q_t},\qquad
k\cdot w=P_s+T_s.
\tag{32.8}
$$

这里前缀的分母整除 $Q_s$，且

$$
|T_s|\le\frac{2B}{Q_{s+1}}
\le\frac{2B}{Q_s^3}\le\frac1{2Q_s^2}<\frac12.
\tag{32.9}
$$

若 $P_s\notin\mathbb Z$，则 $\|P_s\|_{\mathbb T}\ge1/Q_s$，圆距离的三角不等式给出

$$
\|k\cdot\omega\|_{\mathbb T}
\ge\frac1{Q_s}-|T_s|\ge\frac1{2Q_s}.
\tag{32.10}
$$

若 $P_s\in\mathbb Z$，交替安排保证尾部的首个非零系数位于某个 $t\in\{s+1,s+2\}$。其绝对值至少为 $1$，此后尾项由同一个 $B$ 控制：

$$
\left|\sum_{v>t}\frac{k_{\iota(v)}}{Q_v}\right|
\le\frac{2B}{Q_{t+1}}\le\frac1{2Q_t}.
\tag{32.11}
$$

最后一步使用 $Q_t\ge Q_s\ge4B$ 与 $Q_{t+1}\ge Q_t^3$。所以 $|T_s|\ge1/(2Q_t)$；又由 (32.9) 的严格 $|T_s|<1/2$，此时圆距离恰为 $|T_s|$。两种前缀情形合起来均有

$$
\|k\cdot\omega\|_{\mathbb T}\ge\frac1{2Q_{s+2}}.
\tag{32.12}
$$

若 $s\ge1$，最小性给 $Q_{s-1}<4B$，故 $Q_s\le Q_{s-1}^5<(4B)^5\le CB^5$；若 $s=0$，直接有 $Q_s=Q_0\le CB^5$。因此所有 $B\ge1$ 都满足 $Q_{s+2}\le Q_s^{25}\le C^{25}B^{125}$，(32.12) 即为 (32.6)。没有把尚未证明为正的有限多个小频率吸收到常数。

任何有理线性关系清除分母后都是 $d+k\cdot w=0$，其中 $d\in\mathbb Z,k\in\mathbb Z^2$。若 $k\ne0$，(32.6) 排除此式；若 $k=0$，则 $d=0$。有理独立性随之成立。前缀分母与尾项分离是经典 Cantor 级数方法在本条内部的中间步骤；这里的综合（repo-derived）是将原实际周期的受控幂增长、两坐标交替及全部频率下界相接，不单立一般级数或独立性定理。$\square$

## 33. 同一有限端上的 character 上包与完整零测

**定义 33.1（辅助整段与有理截断 character）。** 对定义 32.1 的固定方向及每个 $s\ge0$，置

$$
\mathcal I_s=\{n\in\mathbb Z_{\ge1}:H_s\le h(n)<H_{s+1}\},\qquad
N_s=\left\lceil\exp(H_{s+1}^2)\right\rceil,\qquad i_s=\iota(s),
\tag{33.1}
$$

并用活动坐标的有理截断定义整数 $a_s$：

$$
\xi_s=\sum_{\substack{0\le t\le s\\\iota(t)=i_s}}\frac1{Q_t}
=\frac{a_s}{Q_s},\qquad a_s\in\mathbb Z,\qquad
0<w_{i_s}-\xi_s\le\frac2{Q_{s+2}}.
\tag{33.2}
$$

最后一界来自下一次同坐标更新在 $s+2$ 及 (32.7) 的同样几何尾估计。对 $u\in\widehat{\mathbb Z}$，任取 $u\bmod Q_s$ 的整数代表 $b_s$，定义到圆的连续 character

$$
\chi_s:\widehat{\mathbb Z}\times\mathbb T^2\longrightarrow\mathbb T,
\qquad \chi_s(u,z)=z_{i_s}-\frac{a_s b_s}{Q_s}\pmod1,
\qquad
\delta_s(\gamma)=H_s^{-2\gamma}+\frac{2N_s}{Q_{s+2}}.
\tag{33.3}
$$

改变代表 $b_s$ 使 $a_s b_s/Q_s$ 只增加一个整数，所以该式良定义；其有限端因子经过群商 $\mathbb Z/Q_s\mathbb Z$，实端因子是坐标投影。这里使用的是环境紧群的 character 在余类空间 $Y=C_M\times\mathbb T^2$ 上的限制。

**定理 33.2（同一有限型方向在全部正对数指数下完整零测）。** 定义 32.1 的同一个固定 $\omega$ 对每个 $\gamma>0$ 均满足

$$
\nu(R(\omega))=0,\qquad g_j(\omega)\longrightarrow0,
\qquad R(\omega)\text{ 为 }Y\text{ 中的稠密 }G_\delta.
\tag{33.4}
$$

$E_n(\omega),R(\omega)$ 严格取 (28.1) 的原完整比较事件，$g_j$ 严格取 (28.2) 在该 $\gamma$ 下的全部真实 dyadic 片；原 $h,q_{h(n)},\rho,M,a_0,Y$ 及每次事件的同一个整数均保持不变。

**证明（逐整数、逐纤维的完整上包）。** 若 $n\in\mathcal I_s$，因 $H_s\ge7$，原取整给出

$$
H_s^2\le\log(n+2)<H_{s+1}^2,\qquad
n<N_s,\qquad \rho(n)\le H_s^{-2\gamma},\qquad
Q_s\mid q_{h(n)}.
\tag{33.5}
$$

若 $(u,z)\in E_n(\omega)$，则 $n\in A$ 且 $u\equiv n\pmod{q_{h(n)}}$，从而同一个 $u$ 满足 $b_s\equiv n\pmod{Q_s}$。有理截断恰给 $a_s b_s/Q_s=n\xi_s\pmod1$，故

$$
\begin{aligned}
\|\chi_s(u,z)\|_{\mathbb T}
&=\|z_{i_s}-n\xi_s\|_{\mathbb T}\\
&\le\|z_{i_s}-n\omega_{i_s}\|_{\mathbb T}
       +n|w_{i_s}-\xi_s|\\
&<\rho(n)+\frac{2N_s}{Q_{s+2}}\le\delta_s(\gamma).
\end{aligned}
\tag{33.6}
$$

因此在同一完整目标空间上有

$$
\bigcup_{n\in\mathcal I_s}E_n(\omega)
\subseteq S_s:=\{(u,z)\in Y:\|\chi_s(u,z)\|_{\mathbb T}<\delta_s(\gamma)\},
\qquad \nu(S_s)=\min(1,2\delta_s(\gamma)).
\tag{33.7}
$$

质量等式来自每个固定 $u$ 纤维中 $z_{i_s}$ 的均匀 Haar 分布，再对 $u$ 积分；不需要有限余类相互独立，也不要求该纤维中实际存在允许整数。原事件仍承担自身的全部有限条件；上包只使用其必然蕴含的模 $Q_s$ 信息。

由 (32.2) 及 $H_{s+2}=4H_s$，

$$
\frac{N_s}{Q_{s+2}}
\le2\exp\left(4H_s^2-\frac9{10}\,16H_s^2\right)
=2e^{-52H_s^2/5}\le e^{-10H_s^2}.
\tag{33.8}
$$

末步对 $H_s\ge7$ 成立。又 $H_s=2^sH_0$，所以对每个 $\gamma>0$ 都有 $\sum_s\delta_s(\gamma)<\infty$。

各 $\mathcal I_s$ 两两不交且有限，合起来恰为 $\{n:h(n)\ge H_0\}$；其补集为有限初段。因此无穷多个原整数命中必落入无穷多个这样的整段，$R(\omega)\subseteq\limsup_s S_s$。对每个 $S\ge0$，

$$
\nu(R(\omega))\le\nu\left(\bigcup_{s\ge S}S_s\right)
\le2\sum_{s\ge S}\delta_s(\gamma)\longrightarrow0.
\tag{33.9}
$$

这是收敛 Borel–Cantelli 的尾并集论证。整段内部允许原 $h$ 的所有中间值，左右边界以 $H_s\le h(n)<H_{s+1}$ 唯一分配；(33.5)–(33.7) 对每一个原整数成立，故全部跳点两侧、非好阶段及全部有限端纤维均已覆盖。定理 28.1 的 (28.4) 随即给出完整 $g_j\to0$，无需重新切分 dyadic 跳点。

**证明（完整共同中心的类别结论）。** 任一非空基本窗 $((b+d\widehat{\mathbb Z})\cap C_M)\times W$ 的有限端由 CRT 给出一个共同整数类 $t\pmod\ell$，其中 $\ell=\operatorname{lcm}(M,d)$。定理 32.2 的有理独立性使每个非零 $k$ 都满足 $\ell k\cdot\omega\notin\mathbb Z$，故经典 Kronecker 定理使 $(t+\ell m)\omega$ 的每条正尾在两圆中稠密。同一个整数的中心 $(n,n\omega)$ 因而在 $Y$ 中尾稠密，且属于自身的 $E_n(\omega)$。每个 $E_n(\omega)$ 开，原半径逐项严格为正，所以每个尾并集 $\bigcup_{n>N}E_n(\omega)$ 开且稠密。紧度量空间 $Y$ 上的 Baire 定理给出 $R(\omega)$ 为稠密 $G_\delta$。这是原定理 20.2、23.1 的共同中心论证对新方向的应用，类别结论不从零一律推得。

Haar 推前、Kronecker、Borel–Cantelli 与 Baire 均为经典中间输入（literature-attested）；其共同中心与文献接口沿用原定理 20.2、23.1。新增综合（repo-derived）是原周期交替截断与同一 $u$ 上良定义的有限实 character 相接，并以可求和整段覆盖完整原整数尾。此方向是比较 $\omega$，不是原 CM 点的实方向 $\alpha$。$\square$

## 34. 严格原阶段窗口、全方向几何发散与同一反模型

**定理 34.1（每个原负阶段的严格 dyadic 窗口下界）。** 固定任意 $\gamma>0$，取 $\beta=0,c_0=1$，保留原 $\mathcal H_- =\{H\ge7:\vartheta(H)<H\}$ 及 (28.2) 的完整权重。对每个充分大的 $H\in\mathcal H_-$，定义

$$
\mathcal D_H=\{j\in\mathbb Z:j\ge j_0,\quad
 H^2+H/2\le j\log2\le H^2+H\}.
\tag{34.1}
$$

这些窗口对不同整数 $H$ 两两不交，且存在 $c_\gamma>0$，使对所有比较方向 $\omega\in\mathbb T^2$ 同时有

$$
\#\mathcal D_H\ge\frac{H}{4\log2},\qquad
g_j(\omega)\ge(H+1)^{-4\gamma}\quad(j\in\mathcal D_H),\qquad
\boxed{\ \sum_{j\in\mathcal D_H}g_j(\omega)\ge c_\gamma H^{1-4\gamma}.\ }
\tag{34.2}
$$

充分大阈值可依赖原固定数据及 $\gamma$，不依赖方向；无须第二逐次极小的额外反共振前提。

**证明（整块处于原阶段且保留 floor 差）。** 定义 (34.1) 的实区间长度为 $H/(2\log2)$，故整数数至少为该长度减一，最终给出第一界。$H^2+H<(H+1)^2+(H+1)/2$，所以不同 $H$ 的窗口不交。若 $j\in\mathcal D_H$、$X=2^j$，则对整块的每个整数 $X<n\le2X$，

$$
H^2<\log(n+2)\le\log(2X+2)
\le j\log2+\log3\le H^2+H+\log3<(H+1)^2.
\tag{34.3}
$$

这里 $X\ge2$，且 $2X+2\le3X$。因此整块恰为原 $h=H$ 的一个完整片，不跨跳点。其原允许项数和几何尺度为

$$
J=\left\lfloor\frac{2X-a_0}{M}\right\rfloor
  -\left\lfloor\frac{X-a_0}{M}\right\rfloor,\qquad
|MJ-X|<M,\qquad K=\frac{MJ}{q_H}.
\tag{34.4}
$$

对充分大 $H$，统一有 $X\ge2M$，故 $MJ\ge X/2>0$。原 (16.26) 在负阶段给出 $q_H\le5M\exp((H-1)\vartheta(H))\le5M\exp(H^2-H)$。所以对窗口内全部 $j$，

$$
K\ge\frac1{10M}e^{3H/2},\qquad
r=r_j^-=[\log(2^{j+1}+2)]^{-\gamma}\ge(H+1)^{-2\gamma},\qquad
Kr^2\ge\frac1{10M}e^{3H/2}(H+1)^{-4\gamma}\longrightarrow\infty.
\tag{34.5}
$$

并且一致地 $r<1/4$、$K\ge r$ 最终成立。

**证明（方向无关的三因子下界）。** 对原对偶格 $L=\{(K(a'-q_Hk\cdot\omega),rk):a'\in\mathbb Z,k\in\mathbb Z^2\}$ 的任一非零向量，若 $k=0$，其长度至少为 $K$；若 $k\ne0$，其空间长度至少为 $r$。于是 $\lambda_1,\lambda_2\ge r$。由 (25.1)，$\det L=Kr^2\le\lambda_1\lambda_2\lambda_3\le\lambda_3^3$；(34.5) 使 $\lambda_3>1$ 最终成立。因此

$$
g_j(\omega)=p_{3,j}^-
=\min(1,\lambda_1)\min(1,\lambda_2)
\ge r^2\ge(H+1)^{-4\gamma}.
\tag{34.6}
$$

等号中的 $g_j$ 使用的就是整块唯一的真实非空片。将此式对 $\mathcal D_H$ 求和，并用 $H+1\le2H$，即得 (34.2)，例如可取 $c_\gamma=2^{-4\gamma}/(4\log2)$。本条复用原周期上界和本卷格的行列式比较，建立完整原 dyadic 权重的窗口估计；不将一般格论另立为新成果。$\square$

**定理 34.2（含端点的全方向完整几何权重发散）。** 对原对数端点的每个 $0<\gamma\le3/8$ 及每个方向 $\omega\in\mathbb T^2$，有

$$
\sum_{j\ge j_0}g_j(\omega)=\infty.
\tag{34.7}
$$

**证明。** 经典 Littlewood 输入的准确形式是 $\psi(x)-x=\Omega_-(\sqrt x\log\log\log x)$。Platt–Trudgian，*On the first sign change of $\theta(x)-x$*，[arXiv:1407.1914v1 原文](https://arxiv.org/pdf/1407.1914v1)，第 1 页式 (2)，给出更完整的 $\Omega_\pm$ 陈述；$\psi(x)=\sum_{p^m\le x}\log p$。这与原定理 21.2 使用的是同一经典输入，此处不重证或单列一般振荡定理。

因此存在固定 $c>0$ 和无界的实数 $x$，使 $\psi(x)\le x-c\sqrt x\,L(x)$，其中 $L(x)=\log\log\log x$。对这些充分大的 $x$ 置 $\ell=(c/2)\sqrt x\,L(x)$。每个整数 $H\in[x-\ell,x]$ 都满足

$$
\vartheta(H)\le\psi(H)\le\psi(x)\le x-2\ell<H.
\tag{34.8}
$$

所以这些整数均为原负阶段。它们的数量至少为 $\ell-1\ge(c/4)\sqrt x\,L(x)$，且因 $\ell=o(x)$ 而一致地 $x/2\le H\le x$。这里取的是负点之前的区间，只使用 $\psi$ 的单调性，没有向前素数跳跃界。

令 $J(x)=\lfloor(x^2+x)/\log2\rfloor$。上述每个 $\mathcal D_H$ 都包含于 $[j_0,J(x)]$，这些窗口两两不交。对固定 $\gamma$，在 $H\in[x/2,x]$ 上 $H^{1-4\gamma}\ge c'_\gamma x^{1-4\gamma}$，其中 $c'_\gamma>0$。逐窗口复用定理 34.1 的 (34.2)，得到与方向无关的部分和下界

$$
\begin{aligned}
\sum_{j=j_0}^{J(x)}g_j(\omega)
&\ge\sum_{\substack{H\in\mathbb Z\\x-\ell\le H\le x}}
       \sum_{j\in\mathcal D_H}g_j(\omega)\\
&\ge C_\gamma x^{3/2-4\gamma}\log\log\log x,
\qquad C_\gamma>0.
\end{aligned}
\tag{34.9}
$$

当 $0<\gamma<3/8$ 时，幂指数严格正；当 $\gamma=3/8$ 时，剩余的 $\log\log\log x$ 仍趋于无穷。非负项的部分和因而无界，证明 (34.7)。不需要不同负点 $x$ 所给区间相互不交：每次都只是对同一正项部分和作下界，而同一次下界内部的 $\mathcal D_H$ 已两两不交。对 $\gamma>3/8$，(34.9) 不裁定完整级数的敛散。

新增综合（repo-derived）是将 Littlewood 负幅度转为原负阶段的同时计数，并让每个阶段消费 (34.2) 的严格窗口下界；Littlewood、单调性与正项部分和比较均只作中间输入。$\square$

**定理 34.3（同一个有限型方向的趋零、发散与完整零测）。** 对定义 32.1 的同一个固定方向，(32.6) 的常数及指数均不依赖 $\gamma$。对每个 $0<\gamma\le3/8$，原完整比较族同时满足

$$
\boxed{\quad g_j(\omega)\to0,\qquad
\sum_{j\ge j_0}g_j(\omega)=\infty,\qquad
\nu(R(\omega))=0.\quad}
\tag{34.10}
$$

$R(\omega)$ 仍是稠密 $G_\delta$，而原逐整数一阶质量仍满足 $\sum_n\nu(E_n(\omega))=\infty$。完整零测与 $g_j\to0$ 本身对全部 $\gamma>0$ 成立。

**证明。** 定理 32.2 已在全部整数频率上给出有限型与有理独立。定理 33.2 对每个 $\gamma>0$ 给出完整零测、类别结论及 $g_j\to0$；定理 34.2 的全方向发散可以用于这个同一方向，得到 (34.10)。原定理 21.2 的准确质量在比较族中与方向无关，见原 (22.2) 及定理 23.1 的质量论证，故原一阶级数仍发散。没有从一阶发散推导几何发散；后者由 (34.2)、(34.8)–(34.9) 独立支付。

这些结论表明，在声明的 $\gamma$ 范围内，即使有统一有限型及完整几何权重和发散，完整原比较事件仍可零测；跨段重复覆盖所需的联合信息不能由这些条件替代。整个构造保留原有限地方、原 $q_H,h,\rho,M,a_0,Y$ 与同一整数，辅助 $H_s,N_s$ 只服务固定比较方向及其上包。该 $\omega$ 没有被认作实际 CM 方向 $\alpha$；原 (17.5) 的 CM 来源桥和实际 $q_H$ 与 $\alpha$ 的联合算术问题仍保留，以上反模型不裁定 $g_j(\alpha)$ 或 $\nu(R(\alpha))$。$\square$

## 追加锚（本行以下为增补区）

## 35. 原负阶段整数计数与严格 dyadic 阶段的几何权重

**定义 35.1（原对数过滤及其负阶段）。** 保持定义 24.1 的全部有限地方过滤、实际共同周期 $q_H$、整数 $M,a_0$、完整目标空间 $Y$、测度 $\nu$ 与同一成功整数，只取 $\beta=0,c_0=1,\gamma>0$。因此仍用原来的

$$
h(n)=\max\left(2,\left\lfloor\sqrt{\log(n+2)}\right\rfloor\right),
\qquad \rho_\gamma(n)=(\log(n+2))^{-\gamma}.
$$

将 (28.1)–(28.2) 中的原量显式记为 $R_\gamma(\omega)$、$g_j^{(\gamma)}(\omega)$ 与 $r_{j,\gamma}^{\pm}$；每片仍使用真实整数个数 $J_{jt}=\#(I_{jt}\cap A)$ 及 $K_{jt}=MJ_{jt}/q_{H_{jt}}$。这只是显示参数，不改变事件、切片、半径或几何权重的定义。对每个 $\gamma>0$，$j_0$ 按定理 28.1 选择，且不依赖方向。沿用原定义 21.1 的全部整数负阶段，并记

$$
\begin{gathered}
\vartheta(x)=\sum_{p\le x}\log p,
\qquad \psi(x)=\sum_{\substack{p\text{ 素数},\ k\ge1\\p^k\le x}}\log p,\\
\mathcal H_- =\{H\in\mathbb Z:H\ge7,\ \vartheta(H)<H\},
\qquad A_-(T)=\#\{H\in\mathcal H_-:H\le T\}.
\end{gathered}
\tag{35.1}
$$

严格窗口 $\mathcal D_H$ 始终取定理 34.1 的 (34.1)，其不交性与窗口下界直接使用 (34.2)。以整数 $H_0(\gamma)\ge7$、$c_\gamma>0$ 表示该定理的充分大阈值与常数，二者均不依赖方向。这里只将原负阶段的整数计数接到该严格窗口的原权重上。

**定理 35.2（原完整几何权重的全方向发散）。** 对定义 35.1 的原过滤，无条件有

$$
\forall\gamma\in(0,1/2)\ \forall\omega\in\mathbb T^2,
\qquad \sum_{j\ge j_0}g_j^{(\gamma)}(\omega)=\infty.
\tag{35.2}
$$

若假设 Riemann 假设（RH），还在端点有

$$
\forall\omega\in\mathbb T^2,
\qquad \sum_{j\ge j_0}g_j^{(1/2)}(\omega)=\infty.
\tag{35.3}
$$

RH 端点不另假设零点的线性独立性或简单性。

证明。所用整数计数来自 Jerzy Kaczorowski，*Results on the distribution of primes*，J. reine angew. Math. **446** (1994)，89–113，[DOI:10.1515/crll.1994.446.89](https://doi.org/10.1515/crll.1994.446.89)，[原始扫描](https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0446/LOG_0007.pdf)。该文 §3，印刷页 94，Theorem 8 的负向 $\psi$ 计数是：对每个 $0<\varepsilon<1$ 和每个实数 $u\ge0$，无条件有

$$
\#\{m\in\mathbb N:m\le T,\ \psi(m)<m-u\sqrt m\}
=\Omega(T^{1-\varepsilon}).
\tag{35.4}
$$

这是 literature-attested 的中间输入。这里只取 $u=0$，并只使用其下述含义：存在 $a_\varepsilon>0$ 和一个无界序列 $T_\ell\to\infty$，使该计数至少为 $a_\varepsilon T_\ell^{1-\varepsilon}$。因 $\vartheta(H)\le\psi(H)$，每个整数 $H\ge7$ 若满足 $\psi(H)<H$，就是同一个原负阶段 $H\in\mathcal H_-$。丢弃 $H<7$ 的至多六项并缩小常数，得到

$$
A_-(T_\ell)\ge a'_\varepsilon T_\ell^{1-\varepsilon}
\qquad(\ell\text{ 充分大}),\qquad a'_\varepsilon>0.
\tag{35.5}
$$

不把 (35.5) 加强为对全部充分大 $T$ 的同一幂次下界。

对 $0<\gamma\le3/8$，全方向发散已由定理 34.2 给出，直接复用该结论。现取 $3/8<\gamma<1/2$，置 $s=4\gamma-1\in(1/2,1)$，并选 $0<\varepsilon<1-s$。由于 $H^{-s}\ge T_\ell^{-s}$ 对 $H\le T_\ell$ 成立，(35.5) 给出

$$
\begin{aligned}
\sum_{\substack{H\in\mathcal H_-\\H_0(\gamma)\le H\le T_\ell}}
 H^{1-4\gamma}
&\ge T_\ell^{-s}
 \bigl(A_-(T_\ell)-A_-(H_0(\gamma)-1)\bigr)\\
&\ge \frac{a'_\varepsilon}{2}
 T_\ell^{1-s-\varepsilon}\longrightarrow\infty.
\end{aligned}
\tag{35.6}
$$

此处只在 $s>0$ 的范围使用 $H^{-s}\ge T_\ell^{-s}$，不将这一不等式套用到 $s\le0$。

由非负性、定理 34.1 的窗口互不重叠及 (34.2)，对每个方向同时有

$$
\sum_{j\ge j_0}g_j^{(\gamma)}(\omega)
\ge\sum_{\substack{H\in\mathcal H_-\\H\ge H_0(\gamma)}}
 \sum_{j\in\mathcal D_H}g_j^{(\gamma)}(\omega)
\ge c_\gamma
 \sum_{\substack{H\in\mathcal H_-\\H\ge H_0(\gamma)}}H^{1-4\gamma}
=\infty.
\tag{35.7}
$$

这证明 (35.2)。用白话说，无条件计数只需在越来越远的位置积累足够多的负阶段整数；每项所付的负幂还不到谐和幂，因此这些位置上的累积下界已迫使总和发散。窗口不重叠使每份贡献只记一次，且同一估计对所有实方向有效。

端点另用同文 §2，印刷页 90，Theorem 1。其负向 $\psi$ 陈述仅以 RH 为假设：对每个实数 $u\ge0$，存在 $C_{\mathrm K}(u)>1$、$b_{\mathrm K}(u)>0$，使每个 $T\ge1$ 都有

$$
\#\{m\in\mathbb N:T\le m\le C_{\mathrm K}(u)T,
 \ \psi(m)<m-u\sqrt m\}
\ge b_{\mathrm K}(u)T.
\tag{35.8}
$$

这里 $C_{\mathrm K}(u)$ 是原文的区间伸缩常数，与原过滤中固定为 $1$ 的 $c_0$ 无关。(35.8) 同样仅作 literature-attested 中间输入；取 $u=0$，简记 $C=C_{\mathrm K}(0)$、$b=b_{\mathrm K}(0)$，再取 $T=N/C$，便在 $N\ge C$ 时得到

$$
A_-(N)\ge\frac bC N-6.
\tag{35.9}
$$

因此存在 $a>0$、$N_0\ge7$，使全部 $N\ge N_0$ 满足 $A_-(N)\ge aN$。对这个原整数计数作普通部分求和，得

$$
\sum_{\substack{H\in\mathcal H_-\\H\le N}}\frac1H
=\frac{A_-(N)}N+\int_1^N\frac{A_-(t)}{t^2}\,dt
\ge a\log\frac N{N_0}\longrightarrow\infty.
\tag{35.10}
$$

删去有限初段不改变发散。将 $\gamma=1/2$ 的 $H^{1-4\gamma}=1/H$ 及 (35.10) 代入 (35.7) 的窗口求和不等式，便得 (35.3)。普通正项求和及部分求和均为经典中间方法（literature-attested）；这里的 repo-derived 综合是将上述原文整数计数转接到指定原过滤的严格 dyadic 窗口与完整 $g_j$，不另立一般振荡或求和定理。

用白话说，RH 给出的每个伸缩区间内线性个数下界，使负阶段整数集具有正下密度，因而能承担恰好一阶的谐和权重。无条件的 (35.5) 在 $s=1$ 时不能给出 (35.6) 中的正指数；本证明留下 $\gamma=1/2$ 的无条件发散未决，也不由此断言 RH 必要。$\square$

## 36. 零方向的完整收敛界与全方向命题的上界

**定理 36.1（原完整几何权重在零方向的可求和范围）。** 保持定义 35.1 的原过滤。对每个 $\gamma>1/2$，零方向 $0=(0,0)$ 满足

$$
\begin{gathered}
0\le g_j^{(\gamma)}(0)
\le(r_{j,\gamma}^-)^2
=\bigl(\log(2^{j+1}+2)\bigr)^{-2\gamma},\\
\sum_{j\ge J}g_j^{(\gamma)}(0)
\le\frac{(\log2)^{-2\gamma}}{2\gamma-1}\,J^{1-2\gamma}
\qquad(J\ge\max(j_0,1)),\\
\sum_{j\ge j_0}g_j^{(\gamma)}(0)<\infty,
\qquad \nu(R_\gamma(0))=0.
\end{gathered}
\tag{36.1}
$$

因此任何 $\gamma>1/2$ 都不满足“对所有方向 $\omega$，原 $\sum_jg_j^{(\gamma)}(\omega)$ 发散”。

证明。每个真实保留片在零方向的准确公式由定理 27.1 给出：

$$
p_{3,jt}^-(0)=\min(1,K_{jt})(r_{j,\gamma}^-)^2.
$$

同一 dyadic 块的各片使用同一个 $r_{j,\gamma}^-$，所以按 (28.2) 取最大值，即有 $g_j^{(\gamma)}(0)\le(r_{j,\gamma}^-)^2$；没有保留片时，空最大值为零，估计仍成立。原半径在 $\beta=0$ 下准确等于 (36.1) 第一行，并且该平方与 $j^{-2\gamma}$ 同阶。由 $\log(2^{j+1}+2)\ge(j+1)\log2$，普通正项积分比较给出

$$
\begin{aligned}
\sum_{j\ge J}g_j^{(\gamma)}(0)
&\le(\log2)^{-2\gamma}\sum_{j\ge J}(j+1)^{-2\gamma}\\
&\le(\log2)^{-2\gamma}\int_J^\infty x^{-2\gamma}\,dx
=\frac{(\log2)^{-2\gamma}}{2\gamma-1}J^{1-2\gamma}.
\end{aligned}
\tag{36.2}
$$

加回有限初段即得完整级数收敛，(28.4) 随即给出完整 $R_\gamma(0)$ 零测。这里的原过滤上界比较为 repo-derived，格的准确公式直接复用定理 27.1；一般格论及正项积分比较均为 literature-attested 中间方法。

用白话说，零方向的全部实中心重合，允许整数再多也只贡献同一半径的方块；三因子乘积因而至多是这个半径的平方。平方半径在 dyadic 指标上成为 $j^{-2\gamma}$，超过半端点就可求和。

零方向不满足 (29.1) 的有限型条件，且 $1,0,0$ 在 $\mathbb Q$ 上线性相关。本条给出的是全方向发散命题不能越过 $1/2$ 的上界，不给有限型方向类或实际 CM 方向 $\alpha$ 的锐界。结合定理 35.2，在 RH 下全方向几何权重发散的参数范围恰为 $0<\gamma\le1/2$；无条件端点仍未由这些输入判定。$\square$

## 37. 同一固定有限型方向上的发散与完整零测

**定理 37.1（固定有限型零测方向的几何发散消费者）。** 令 $\omega_*$ 为定义 32.1 中 (32.5) 给出的同一个固定方向。定理 32.2 的 (32.6) 保证它满足 (29.1)，且方向、有限型常数与指数均不依赖 $\gamma$。在定义 35.1 的同一原过滤中，定理 33.2 已给出

$$
\forall\gamma>0,\qquad \nu(R_\gamma(\omega_*))=0.
\tag{37.1}
$$

这个方向无条件同时满足

$$
\forall\gamma\in(0,1/2),\qquad
\left\{
\begin{aligned}
g_j^{(\gamma)}(\omega_*)&\longrightarrow0,\\
\sum_{j\ge j_0}g_j^{(\gamma)}(\omega_*)&=\infty,\\
\nu(R_\gamma(\omega_*))&=0.
\end{aligned}
\right.
\tag{37.2}
$$

在 RH 下，同一个 $\omega_*$ 还使 (37.2) 在 $\gamma=1/2$ 成立。方向、有限型性及对全部 $\gamma>0$ 的完整零测性分别直接复用定义 32.1、定理 32.2 与定理 33.2，没有额外的方向存在性假设。

证明。固定任意 $\gamma>0$，定理 33.2 直接给出 (37.1) 与 $g_j^{(\gamma)}(\omega_*)\to0$。对 $0<\gamma<1/2$，定理 35.2 的全方向结论直接给同一个 $\omega_*$ 上的级数发散；RH 下再用其端点结论。此处每个 $\gamma$ 都在同一原目标空间及同一固定方向上取值，不随 $\gamma$ 另选方向。于是 (37.2) 完整成立。$\square$

用白话说，原几何权重的总量可以无穷，每块的权重又可以趋零，而同一个有限型方向的完整无限命中集合仍是零测。故即使保留有限型与共同成功整数，也不能只从 $\sum_jg_j=\infty$ 推出满测。本条是定理 32.2、33.2 与 35.2 的原过滤消费者（repo-derived），不新增一般格论或 Borel–Cantelli 定理。

对实际 $\omega=\alpha$，定理 35.2 同样提供无条件严格区间内的级数发散及 RH 下的半端点发散；本条的 $\omega_*$ 不被认作 $\alpha$。实际 $\alpha$ 是否具有足以裁定 $\nu(R_\gamma(\alpha))$ 的跨块联合控制或相应凝聚发散条件，仍是未决桥。

## 追加锚（本行以下为增补区）

## 38. 原完整比较族的共同最小预算与真实块测度

**定义 38.1（全部真实片上的标量预算）。** 保持定义 24.1 的实际 CM 数据、全部原有限地方、实际周期 $q_H=q(H,H;M)$、原 $h,\rho,M,a_0,A,C_M,Y,\nu$，以及 (28.1) 的同一成功整数事件。比较方向 $\omega\in\mathbb T^2$ 只替换实中心，不替换有限过滤或指定的 CM 方向 $\alpha$。沿用定理 28.1 的完整分块、$U_j(\omega)$、$r_j^\pm$、$C_\rho=2^{\beta+\gamma}$ 及 $g_j(\omega)$。若真实同阶段片为 $I_{jt}=(A_{jt},B_{jt}]\cap\mathbb Z$，仍取

$$
J_{jt}=\left\lfloor\frac{B_{jt}-a_0}{M}\right\rfloor
       -\left\lfloor\frac{A_{jt}-a_0}{M}\right\rfloor,
\qquad Q_{jt}=q_{H_{jt}},\qquad K_{jt}=\frac{MJ_{jt}}{Q_{jt}}.
\tag{38.1}
$$

$J_{jt}=0$ 的片贡献零；只在 $J_{jt}>0$ 时使用原格及其 $p_{3,jt}^-(\omega)$。置

$$
s_j=(r_j^-)^2\max_t\min\{1,K_{jt}\},
\qquad \mathscr S=\sum_{j\ge j_0}s_j,
\tag{38.2}
$$

空最大值为零。每个 $j\ge j_0$ 至多两片，且 $r_j^+<1/4$。所有 $J$ 均为真实整数，不以片的实数长度替代。

**定理 38.2（同一个零方向逐片实现共同锐下包）。** 对任意 $K>0$、$0<r<1/4$、原整数周期 $Q$ 与任意 $\omega\in\mathbb T^2$，原形状的格

$$
L(\omega)=\{(K(a-Qk\cdot\omega),rk):a\in\mathbb Z,\ k\in\mathbb Z^2\}
$$

满足

$$
\boxed{\quad
p_3(\omega)=\prod_{i=1}^3\min\{1,\lambda_i(L(\omega))\}
\ge\min\{1,K\}r^2=p_3(0).
\quad}
\tag{38.3}
$$

因此对全部真实片、全部 $j\ge j_0$，同一个固定方向 $0=(0,0)$ 给出

$$
g_j(\omega)\ge g_j(0)=s_j,
\qquad
\boxed{\quad
\left[\forall\omega\in\mathbb T^2:\sum_{j\ge j_0}g_j(\omega)=\infty\right]
\iff \mathscr S=\infty.
\quad}
\tag{38.4}
$$

证明。只将本卷 (25.1)、(25.13)–(25.14) 的整数子式比较用作中间输入。任意非零格向量在 $k=0$ 时长度至少为 $K$，在 $k\ne0$ 时空间长度至少为 $r$，故

$$\lambda_1\ge\min\{K,r\}.\tag{38.5}$$

取达到前两条极小的独立向量 $v_i=(K(a_i-Qk_i\cdot\omega),rk_i)$。若 $k_1,k_2$ 独立，外积的纯空间分量是非零整数乘 $r^2$；若它们相关，包括其中一个为零的情形，(25.13) 的剪切抵消给出混合分量 $Kr(a_1k_2-a_2k_1)$。因 $v_1,v_2$ 独立，后一整数向量非零。因此

$$
\lambda_1\lambda_2\ge\|v_1\wedge v_2\|_2
\ge\min\{r^2,Kr\},\qquad
\lambda_1\lambda_2\lambda_3\ge\det L=Kr^2.
\tag{38.6}
$$

最后一式直接复用 (25.1)。令 $m=\#\{i:\lambda_i<1\}$。截断乘积在 $m=0,1,2,3$ 时，分别不小于

$$
1,\qquad \min\{K,r\},\qquad \min\{r^2,Kr\},\qquad Kr^2.
$$

因为 $r<1$，这四个量都不小于 $\min\{1,K\}r^2$。长度恰为 $1$ 的因子归入未截短部分，故阈值边界也已包括。零方向的等号直接由定理 27.1 的正交直积公式取得；不要求 $K\ge1$ 或 $Kr^2\ge1$。

逐片代入 $r=r_j^-$ 后取最大值，得 $g_j(\omega)\ge s_j=g_j(0)$，空片的零项不改变此式。若 $\mathscr S$ 发散，则逐项比较给出每个固定方向的发散；反向只需在全称量词中取同一个方向 $0$。没有逐块选择再拼接方向。$\square$

用白话说，把所有实中心放在零点的同一个方向，同时使每片的三因子权重最小。全方向发散问题因此准确等价于这一个共同最坏方向的标量预算。

**定理 38.3（原完整块真实测度的共同最小性）。** 对定义 38.1 的完整事件并，有

$$
\boxed{\quad
\nu(U_j(\omega))\ge\nu(U_j(0)),\qquad
4s_j\le\nu(U_j(0))\le8C_\rho^2s_j
\quad(j\ge j_0).
\quad}
\tag{38.7}
$$

这是同一有限纤维上的测度比较，不是不同方向事件之间的集合包含。

证明。固定 $u\in C_M$，在同一个完整块中定义准确允许集合

$$
\mathcal N_j(u)=\{n\in A:2^j<n\le2^{j+1},\ u\equiv n\pmod{q_{h(n)}}\}.
\tag{38.8}
$$

它与 $\omega$ 无关。它只依赖 $u$ 在该块全部 $Q_{jt}$ 的最小公倍数下的剩余类，因而给出了可供所有方向共用的有限纤维分割。若它为空，则所有方向的该纤维均为空。否则令 $n_*(u)=\min\mathcal N_j(u)$。由于 $\rho$ 递减，零方向的该纤维准确等于最大窗，而任意方向的同一纤维至少含这个整数的一次平移窗：

$$
\begin{aligned}
\{z:(u,z)\in U_j(0)\}&=\mathcal B_{\rho(n_*(u))}(0),\\
\{z:(u,z)\in U_j(\omega)\}&\supseteq
\mathcal B_{\rho(n_*(u))}(n_*(u)\omega).
\end{aligned}
\tag{38.9}
$$

两个所列窗的 Haar 面积均为 $4\rho(n_*(u))^2$。故逐同一纤维的面积不等式成立，积分得 (38.7) 的第一式；这里没有比较两个不同中心窗的包含关系。每次有限端和两个实端仍由同一个 $n_*(u)$ 承担。

再令 $U_{jt}(\omega)=\bigcup_{n\in I_{jt}}E_n(\omega)$。在一个真实片内，$n\in I_{jt}\cap A$ 对应连续的 $J_{jt}$ 个整数 $(n-a_0)/M$，其模 $Q_{jt}/M$ 的不同剩余类准确有

$$
\min\{J_{jt},Q_{jt}/M\}
$$

个。每个有限柱在 $C_M$ 中的归一化测度为 $M/Q_{jt}$，故非空纤维的总比例准确为 $\min\{1,K_{jt}\}$。在每个这样的纤维上，零方向的最大窗半径仍位于 $[r_j^-,r_j^+]$，所以

$$
4(r_j^-)^2\min\{1,K_{jt}\}
\le\nu(U_{jt}(0))
\le4(r_j^+)^2\min\{1,K_{jt}\}.
\tag{38.10}
$$

$J_{jt}=0$ 时两端及事件测度均为零，故空片已包括。对完整块，下界取任一片的测度再取最大值，上界用至多两片的并集界；由 $r_j^+\le C_\rho r_j^-$，即得 $4s_j$ 和 $8C_\rho^2s_j$。片之间可以重叠，不把下界相加。$\square$

用白话说，固定一把有限端钥匙后，零方向把它允许的所有窗重叠在最大窗内，因而面积最小。移动中心至少还保留其中一个同样大的窗。真实块测度的共同最坏总量，与 (38.2) 的标量预算只差固定倍数。

## 39. 保留 floor、空片及两端短片的完整阶段积分

**定义 39.1（准确完整阶段及阶段截断预算）。** 取原对数半径 $\beta=0,c_0=1,\gamma>0$，其余数据保持定义 38.1。对整数 $H\ge3$ 置

$$
\begin{gathered}
A_H=e^{H^2},\qquad B_H=e^{(H+1)^2},\qquad \ell_H=2H+1,\\
u_H=\lceil A_H\rceil-3,\qquad v_H=\lceil B_H\rceil-3.
\end{gathered}
$$

于是准确完整阶段是

$$
\{n\ge1:h(n)=H\}
=(u_H,v_H]\cap\mathbb Z
=\{n\in\mathbb Z:A_H\le n+2<B_H\}.
\tag{39.1}
$$

令 $X_j=2^j$、$a_{Hj}=\max\{X_j,u_H\}$、$b_{Hj}=\min\{2X_j,v_H\}$，并令

$$
J_{Hj}=
\begin{cases}
\left\lfloor\dfrac{b_{Hj}-a_0}{M}\right\rfloor
-\left\lfloor\dfrac{a_{Hj}-a_0}{M}\right\rfloor,&b_{Hj}>a_{Hj},\\
0,&b_{Hj}\le a_{Hj}.
\end{cases}
\tag{39.2}
$$

对 $q>0$、$x\ge0$ 记 $f_q(x)=\min\{1,x/q\}$。阶段和、实际相位及积分为

$$
\begin{gathered}
D_H=\sum_{j\ge j_0}f_{q_H}(MJ_{Hj}),\qquad
\Xi_H=(H+1)^2-\log q_H,\\
\Phi_\ell(x)=\int_0^\ell\min\{1,e^{x-s}\}\,ds\quad(\ell>0),\\
\Phi_H=\int_{A_H}^{B_H}f_{q_H}(x)\,\frac{dx}{x}
=\Phi_{\ell_H}(\Xi_H).
\end{gathered}
\tag{39.3}
$$

最后一个等式由 $s=\log(B_H/x)$ 得到。对完整阶段范围 $H_0\le H\le H_1$，定义原标量预算的阶段截断

$$
\mathscr S_{H_0,H_1}
=\sum_{j\ge j_0}(\log(2^{j+1}+2))^{-2\gamma}
\max_{H_0\le H\le H_1}f_{q_H}(MJ_{Hj}).
\tag{39.4}
$$

跨阶段块中属于所选范围的真实片全部保留；每个最大值至多两个非零项。

**定理 39.2（完整阶段截断的统一双边比较）。** 存在仅依赖原固定数据、$\gamma$ 及初始分块的整数 $H_0\ge3$，使任意 $H_1\ge H_0$ 都有

$$
\boxed{\quad
c_\gamma\sum_{H=H_0}^{H_1}H^{-4\gamma}\Phi_{2H+1}(\Xi_H)
\le\mathscr S_{H_0,H_1}
\le C_\gamma\sum_{H=H_0}^{H_1}H^{-4\gamma}\Phi_{2H+1}(\Xi_H),
\quad}
\tag{39.5}
$$

例如可取

$$
c_\gamma=\frac{4^{-2\gamma}}{360\log2},\qquad
C_\gamma=\frac{35}{\log2}.
\tag{39.6}
$$

阶段和与积分的比较对任意 $q>0$ 一致，不借实际周期的增长渐近式。故 $\mathscr S$ 与 $\sum_{H\ge H_0}H^{-4\gamma}\Phi_{2H+1}(\Xi_H)$ 同敛散，完整截断的含义准确为 (39.4)–(39.5)。

证明。先在整数区间 $(u,v]$ 上比较，取 $u\ge2M$、$v\ge16u$，并使所有相交块均处于 $j\ge j_0$。记 $\mathcal F$ 为完全包含于该区间的 dyadic 块指标，置

$$
F=\sum_{j\in\mathcal F}f_q(X_j).
$$

取满足 $2X_*\le v$ 的最大 dyadic 数 $X_*$，则 $v/4<X_*\le v/2$ 且 $X_*>4u$，故该整块属于 $\mathcal F$。每个完全块的准确允许项数满足 $|MJ-X_j|<M$，因而

$$
\tfrac12 f_q(X_j)\le f_q(MJ)\le\tfrac32 f_q(X_j).
\tag{39.7}
$$

除完全块外，至多还有两个由区间端点切出的短片。每个相交短片的所在块满足 $X_j>u/2\ge M$、$X_j<v<4X_*$。若真实片长为 $T\le X_j$，则准确 floor 差给 $MJ<T+M\le2X_j$；利用 $f_q(cx)\le cf_q(x)$（$c\ge1$），得到

$$
f_q(MJ)\le2f_q(X_j)\le8f_q(X_*).
\tag{39.8}
$$

$J=0$ 时该项为零。因此包括所有空片及两端短片的真实和 $D(u,v;q)$ 满足

$$
\tfrac12 F\le D(u,v;q)\le\tfrac{35}{2}F.
\tag{39.9}
$$

每个完全块的积分满足

$$
(\log2)f_q(X_j)\le\int_{X_j}^{2X_j}f_q(x)\,\frac{dx}{x}
\le2(\log2)f_q(X_j).
$$

每个短片的积分不超过 $2(\log2)f_q(X_j)\le8(\log2)f_q(X_*)$。故

$$
(\log2)F\le\int_u^v f_q(x)\,\frac{dx}{x}\le18(\log2)F,
$$

从而对全部 $q>0$ 统一有

$$
\frac1{36\log2}\int_u^v f_q(x)\,\frac{dx}{x}
\le D(u,v;q)
\le\frac{35}{2\log2}\int_u^v f_q(x)\,\frac{dx}{x}.
\tag{39.10}
$$

取 $u=u_H,v=v_H$。充分大 $H$ 一致满足上述条件，并有 $A_H/2\le u_H\le A_H$、$B_H/2\le v_H\le B_H$、$B_H\ge4A_H$。下端增加的积分满足

$$
\int_{A_H/2}^{A_H}f_q(x)\,\frac{dx}{x}
\le\int_{A_H}^{2A_H}f_q(x)\,\frac{dx}{x},
$$

所以 $\int_{u_H}^{v_H}f_q(x)\,dx/x\le2\int_{A_H}^{B_H}f_q(x)\,dx/x$。另一方面，$[A_H,B_H/2]\subset[u_H,v_H]$，且

$$
\int_{B_H/2}^{B_H}f_q(x)\,\frac{dx}{x}
\le4\int_{B_H/4}^{B_H/2}f_q(x)\,\frac{dx}{x}.
$$

因此 $\int_{u_H}^{v_H}f_q(x)\,dx/x$ 至少为 $\int_{A_H}^{B_H}f_q(x)\,dx/x$ 的 $1/5$。在 (39.10) 中取实际 $q=q_H$，即得

$$
\frac1{180\log2}\Phi_H\le D_H\le\frac{35}{\log2}\Phi_H.
\tag{39.11}
$$

此估计保留准确 floor 差；即使 $q\gg B_H$，两端短片仍由本阶段内的真实完整块支付，没有引入与 $B_H/q$ 无关的加性误差。

若 $J_{Hj}>0$，从该真实片取任一允许整数 $n$。由 $X_j<n\le2X_j$ 及 (39.1)，有

$$
H^2\le\log(2X_j+2)<(H+1)^2+\log2\le4H^2
\qquad(H\ge2).
$$

所以同一 dyadic 半径满足

$$
4^{-2\gamma}H^{-4\gamma}\le(r_j^-)^2\le H^{-4\gamma}.
\tag{39.12}
$$

令 $\mathscr D_{H_0,H_1}$ 为将 (39.4) 中最大值换成片之和所得的量。定理 28.1 的至多两片给出

$$
\tfrac12\mathscr D_{H_0,H_1}\le\mathscr S_{H_0,H_1}
\le\mathscr D_{H_0,H_1}.
\tag{39.13}
$$

有限阶段范围只含有限个整数、只交有限个块，故可准确重排为逐阶段求和。用 (39.11)–(39.12) 即得 (39.5)–(39.6)。令 $H_1\to\infty$，非负项单调极限保留比较；删去 $H<H_0$ 或初始块只改变有限项。没有删去无限族跨阶段短片。$\square$

用白话说，每个完整阶段中，低于周期的尺度按“长度除以周期”计费，超过周期的尺度每块封顶为一。阶段积分把这两段连起来，原半径平方再给出 $H^{-4\gamma}$。两端即使很短，也被同阶段内的大整块统一控制，不能为每条边界另记一个固定成本。

## 40. 原实际周期相位的半端点敛散判据

**定理 40.1（完整预算的截断相位及半端点判据）。** 对定义 39.1 的原实际 $q_H$，令

$$
\eta_H=\min\left\{1,\frac{(\Xi_H)_+}{2H+1}\right\},
\qquad x_+=\max\{x,0\}.
\tag{40.1}
$$

阶段积分的准确三段公式是

$$
\Phi_\ell(x)=
\begin{cases}
e^x(1-e^{-\ell}),&x\le0,\\
x+1-e^{x-\ell},&0\le x\le\ell,\\
\ell,&x\ge\ell.
\end{cases}
\qquad
0\le\Phi_\ell(x)-\min\{\ell,x_+\}\le1.
\tag{40.2}
$$

在原过滤中，对每个 $\gamma>1/4$ 有

$$
\mathscr S<\infty
\iff\sum_{H\ge H_0}H^{1-4\gamma}\eta_H<\infty,
\tag{40.3}
$$

以及

$$
\left[\forall\omega\in\mathbb T^2:\sum_jg_j^{(\gamma)}(\omega)=\infty\right]
\iff\sum_{H\ge H_0}H^{1-4\gamma}\eta_H=\infty.
\tag{40.4}
$$

特别地，在半端点 $\gamma=1/2$，

$$
\boxed{\quad
\left[\forall\omega\in\mathbb T^2:\sum_jg_j^{(1/2)}(\omega)=\infty\right]
\iff\sum_{H\ge H_0}\frac{\eta_H}{H}=\infty.
\quad}
\tag{40.5}
$$

证明。(40.2) 的三段分别把积分按 $s=x$ 处分开，或在整个 $[0,\ell]$ 上处于同一分支。$x=0,\ell$ 处两种公式相等。在 $x\le0$、$0\le x\le\ell$、$x\ge\ell$ 时，减去 $\min\{\ell,x_+\}$ 的余量依次为

$$
e^x(1-e^{-\ell}),\qquad 1-e^{x-\ell},\qquad 0,
$$

均在 $[0,1]$ 内。故

$$
0\le\sum_{H\ge H_0}H^{-4\gamma}
\left(\Phi_{2H+1}(\Xi_H)-(2H+1)\eta_H\right)
\le\sum_{H\ge H_0}H^{-4\gamma}<\infty
\quad(\gamma>1/4).
\tag{40.6}
$$

又 $2/H\le(2H+1)/H^2\le3/H$，等价地 $2H\le2H+1\le3H$。定理 39.2 因而给出 (40.3)，定理 38.2 再给出 (40.4)–(40.5)。这是共同零方向的敛散等价；(40.3) 不声称每个其他方向的级数同时收敛。

$\gamma>1/4$ 是仅凭 (40.2) 的统一误差界删去可求和误差的精确条件。对于不限制相位的统一结论，取 $x_H=0,\ell_H=2H+1$，余量为 $1-e^{-(2H+1)}\ge1-e^{-1}$，故其加权和在 $0<\gamma\le1/4$ 发散。这个检验只说明统一误差论证的阈值；没有将原实际周期替换成此相位，也不声称实际 $q_H$ 在该范围内的余量必不可求和。$\square$

用白话说，$\Xi_H$ 记录完整阶段右端相对实际周期的对数余量，$\eta_H$ 则是该阶段有多少比例已经超过周期。半端点恰好按 $1/H$ 给这个比例加权，在这个端点上，积分中尚未越过周期的指数尾部只留下一个可求和误差。

**原算术身份在 (40.5) 中的参数对应。** 以下直接展开原卷 002 (16.33)，不另立一般算术定理。越过原 (16.32) 对固定 $M$ 的阈值 $H_M$ 后，实际周期准确满足

$$
\begin{aligned}
\log q_H
={}&(H-1)(\vartheta(H)-\log2-\log7)-W(H)\\
&+\log5+b_2(H)\log2+b_7(H)\log7,\\
W(H)&=\sum_{\substack{p\le H\\p\ne2,7}}(t_p-1)\log p\ge0,\\
b_2(H)&=\max\left\{0,\left\lceil\frac{H-15}{8}\right\rceil\right\},
\qquad b_7(H)=\left\lceil\frac{H-1}{2}\right\rceil.
\end{aligned}
\tag{40.7}
$$

这里 $\vartheta(H)=\sum_{p\le H}\log p$，$t_p$ 为原定义 16.1、(16.2) 中同一对 CM 点在原好地方的共同入口深度；二进指数同时引用原 (15.19)。代入 $\Xi_H=(H+1)^2-\log q_H$，得到供 (40.5) 消费的准确相位

$$
\begin{aligned}
\Xi_H&=W(H)-(H-1)(\vartheta(H)-H)+C_H,\\
C_H&=3H+1+(H-1-b_2(H))\log2
 +(H-1-b_7(H))\log7-\log5,\\
C_H&=\left(3+\frac78\log2+\frac12\log7\right)H+O(1).
\end{aligned}
\tag{40.8}
$$

等式中的 $3H+1$ 来自 $(H+1)^2-H(H-1)$，其余线性系数来自准确的 $b_2,b_7$。因此 (40.5) 中的 $\eta_H$ 必须按完整的 (40.8) 计算；线性项与阶段宽度 $2H+1$ 同阶，不能删去。$W$ 的符号是正号：入口余项增加使 $\log q_H$ 减小，使端点预算增大，是有利相位。

作为该准确判据的充分路线，对原负阶段 $H\in\mathcal H_-$，有 $\vartheta(H)-H<0$，故 $\Xi_H\ge C_H$。由 (40.8) 的线性系数严格大于 $2$，充分大的这些 $H$ 全部满足 $\Xi_H>2H+1$，从而 $\eta_H=1$。因此

$$
\sum_{H\in\mathcal H_-}\frac1H=\infty
\quad\Longrightarrow\quad
\sum_H\frac{\eta_H}{H}=\infty.
\tag{40.9}
$$

这里不反向推出负阶段的谐和级数发散。该准确判据也计入非负阶段，其贡献仍由 (40.8) 的实际 $W(H)$ 与素数误差共同决定；目前没有给出它们的总贡献估计。只知道 $W(H)\ge0$ 不能把它升级为任何正的平均下界。

用白话说，素数误差的负相位一定有利，原共同入口余项也有利，但两者必须连同保留下来的线性修正一起进入同一个端点预算。只研究负阶段是一条充分路线，并不穷尽这个准确判据。

## 41. 完整标量判据的来源与同一 CM 目标的未决桥

定理 38.2 的经典整数子式与行列式步骤只消费本卷 (25.1)、(25.13)–(25.14)，零方向准确值消费定理 27.1；真实分块、半径比较与完整事件均消费定理 28.1。定理 38.3 将这些原片接到每个共同有限纤维的最大窗，给出完整真实块测度的共同最小性。定理 39.2 的积分比较只作为保留全部真实 floor、空片及跨阶段短片的完整预算推导之中间方法；(40.7)–(40.8) 则只是原 002 (16.33) 的准确展开，新增消费者是 (40.5) 的半端点判据。这些原过滤上的综合为 repo-derived，不主张经典格论、积分比较或一般求和方法的原创性。

原 002 (16.27) 的 $\log q_H\sim H^2$ 只给出 $\Xi_H=2H+1+o(H^2)$，不控制误差与 $2H+1$ 的相对位置，也不给原 $K_{jt}=e^{O(H_{jt})}$ 的统一上界。上述阶段比较对任意 $q>0$ 已统一成立，因此不需要此类未经支付的次阶估计。原 002 (16.34) 给出的 $W(H)$ 上界不提供端点所需的平均下界；(40.5) 保留其实际值。

定理 35.2 的无条件 $0<\gamma<1/2$ 全方向发散及 RH 下的 $\gamma=1/2$ 发散，连同定理 36.1 的 $\gamma>1/2$ 零方向收敛，均直接作为既有结论使用，不重证其文献输入。无条件半端点的 $\sum_H\eta_H/H$ 是否发散仍未判定，(40.5) 不把这一未决问题改写成已解结论。

标量发散只判定全部比较方向的几何权重和发散，不判定无限命中集满测。事实上对所有 $\gamma>0$，零方向的 $\rho(n)\to0$ 且所有实中心为零，故

$$
R_\gamma(0)\subseteq C_M\times\{(0,0)\},\qquad
\nu(R_\gamma(0))=0.
\tag{41.1}
$$

证明只需固定 $z\ne(0,0)$ 的一个非零坐标圆距离；所有充分晚的实窗均排除该 $z$。这与共同标量预算可以发散相容。更强的同一个有限型零测比较方向已由定理 37.1 给出，直接引用即可，不将该方向认作原 $\alpha$。

对实际 CM 方向 $\omega=\alpha$，原 (17.5) 已提供定理 29.2–31.1 的有限型前提。若实际原好阶段权重在 (31.1) 的某个几何分箱中有发散的最大值和，则定理 31.1 已将它接到同一 $Y$ 上的满测；其证明所需的分隔子族和加权二阶步骤均复用 §§30–31。准确未决桥是能否验证实际权重的 (31.2)，或取得在同一 $Y$ 上足以支撑原加权二阶论证的跨块交能量估计。完整标量预算发散尚未提供其中任一项。不要求每对块都统一渐近独立，也不把既有凝聚充分条件称为必要条件。因此实际 $\nu(R_\gamma(\alpha))$ 仍未裁定。所有事件仍使用原全部有限地方、原 $q_H,h,\rho,M,a_0,Y$ 与同一个成功整数。

## 追加锚（本行以下为增补区）

## 42. 取得谱右边界支付原负阶段的半端点占用

**定义 42.1（取得边界下的同一路径误差与原过滤）。** 保持定义 35.1、24.1 的全部数据：实际 CM 点对、全部有限地方条件、真实共同周期 $q_H$、原 $h,\rho,M,a_0,Y,\nu$ 及同一个成功整数。固定原过滤参数 $\beta=0,c_0=1,\gamma=1/2$，不替换实际 $q_H$ 或实际方向 $\alpha$。令

$$
 b_\zeta:=\sup\{\operatorname{Re}\rho:\rho\text{ 是 }\zeta(s)\text{ 的非平凡零点}\}.
\tag{42.1}
$$

在 Devin 的归一化下写

$$
E_\pi(x)=\frac{\log x}{x^{b_\zeta}}
       \bigl(\pi(x)-\operatorname{Li}(x)\bigr),\qquad
E_\psi(x)=\frac{\psi(x)-x}{x^{b_\zeta}},\qquad
E_\theta(x)=\frac{\vartheta(x)-x}{x^{b_\zeta}}.
\tag{42.2}
$$

若 $b_\zeta>1/2$ 且上确界被某个零点取得，则必有
$1/2<b_\zeta<1$。记 $b=b_\zeta$，并令 $m_\tau$ 是零点
$b+i\tau$ 的重数，$\tau>0$ 取互异的正虚部。

**定理 42.2（取得谱边界的全方向半端点发散）。** 在定义 42.1 的原过滤中，以下两条路线分别成立：

1. RH 路线直接复用定理 35.2：对每个 $\omega\in\mathbb T^2$，
   $\sum_{j\ge j_0}g_j^{(1/2)}(\omega)=\infty$。
2. 若 $b_\zeta>1/2$ 且存在 $\rho_0$ 使
   $\zeta(\rho_0)=0$、$\operatorname{Re}\rho_0=b_\zeta$，则存在
   $\delta>0$、$p>0$ 及整数 $H_1$，使集合

   $$
   \mathcal H_{\delta}:=
   \left\{H\ge H_1:\vartheta(H)-H<-\frac{\delta}{2}H^{b}\right\}
   \subseteq\mathcal H_-
   \tag{42.3}
   $$

   满足

   $$
   \liminf_{N\to\infty}\frac1{\log N}
   \sum_{\substack{H\in\mathcal H_{\delta}\\H\le N}}\frac1H
   \ge p>0,
   \tag{42.4}
   $$

   并且对每个方向 $\omega\in\mathbb T^2$，

   $$
   \boxed{\qquad
   \sum_{j\ge j_0}g_j^{(1/2)}(\omega)=\infty.
   \qquad}
   \tag{42.5}
   $$

**证明。** Devin 的 Theorem 2.1 与其对 $\zeta$ 的 Theorem 3.1 给出
$E_\pi$ 的对数极限分布 $\mu_\zeta$。当 $b>1/2$ 时，Theorem 3.1 的均值为

$$
\mathbb E_{\mu_\zeta}X=0,
\qquad
\operatorname{Var}_{\mu_\zeta}X
 =2\sum_{\tau>0}\frac{m_\tau^2}{b^2+\tau^2}>0.
\tag{42.6}
$$

求和按互异的正虚部进行并保留零点重数。正方差严格为正，是因为取得边界的零点不可能位于实轴：$\zeta$ 在 $(0,1)$ 没有实零点，所以某个取得边界的零点给出一个 $\tau>0$。这里没有使用 LI、简单零点、统一谱隙或任何额外的零点独立性假设。

同一篇文献的 Lemma 4.7，式 (9)，在 zeta 情形给出
$\vartheta(x)=\psi(x)-\sqrt{x}+o(\sqrt{x})$；式 (10) 给出同一实际过程的

$$
E_\pi(x)=E_\psi(x)-x^{1/2-b}+o(1),
\qquad
E_\theta(x)=E_\psi(x)-x^{1/2-b}+o\!\left(x^{1/2-b}\right).
\tag{42.7}
$$

因此 $b>1/2$ 时 $E_\theta(x)-E_\pi(x)\to0$。对任意有界 Lipschitz 函数，时间平均的差也趋于零，所以 $E_\theta$ 具有同一个对数极限分布 $\mu_\zeta$，均值为 $0$ 且方差严格为正。

取随机变量 $Z$ 服从 $\mu_\zeta$。因 $Z$ 可积、$\mathbb EZ=0$ 而
$\operatorname{Var}Z>0$，必有
$\Pr(Z<0)>0$：否则 $Z\ge0$ 几乎处处，零均值会迫使 $Z=0$ 几乎处处，与正方差矛盾。于是可先取 $d_0>0$ 使
$\Pr(Z<-d_0)>0$，再在 $(0,d_0)$ 中避开分布的至多可数个原子，得到

$$
\delta\in(0,d_0),\qquad
p:=\Pr(Z<-\delta)>0,\qquad
\Pr(Z=-\delta)=0.
\tag{42.8}
$$

由有界 Lipschitz 函数从上下两侧逼近区间指标，并用 Devin 的对数极限分布定义，集合

$$
\mathcal A_\delta:=
\{x\ge2:\vartheta(x)-x<-\delta x^b\}
\tag{42.9}
$$

满足

$$
\lim_{N\to\infty}\frac1{\log N}
\int_2^N\mathbf1_{\mathcal A_\delta}(x)\,\frac{dx}{x}=p.
\tag{42.10}
$$

这一步只取得严格负阈值的正对数密度，不把它改写成 $1/2$ 或自然密度。

现在把同一实变量 $x$ 送到唯一的整数 $H=\lfloor x\rfloor$。对充分大的 $x\in\mathcal A_\delta$，有 $\vartheta(H)=\vartheta(x)$，且

$$
\vartheta(H)-H
 =\vartheta(x)-x+(x-H)
 <-\delta x^b+1
 \le-\delta H^b+1
 <-\frac\delta2H^b<0.
\tag{42.11}
$$

故 $H\in\mathcal H_-$。由于每个整数只接收区间 $[H,H+1)$，且
$\log(1+1/H)\le1/H$，由 (42.10) 得

$$
\int_2^N\mathbf1_{\mathcal A_\delta}(x)\,\frac{dx}{x}
\le O(1)+
\sum_{\substack{H\in\mathcal H_\delta\\H\le N}}
\log\left(1+\frac1H\right)
\le O(1)+
\sum_{\substack{H\in\mathcal H_\delta\\H\le N}}\frac1H.
\tag{42.12}
$$

除以 $\log N$ 并取下极限，得到 (42.4)。这一步保留同一个实际整数；连续集合中的不同 $x$ 没有被误当成不同整数。

最后直接消费定理 34.1 的严格窗口。取其在 $\gamma=1/2$ 下的充分大阈值与常数 $c_{1/2}>0$。窗口 $\mathcal D_H$ 对不同 $H$ 两两不交，并且对所有 $\omega$ 同时有

$$
\sum_{j\in\mathcal D_H}g_j^{(1/2)}(\omega)
\ge c_{1/2}H^{-1}
\qquad(H\in\mathcal H_-,\ H\text{ 充分大}).
\tag{42.13}
$$

用 $\mathcal H_\delta\subseteq\mathcal H_-$、非负性及 (42.4)，逐方向得到

$$
\sum_{j\ge j_0}g_j^{(1/2)}(\omega)
\ge c_{1/2}
\sum_{H\in\mathcal H_\delta}\frac1H
=\infty.
\tag{42.14}
$$

这也可准确看作定理 40.1 的 (40.9) 对这些负阶段的应用：端点相位在充分大负阶段已有 $\eta_H=1$。这里只使用已付的端点判据，不另立等价的通用定理。RH 分支则仅引用定理 35.2 的 (35.3)，不重复其证明。$\square$

用白话说，取得的最右零点把真实的 $\pi$、$\psi$、$\vartheta$ 误差放在同一条路径上。Devin 的分布结果说这条路径平均为零却有非零波动，所以它在某个严格负阈值以下占有正的对数时间。因为 $\vartheta$ 是阶梯函数，把每个负的实区间压到 $H=\lfloor x\rfloor$ 后，仍得到具有正下谐和质量的原负整数阶段。每个这样的阶段都由 §34.1 支付至少 $c/H$ 的严格窗口预算，于是原完整几何权重在半端点对每个方向发散。

**来源与边界。** Devin，*Chebyshev’s bias for analytic L-functions*，arXiv v4，[原始 PDF](https://arxiv.org/pdf/1706.06394v4)，DOI [10.1017/S0305004119000100](https://doi.org/10.1017/S0305004119000100)，Theorem 2.1、Theorem 3.1、Lemma 4.7 的 (9)–(10) 及 Remark 7(1) 是本条的 literature-attested 中间输入；不在这里重证成熟的极限分布或 Abel/部分求和步骤。zeta 在 $\operatorname{Re}s=1$ 无零点、在 $(0,1)$ 无实零点只用于说明边界范围与正虚部存在。把该分布接到同一实际 $\vartheta$、原负阶段及 §34.1 窗口，是本卷的 repo-derived 消费者。

本条不主张右边界实际取得，不主张 RH，也不声称取得条件在逻辑上严格弱于 RH。若 $b_\zeta>1/2$ 的上确界未被零点取得（包括 $b_\zeta=1$ 或 $1/2<b_\zeta<1$ 仅从左侧逼近的情形），本条不覆盖它；Devin 的 Remark 7(1) 允许边界零点集合为空且分布退化为 $\delta_0$，固定负阈值因而没有由该输入得到。半端点的无条件结论仍未由本条取得。即使 (42.5) 成立，它只给每个方向的完整几何权重和发散；§41 所列实际 $\alpha$ 的跨块联合桥仍未付，不能推出 $\nu(R_{1/2}(\alpha))$ 的满测结论。

## 追加锚（本行以下为增补区）

## 43. 未取得谱边界的移动余谱单侧尺度与固定幂次障碍

**定义 43.1（同一窗口上的真实删对余谱）。** 保持定义 42.1 的原 CM 点对、全部有限地方、实际 $q_H$、原 $h,\rho,M,a_0,Y,\nu$、实际方向 $\alpha$ 及同一个成功整数；原过滤仍为 $\beta=0,c_0=1,\gamma=1/2$。以下谱变量 $\beta_n$ 是零点实部，不是过滤参数 $\beta$。令 $\mathcal Z$ 为 $\zeta$ 的非平凡零点的不同位置集合，每个位置 $\rho$ 的实际重数记为 $m_\rho$，并假设

$$
b=b_\zeta=\sup_{\rho\in\mathcal Z}\operatorname{Re}\rho>\frac12,
\qquad \operatorname{Re}\rho<b\quad(\rho\in\mathcal Z).
\tag{43.1}
$$

这里 $b\le1$，允许 $b=1$。取任意真实零点序列及任意截断高度

$$
\rho_n=\beta_n+iG_n\in\mathcal Z,\qquad
\beta_n\longrightarrow b,\qquad G_n>0,\qquad G_n\longrightarrow\infty,
\qquad T_n\ge G_n.
\tag{43.2}
$$

以下只取 $\log T_n\ge1$ 的尾部。固定 $0<\kappa<1$，记

$$
\begin{gathered}
r=\kappa^{-1},\qquad q=\frac{1+r}{2},\qquad d=\frac{r-1}{2},
\qquad t_n=\log T_n,\\
I_n=[t_n,rt_n]=[(q-d)t_n,(q+d)t_n],\qquad
L_n=(r-1)t_n,\\
m_n=m_{\rho_n},\qquad A_n=\frac{m_n}{|\rho_n|},\qquad
\delta_n=b-\beta_n\longrightarrow0.
\end{gathered}
\tag{43.3}
$$

只删除选中的两个位置及其全部重数贡献，定义

$$
\begin{aligned}
F_n(y)&=\sum_{\substack{\rho\in\mathcal Z,\ |\operatorname{Im}\rho|\le T_n\\
                 \rho\notin\{\rho_n,\overline{\rho_n}\}}}
       \frac{m_\rho}{\rho}\,e^{(\rho-\beta_n)y},\\
(F_n)_+(y)&=\max\{F_n(y),0\},\qquad
(F_n)_-(y)=\max\{-F_n(y),0\},\\
M_n^\pm&=\frac1{L_n}\int_{I_n}(F_n)_\pm(y)^2\,dy.
\end{aligned}
\tag{43.4}
$$

共轭位置具有相同重数，截断及删除均保留共轭性，故 $F_n$ 为实值。求和按不同位置，重数只在系数中出现。不要求 $\rho_n$ 在有限截断内实部最右；其他项可以满足 $\operatorname{Re}\rho>\beta_n$。也不假设简单零点、LI、不同零点的统一频差或随机独立性。窗口始终是 (43.3)，没有改用另一个平均区间。

**定理 43.2（移动删对余谱的两侧对数指数）。** 在定义 43.1 下，$M_n^+$ 与 $M_n^-$ 对充分大的 $n$ 均严格为正，且分别满足

$$
\boxed{\qquad
\lim_{n\to\infty}\frac{\log M_n^+}{\log T_n}
=\lim_{n\to\infty}\frac{\log M_n^-}{\log T_n}=0.
\qquad}
\tag{43.5}
$$

即对每个固定 $\eta>0$，充分大的 $n$ 有 $T_n^{-\eta}\le M_n^\pm\le T_n^\eta$。记法 $T_n^{o(1)}$ 在此只指这个对数指数结论，不指趋于某个正数。

**证明。** 所有非平凡零点满足 $0<\operatorname{Re}\rho<1$。先列出证明使用的经典零点输入及其直接后果。设 $N(U)$ 按重数计数 $0<\operatorname{Im}\rho\le U$ 的零点；无条件局部计数给出

$$
N(U+1)-N(U)\ll\log(U+2)\quad(U\ge2).
\tag{43.6}
$$

此处只引用 Maynard–Pratt，*Half-isolated zeros and zero-density estimates*，[arXiv:2206.11729v2](https://arxiv.org/pdf/2206.11729v2)，印刷页 14、Definition 18 后的这一经典估计，不使用该文的 Hypothesis $\mathcal F$ 或条件零密度结论。由单位高度分组及共轭性，

$$
\begin{gathered}
\#\{\rho\in\mathcal Z:|\operatorname{Im}\rho|\le W\}
\ll W\log(W+2)\quad(W\ge2),\\
m_\rho\ll\log(|\operatorname{Im}\rho|+2),\qquad
B(T):=\sum_{\substack{\rho\in\mathcal Z\\|\operatorname{Im}\rho|\le T}}
                  \frac{m_\rho}{|\rho|}
\ll\log^2(T+2).
\end{gathered}
\tag{43.7}
$$

最后一个估计的高处贡献由 $\sum_{k\le T}\log(k+2)/k$ 控制，低处只有固定有限个零点。此外存在固定 $\gamma_0>0$ 使每个 $\rho\in\mathcal Z$ 都有 $|\operatorname{Im}\rho|\ge\gamma_0$。事实上对 $0<s<1$，将交错级数两两分组得 $\eta(s)>0$，而 $\eta(s)=(1-2^{1-s})\zeta(s)$，故 $\zeta(s)<0$。完成函数 $\xi$ 在 $[0,1]$ 上无零点，端点值均为 $1/2$；若非平凡零点虚部能趋于零，实部的紧性和 $\xi$ 的连续性会给出该实区间上的零点。这里仅用 $\gamma_0>0$，不要求 $\gamma_0>1$，也没有把它当作不同零点之间的距离。

先固定常数

$$
0<C<\min\left\{\frac q4,\frac d8,\frac{d^2}{16r}\right\},
\qquad h=\frac{d^2}{8C}-r>0,
\qquad c=\min\{C\gamma_0^2,h\}>0.
\tag{43.8}
$$

这些常数只依赖固定窗口和真实谱的正虚部间隙，尚未选择任何旧根。对 $t\ge1$ 定义正高斯

$$
g_t(y)=\frac{e^{-(y-qt)^2/(4Ct)}}{\sqrt{4\pi Ct}},
\qquad
\Phi_t(y)=\frac{e^{-(y-qt)^2/(8Ct)}}{\sqrt{8\pi Ct}}.
\tag{43.9}
$$

高斯积分给出对所有 $z\in\mathbb C$

$$
\int_{\mathbb R}e^{zy}g_t(y)\,dy=e^{t(qz+Cz^2)},
\qquad
\int_{\mathbb R}e^{zy}\Phi_t(y)\,dy=e^{t(qz+2Cz^2)}.
\tag{43.10}
$$

可先对实 $z$ 配方，再由两端关于 $z$ 的整性延拓；高斯保证任意紧 $z$ 集上的积分及各阶导数绝对收敛。

先把整个窗外的代价统一支付。令 $u=y/t$，写

$$
\Psi(u)=-\frac{(u-q)^2}{8C}+|u|.
$$

由 (43.8)，在 $u<0$ 上 $\Psi'(u)\ge q/(4C)-1>1$，在 $0<u\le1$ 上 $\Psi'(u)\ge d/(4C)+1>1$；在 $u\ge r$ 上 $\Psi'(u)\le1-d/(4C)<-1$。函数在 $u=0$ 连续，且

$$
\Psi(1)=1-\frac{d^2}{8C}\le-h,
\qquad \Psi(r)=r-\frac{d^2}{8C}=-h.
$$

因而 $u\le1$ 时 $\Psi(u)\le-h-(1-u)$，$u\ge r$ 时 $\Psi(u)\le-h-(u-r)$。直接积分得到

$$
\begin{aligned}
\int_{\mathbb R\setminus[t,rt]}e^{|y|}\Phi_t(y)\,dy
&=\frac{t}{\sqrt{8\pi Ct}}
  \left(\int_{-\infty}^{1}+\int_r^\infty\right)e^{t\Psi(u)}\,du\\
&\le\frac{2}{\sqrt{8\pi Ct}}e^{-ht}
\ll_C e^{-ht}.
\end{aligned}
\tag{43.11}
$$

这里的左尾是全部 $y<t$，明确包括 $0\le y<t$，不是只估计 $y<0$。

对每个参与 $F_n$ 的零点置 $a=\operatorname{Re}\rho-\beta_n$、$v=\operatorname{Im}\rho$。有 $-1<a\le\delta_n$。当 $-1\le a\le0$ 时，$qa+2Ca^2=a(q+2Ca)\le0$；当 $0\le a\le\delta_n$ 时，该式至多 $q\delta_n+2C\delta_n^2$。故充分大的 $n$ 对全部项同时有

$$
qa+2C(a^2-v^2)
\le q\delta_n+2C\delta_n^2-2C\gamma_0^2
\le-C\gamma_0^2.
$$

利用 (43.7)、(43.10)，可得整轴正核均值的界

$$
\left|\int_{\mathbb R}F_n(y)\Phi_{t_n}(y)\,dy\right|
\ll t_n^2 T_n^{-C\gamma_0^2}.
\tag{43.12}
$$

另一方面 $|a|<1$ 给出对全部实 $y$ 的包络 $|F_n(y)|\le B(T_n)e^{|y|}$。以 (43.11) 限制回同一窗口，得到

$$
\left|\int_{I_n}F_n(y)\Phi_{t_n}(y)\,dy\right|
\ll t_n^2 T_n^{-c}.
\tag{43.13}
$$

下面从同一余谱抽取一个固定旧根。取任意真实 $\rho_\ast=\sigma_\ast+i\gamma_\ast$，其中 $\gamma_\ast>0$，使

$$
0<\varepsilon=b-\sigma_\ast<\frac{c}{2r}.
\tag{43.14}
$$

由上确界定义和共轭性，可令 $\varepsilon$ 任意小；每次选定后 $\rho_\ast$ 在整个 $n\to\infty$ 过程中保持固定。对 $W>|\gamma_\ast|+1$ 定义

$$
P_W(z)=\prod_{\substack{\rho\in\mathcal Z,\ |\operatorname{Im}\rho|\le W\\
                                  \rho\ne\rho_\ast}}
        \left(1-\frac{z}{\rho-\rho_\ast}\right),
\qquad D_W=\deg P_W\ll W\log(W+2).
\tag{43.15}
$$

乘积按不同位置，无重数重复因子；分母均非零，$P_W(0)=1$。不要求这些分母有随 $W$ 一致的下界。记

$$
\chi_t(y)=P_W(-\partial_y)g_t(y).
\tag{43.16}
$$

对于每个固定阶数 $j$，直接微分有

$$
\partial_y^j g_t(y)
=t^{-j/2}Q_{j,C}\!\left(\frac{y-qt}{\sqrt t}\right)g_t(y),
\qquad
\frac{g_t(y)}{\Phi_t(y)}
=\sqrt2\,e^{-(y-qt)^2/(8Ct)},
$$

其中 $Q_{j,C}$ 是固定多项式。因此对固定的 $W,\rho_\ast,C$，存在与 $t\ge1$、$y$ 无关的有限常数 $K$，使

$$
|\chi_t(y)|\le K\Phi_t(y),\qquad
\int_{\mathbb R}e^{zy}\chi_t(y)\,dy
=P_W(z)e^{t(qz+Cz^2)}.
\tag{43.17}
$$

后一式由有限次分部积分得到，所有边界项均由高斯衰减消失。$K$ 可以依赖实际低根之间的距离，不要求它随 $W$ 一致。

现在先固定任意 $B>0$，再取足够大的固定 $W$，使

$$
C(W-|\gamma_\ast|)^2>D_W+q+C+B.
\tag{43.18}
$$

这种 $W$ 存在，因为 (43.15) 的次数为 $O(W\log(W+2))$，而左边随 $W$ 二次增长。对任一高根 $|\operatorname{Im}\rho|>W$，令 $z=\rho-\rho_\ast$。其变换的指数满足

$$
\operatorname{Re}(qz+Cz^2)
\le q+C-C(W-|\gamma_\ast|)^2.
$$

且在 $|\operatorname{Im}\rho|\le T_n$ 内 $|P_W(\rho-\rho_\ast)|\le K_W T_n^{D_W}$。由 (43.7)，无论高根是否比 $\rho_n$ 更靠右，其总贡献的绝对值至多

$$
\begin{aligned}
&\sum_{\substack{\rho\in\mathcal Z\\W<|\operatorname{Im}\rho|\le T_n}}
\frac{m_\rho}{|\rho|}
|P_W(\rho-\rho_\ast)|
\left|e^{t_n(q(\rho-\rho_\ast)+C(\rho-\rho_\ast)^2)}\right|\\
&\hspace{1cm}\ll_W
 t_n^2 T_n^{D_W+q+C-C(W-|\gamma_\ast|)^2}
\ll_W t_n^2 T_n^{-B}.
\end{aligned}
\tag{43.19}
$$

这里保留了次数 $D_W$ 和实部增长 $q+C$ 的全部成本；删除其中的选中共轭对只会减小这个绝对值上界。

充分大的 $n$ 有 $G_n>W$，所以选中对不在低根乘积内，旧根仍保留在 $F_n$。将 (43.17) 应用于每个 $z=\rho-\rho_\ast$，低根除 $\rho_\ast$ 外全部被消去，遂有

$$
\int_{\mathbb R}e^{(\beta_n-\rho_\ast)y}F_n(y)\chi_{t_n}(y)\,dy
=\frac{m_{\rho_\ast}}{\rho_\ast}+O_W(t_n^2T_n^{-B}).
\tag{43.20}
$$

此式利用的是准确抵消
$e^{(\beta_n-\rho_\ast)y}e^{(\rho-\beta_n)y}=e^{(\rho-\rho_\ast)y}$，不是假设 $\rho_n$ 为截断最右根。还须将抽取限制回原窗。由 (43.17) 以及 $|\operatorname{Re}\rho-\sigma_\ast|<1$，对全部实 $y$ 有

$$
\left|e^{(\beta_n-\rho_\ast)y}F_n(y)\chi_{t_n}(y)\right|
\le K B(T_n)e^{|y|}\Phi_{t_n}(y).
$$

故同一个 (43.11) 给出整个窗外积分为 $O_W(t_n^2T_n^{-h})$。取例如 $B=1$，得到

$$
\int_{I_n}e^{(\beta_n-\rho_\ast)y}F_n(y)\chi_{t_n}(y)\,dy
=\frac{m_{\rho_\ast}}{\rho_\ast}+o(1).
\tag{43.21}
$$

误差的指数 $h$ 不依赖旧根或多项式；其常数允许依赖它们。此窗外界包括全部 $0\le y<t_n$。

记 $a_\ast=m_{\rho_\ast}/|\rho_\ast|>0$、$\Phi_n=\Phi_{t_n}$。在 $I_n$ 内，由 $\beta_n\le b$ 及 $y>0$，

$$
\left|e^{(\beta_n-\rho_\ast)y}\right|
=e^{(\beta_n-\sigma_\ast)y}\le T_n^{r\varepsilon}.
$$

由 (43.17)、(43.21)，对充分大的 $n$ 有

$$
J_n:=\int_{I_n}|F_n(y)|\Phi_n(y)\,dy
\ge\frac{a_\ast}{2K}T_n^{-r\varepsilon}.
\tag{43.22}
$$

令 $U_n^\pm=\int_{I_n}(F_n)_\pm\Phi_n$。实值性与正核给出准确恒等式

$$
U_n^++U_n^-=J_n,\qquad
U_n^+-U_n^-=\int_{I_n}F_n\Phi_n.
$$

(43.13) 与 $r\varepsilon<c$ 说明后一项为 $o(T_n^{-r\varepsilon})$。因此两侧分别有

$$
U_n^\pm\ge\frac{a_\ast}{8K}T_n^{-r\varepsilon}
\quad(n\text{ 充分大}).
\tag{43.23}
$$

最后，高斯积分给出 $\|\Phi_n\|_2^2=(16\pi Ct_n)^{-1/2}$。Cauchy–Schwarz 于是把正核下界送到同一窗上的未加权能量：

$$
U_n^\pm\le (L_nM_n^\pm)^{1/2}\|\Phi_n\|_2,
\qquad
M_n^\pm\gg_{\rho_\ast,W,C,\kappa}
 t_n^{-1/2}T_n^{-2r\varepsilon}.
\tag{43.24}
$$

上界则不需要消根。在 $I_n$ 上，所有项的实指数至多 $r\delta_nt_n$，所以

$$
|F_n(y)|\ll t_n^2T_n^{r\delta_n},\qquad
M_n^\pm\ll t_n^4T_n^{2r\delta_n}.
\tag{43.25}
$$

因此两侧的对数指数上极限至多为零；对每个满足 (43.14) 的固定旧根，(43.24) 给出下极限至少为 $-2r\varepsilon$。上确界未取得保证有实部任意接近 $b$ 的旧根，令所选固定旧根的 $\varepsilon\downarrow0$，下极限至少为零，得到 (43.5)。这里的量词顺序是

$$
\kappa,\gamma_0\ \longrightarrow\ C,h,c
\longrightarrow\ \rho_\ast,\varepsilon
\longrightarrow\ B,W,P_W,K
\longrightarrow\ n\to\infty.
\tag{43.26}
$$

任意小的 $\varepsilon$ 对应一次固定旧根的极限；没有把随 $n$ 变化的根、多项式或包络常数当作固定常数。$\square$

用白话说，余谱中可以有比选中根更靠右的根，所以不能逐项称它为衰减尾项。这里先用一个正高斯作平均：所有真实零点都离实轴有正距离，频率衰减便使该有符号平均很小。另一方面，固定一个靠近全局右边界的旧根，用有限多项式消去其他低根，再以高斯压低全部高根，可以从余谱中抽出它的非零系数。整个抽取连同窗外误差都被控制在原窗口上，故余谱的加权绝对值不能太小。绝对值平均不小而有符号平均很小，迫使正侧、负侧各自贡献能量。旧根可以任意接近边界，就使两侧能量都不能按 $T_n$ 的任何固定负幂下降；同时实部上确界给出任何固定正幂以下的上界。这仍允许能量缓慢趋零、缓慢增长或振荡。

**推论 43.3（单对相对能量的必要截断尺度）。** 在定义 43.1 下，令

$$
\mathcal R_n^\pm:=\frac{M_n^\pm}{A_n^2}
=\frac1{L_nA_n^2}\int_{I_n}(F_n)_\pm(y)^2\,dy.
\tag{43.27}
$$

对两种符号分别有

$$
\boxed{\qquad
\frac{\log\mathcal R_n^\pm}{\log T_n}
=2\frac{\log G_n}{\log T_n}+o(1).
\qquad}
\tag{43.28}
$$

因而任一侧的相对能量最终有界，必须满足

$$
\frac{\log G_n}{\log T_n}\longrightarrow0.
\tag{43.29}
$$

特别地，对任意固定 $1\le P<\infty$，若最终有 $G_n\le T_n\le G_n^P$，则

$$
\liminf_{n\to\infty}
\frac{\log\mathcal R_n^\pm}{\log T_n}\ge\frac2P>0,
\qquad \mathcal R_n^+\longrightarrow\infty,
\quad \mathcal R_n^-\longrightarrow\infty.
\tag{43.30}
$$

**证明。** 实际重数为正整数，由 (43.7) 有 $1\le m_n\ll\log(G_n+2)$；并且 $G_n^2\le|\rho_n|^2\le G_n^2+1$。所以

$$
\log A_n^{-2}
=2\log G_n+O(\log\log(G_n+2)).
\tag{43.31}
$$

由 $T_n\ge G_n\to\infty$，误差除以 $\log T_n$ 后趋零。(43.5) 加上 (43.31) 即为 (43.28)。若 $\mathcal R_n^\pm\le K_0$ 最终成立，则其对数除以 $\log T_n$ 的上极限至多为零；(43.28) 中 $\log G_n/\log T_n\ge0$，迫使 (43.29)。若有固定幂次上限，则 $\log G_n/\log T_n\ge1/P$，故 (43.30) 成立。等价地，对任意固定 $0<\eta<2/P$，(43.5) 给出

$$
\mathcal R_n^\pm\gg
\frac{G_n^2T_n^{-\eta}}{\log^2(G_n+2)}
\ge\frac{G_n^{2-P\eta}}{\log^2(G_n+2)}\longrightarrow\infty.
\tag{43.32}
$$

条件 (43.29) 只是必要条件，未证明它足以使任一相对能量有界。$\square$

用白话说，一个高零点自身的系数至多是常数倍的 $\log G_n/G_n$。余谱的两侧能量虽然在 $T_n$ 的对数指数上都是零，但再除以这个很小的单对系数平方，就会付出接近 $G_n^2$ 的放大。只要截断高度至多是 $G_n$ 的某个固定幂，这个代价就无法抵消。因此任何必须让该相对正部或负部 $L^2$ 成本统一有界的路线，都不能在固定幂次截断内完成。这里排除的是具有此必要步骤的路线，不排除控制小坏集、容许稀少尖峰，或按整个真实谱的自然能量尺度组织估计。

附于定理 43.2 与推论 43.3 的来源与范围如下。高斯积分、其有限阶微分包络、有限多项式消根、单位高度零点计数和 Cauchy–Schwarz 都只是成熟的中间输入；新增的 repo-derived 结论是它们对 (43.1)–(43.4) 这一个移动、删选中共轭对、保留实际重数且不假设截断最右的余谱所给出的两侧尺度及 (43.28)–(43.30)。不主张这些中间工具的原创性或该综合的文献优先性。Devin，*Chebyshev’s bias for analytic L-functions*，[arXiv:1706.06394v4](https://arxiv.org/pdf/1706.06394v4)，Proposition 4.5、印刷页 19–20 给出显式公式与平方尾估计；它不直接给出这里的单侧有限窗口结论，也不被用作原负阶段占用的证明。Johnston–Trudgian，*A round of Pintz to celebrate oscillations in sums*，[arXiv:2511.09978v4](https://arxiv.org/pdf/2511.09978v4)，Theorem 1、印刷页 3–4 是带其解析性、增长及简单零点等条件的 Landau–Pintz 绝对均值结果；它没有包含这里删移动共轭对的两侧窗口断言，亦非本证明的输入。

本条没有判定实际 $b$ 是否满足 (43.1)，不改变 §42 的取得边界条件结论，也不把方法障碍升级为原端点反例。尤其 (43.24) 是随截断变化的谱能量下界，不是同一实际 $\vartheta(H)-H$ 在原负阶段的谐和占用下界；没有从它推出 $\sum_{H\in\mathcal H_-}1/H=\infty$。无条件半端点的 $\sum_H\eta_H/H$ 发散仍未由此支付。能否用同一实际谱的小坏集估计，或整体谱自然尺度的联合估计，接回原负阶段及端点预算，仍是实际未付的桥；本条没有声称这些替代路线已经可行。即使端点标量预算发散，§41 的实际 CM 方向跨块联合桥仍须另付，实际 $\nu(R_{1/2}(\alpha))$ 满测仍未裁定。全部这些边界均针对原实际点对、全部有限地方、同一 $q_H$ 和同一个成功整数，没有以替代过滤或随机模型消除原问题。

## 追加锚（本行以下为增补区）

## 44. 完整真实 ζ 谱的截平正能量参与长度消费者

**定义 44.1（同一实际谱、同一窗口与同一显式公式余项）。** 保持定义 43.1 的全部原数据：实际 CM 点对、全部有限地方、实际共同周期 $q_H$、原 $h,\rho,M,a_0,Y,\nu$、实际方向 $\alpha$ 及每个事件使用的同一个成功整数。原过滤仍为 $\beta=0,c_0=1,\gamma=1/2$；下面的 $\beta_n$ 只表示所选零点的实部。假设

$$
 b=\sup_{\rho\in\mathcal Z}\operatorname{Re}\rho>\frac12,
 \qquad \operatorname{Re}\rho<b\quad(\rho\in\mathcal Z),
$$

其中 $\mathcal Z$ 是非平凡零点的不同位置集合，$m_\rho$ 是位置 $\rho$ 的实际重数。取实际零点

$$
 \rho_n=\beta_n+iG_n,
 \qquad \beta_n\to b,
 \qquad G_n\to\infty,
$$

并固定 $p>2$ 与 $0<\kappa<1$，令

$$
 T_n=G_n^p,
 \quad t_n=\log T_n,
 \quad r=\kappa^{-1},
 \quad I_n=[t_n,rt_n],
 \quad L_n=(r-1)t_n,
 \quad \delta_n=b-\beta_n.
 \tag{44.1}
$$

这里允许 $b=1$；不要求 $\rho_n$ 是截断谱中实部最右的根，也不假设简单零点、LI、统一频差或随机独立。对每个 $n$，按不同位置求和、在系数中只计一次实际重数，定义完整截断谱

$$
 S_n(y)=
 \sum_{\substack{\rho\in\mathcal Z\\|\operatorname{Im}\rho|\le T_n}}
 c_\rho e^{(\rho-\beta_n)y},
 \qquad c_\rho=\frac{m_\rho}{\rho}.
 \tag{44.2}
$$

共轭位置和重数均保留，故 $c_{\bar\rho}=\overline{c_\rho}$ 且 $S_n(y)\in\mathbb R$。这是完整真实谱，未删除移动共轭对，也没有为不同窗口更换零点集合、相位、$\psi$ 或原过滤。令

$$
 e^{-\beta_n y}\bigl(\psi(e^y)-e^y\bigr)
   =-S_n(y)+R_n(y)
 \qquad (y\in I_n),
 \tag{44.3}
$$

把 $R_n$ 定义为这一条同一实际 $\psi$ 的截断显式公式余项，并置

$$
 h_n(y)=e^{-\beta_n y},
 \qquad
 E_n=\int_{I_n}\bigl(|R_n(y)|+h_n(y)\bigr)^2\,dy.
 \tag{44.4}
$$

$h_n$ 只支付固定阈值 $2$ 的归一化成本；以后取整数部分时的 $x-H<1$ 也保留为同一实际取整成本。

**引理 44.2（完整谱的两侧指数与余项支付）。** 在定义 44.1 下，令

$$
 Q_n=\int_{I_n}(S_n(y)_+)^2\,dy,
 \qquad
 M_n^\pm=\frac1{L_n}\int_{I_n}(S_n(y)_\pm)^2\,dy.
 \tag{44.5}
$$

则 $Q_n>0$ 对充分大的 $n$ 成立，并且

$$
 \lim_{n\to\infty}\frac{\log M_n^+}{\log T_n}
 =
 \lim_{n\to\infty}\frac{\log M_n^-}{\log T_n}=0.
 \tag{44.6}
$$

此外，Devin 的同一截断显式公式给出

$$
 \frac{E_n}{L_n}
 \ll
 t_n^2T_n^{-1+2\delta_n/\kappa}
 +(t_n^4+1)T_n^{-2\beta_n}.
 \tag{44.7}
$$

因此 $E_n/Q_n\to0$。

**证明。** (44.6) 是定理 43.2 的高斯定位、固定旧根有限消去和同一窗口 Cauchy--Schwarz 推理在完整和 $S_n$ 上的直接复用。完整和仍满足相同的单位高度零点计数

$$
 \sum_{|\operatorname{Im}\rho|\le T_n}|c_\rho|\ll\log^2(T_n+2),
$$

并且共轭配对使其为实值。正高斯的整线均值和窗外尾分别按 (43.10)--(43.13) 估计；固定任意实部 $b-\varepsilon$ 的旧根，用 (43.15)--(43.21) 的有限多项式消去固定低谱，再让高谱由高斯频率衰减支付。选中的 $\rho_n,\bar\rho_n$ 最终高于该固定低谱，是否比它们更靠右不影响恒等式

$$
 e^{(\beta_n-\rho_*)y}e^{(\rho-\beta_n)y}=e^{(\rho-\rho_*)y}.
$$

于是正、负两侧各有 $T_n^{-\eta}$ 的下界，而实部上界给出任意固定 $T_n^\eta$ 的上界；先固定旧根再令 $\varepsilon\downarrow0$ 即得 (44.6)。这只复用 §43 已交付的证明组织，没有把移动根当作最右根。

对 (44.7)，直接使用 Devin，*Chebyshev’s bias for analytic $L$-functions*，arXiv:1706.06394v4，Proposition 4.5 的 (4)--(8)：其中的 $\varepsilon(x,T_n)$ 已是 $T_n<|\operatorname{Im}\rho|\le e^y$ 的实际高谱尾，因此 (44.7) 不再另加一份高零点尾。因 $\beta_n\to b>1/2$，任取足够小的

$$
 0<\eta<\min\left\{\frac12,\frac{2b-1}{2}\right\}
$$

后，(44.7) 给 $E_n/L_n\ll T_n^{-1+\eta}$，而 (44.6) 给 $Q_n/L_n\ge T_n^{-\eta}$，故

$$
 \frac{E_n}{Q_n}\ll T_n^{-1+2\eta}\longrightarrow0.
 \tag{44.8}
$$

这一步把同一实际显式公式余项、固定阈值和取整前的常数成本付清；它没有证明完整谱的长度证书发散。$\square$

**定义 44.3（截平高度与正能量参与长度）。** 写

$$
 X_n(y)=(S_n(y)_+)^2,
 \qquad
 C_n(z)=\int_{I_n}\min\{X_n(y),z\}\,dy \quad(z>0).
 \tag{44.9}
$$

若 $Q_n>0$，连续性和 $C_n(0)=0<C_n(\|X_n\|_\infty)=Q_n$ 给出唯一的
$z_n\in(0,\|X_n\|_\infty)$ 使

$$
 C_n(z_n)=\frac{Q_n}{2}.
 \tag{44.10}
$$

其唯一性只用有限指数和的连续性：对 $0\le z_1<z_2<\|X_n\|_\infty$，$X_n>z_1$ 的开邻域具有正长度。定义截平正能量参与长度

$$
 \Lambda_n=\frac{C_n(z_n)}{z_n}=\frac{Q_n}{2z_n}.
 \tag{44.11}
$$

$z_n$ 截平的是同一完整谱在同一原窗口中的正能量高度，不删除任何根，也不替换 $\psi$、原过滤或取整规则。

**定理 44.4（截平消费者及四阶强证书）。** 设选取的窗口族 $\{I_n\}$ 两两不交。定义

$$
 u_n(y)=|R_n(y)|+h_n(y),
 \qquad
 B_n=\{y\in I_n:S_n(y)>2u_n(y)\}.
 \tag{44.12}
$$

则充分大的 $n$ 有

$$
 \boxed{
 \frac{Q_n^2}{V_n}\le\Lambda_n\le L_n,
 \qquad
 V_n:=\int_{I_n}(S_n(y)_+)^4\,dy.
 }
 \tag{44.13}
$$

并且当 $E_n\le Q_n/16$ 时

$$
 |B_n|\ge\frac{\Lambda_n}{2}
 \ge\frac{Q_n^2}{2V_n}.
 \tag{44.14}
$$

因此任一条下列充分条件都给出同一个原负整数阶段的谐和发散：

$$
 \sum_n\Lambda_n=\infty,
 \qquad\text{或更强的}\qquad
 \sum_n\frac{Q_n^2}{V_n}=\infty.
 \tag{44.15}
$$

在每个条件下，均有

$$
 \sum_{\substack{H\ge7\\\vartheta(H)<H}}\frac1H=\infty,
 \tag{44.16}
$$

并由 §34.1 的同一严格负阶段窗口得到每个比较方向 $\omega\in\mathbb T^2$ 的

$$
 \sum_{j\ge j_0}g_j^{(1/2)}(\omega)=\infty.
 \tag{44.17}
$$

**证明。** 对任意 $x,z>0$，有

$$
 (x-z)_+\le\frac{x^2}{4z},
$$

因为 $x\ge z$ 时等价于 $(x-2z)^2\ge0$。取 $z=V_n/(2Q_n)$，便有

$$
 C_n(z)\ge Q_n-\frac{V_n}{4z}=\frac{Q_n}{2}.
$$

由 (44.10) 的唯一性，$z_n\le V_n/(2Q_n)$，从而
$\Lambda_n=Q_n/(2z_n)\ge Q_n^2/V_n$；另一方面 $C_n(z_n)\le L_nz_n$，故 $\Lambda_n\le L_n$。

在 $I_n\setminus B_n$ 上，$X_n\le4u_n^2$，所以

$$
 \int_{B_n}\min\{X_n,z_n\}
 \ge C_n(z_n)-4E_n
 \ge\frac{Q_n}{4}
 \qquad(E_n\le Q_n/16).
 \tag{44.18}
$$

除以 $z_n$ 得 (44.14)。这比直接用四阶 Hölder 保留更多信息：$Q_n^2/V_n$ 只是截平长度的一个强制下界，$\Lambda_n$ 允许极高而极稀的正尖峰被截去。

在 $B_n$ 上，由 (44.3)、(44.4) 和 $h_n=e^{-\beta_n y}$，有

$$
 \psi(e^y)-e^y
 =e^{\beta_n y}(-S_n(y)+R_n(y))<-2.
 \tag{44.19}
$$

令 $x=e^y$、$H=\lfloor x\rfloor$。同一个实际阶梯函数满足
$\vartheta(H)\le\psi(H)\le\psi(x)$，且 $0\le x-H<1$，故

$$
 \vartheta(H)-H< -2+(x-H)<-1<0.
 \tag{44.20}
$$

没有为每个窗口另取整数；所有 $B_n$ 都落在同一个实际集合

$$
 D=\{y:\psi(e^y)-e^y<-2\}.
 \tag{44.21}
$$

对 $Y$ 足够大，按唯一胞 $[\log H,\log(H+1))$ 分割并使用
$\log(1+1/H)\le1/H$，得到

$$
 |D\cap[\log7,Y]|
 \le O(1)+
 \sum_{\substack{7\le H\le e^Y\\\vartheta(H)<H}}\frac1H.
 \tag{44.22}
$$

由于窗口不交，(44.14) 与 (44.15) 使 $\sum_n|B_n|=\infty$；取越来越大的前缀应用 (44.22)，即得 (44.16)。最后复用 §34.1：每个充分大的 $H$、每个方向同时有一个两两不交窗口族的贡献至少 $c_{1/2}/H$。对 $H$ 求和即为 (44.17)；等价地，这是 §40.9 在 $\gamma=1/2$ 的原半端点消费者。这正是原负 $\vartheta$ 阶段的长度消费者，未把方法障碍改写成端点反例。$\square$

**单窗、互不相交与重叠的量词。** (44.15) 的求和必须在不交窗口上进行；若窗口重叠，裸和会把同一对数时间重复计数，不能推出 (44.16)。单窗证书沿子列无界则足够：由 $\Lambda_n\le L_n$ 且 $t_n\to\infty$，可递归选取 $n_k$ 使 $I_{n_k}$ 两两不交且 $\Lambda_{n_k}\ge k$，于是其和发散；$Q_n^2/V_n$ 同理。反向则不成立：每窗证书恒为 $1$ 的不交族已有发散和，却没有单窗无界。若只有有界重叠，需先按重叠常数付账，不能静默套用 (44.22)。

**严格性例子（一般函数类，不是 ζ 反例）。** 取不交区间 $I_n$，令 $t_n=R^n$、$R>1/\kappa$，$L_n=(r-1)t_n$。在每个区间的两半上先取 $S_n=+1$ 与 $S_n=-1$；再在正半的一小段、负半的同长度一小段上分别改为 $+A_n$、$-A_n$，其中

$$
 d_n=e^{-3\sqrt{t_n}},
 \qquad A_n=e^{\sqrt{t_n}}.
$$

它保持均值为零，且 $\|S_n\|_\infty=e^{o(t_n)}$。直接计算给出

$$
 Q_n=\frac{L_n}{2}+o(1),
 \qquad
 V_n\asymp d_nA_n^4=e^{\sqrt{t_n}},
 \qquad
 \frac{Q_n^2}{V_n}\asymp L_n^2e^{-\sqrt{t_n}},
 \tag{44.23}
$$

故四阶和收敛。另一方面，解 (44.10) 得 $z_n=1/2+o(1)$，所以 $\Lambda_n=L_n/2+o(L_n)$，其不交和发散。这个例子只说明极稀尖峰会破坏四阶参与长度而不破坏截平参与长度；它没有 ζ 的零点系数、实部联合分布或显式公式，也不是实际 ζ 的反例。

**完整四频接口与当前文献边界。** 令 $\sigma_j=\operatorname{Re}\rho_j$、$\gamma_j=\operatorname{Im}\rho_j$，并置

$$
 a=\sigma_1+\sigma_2+\sigma_3+\sigma_4-4\beta_n,
 \qquad
 \omega=\gamma_1+\gamma_2-\gamma_3-\gamma_4,
$$

$$
 K_n(z)=\int_{I_n}e^{zy}\,dy
 =e^{zt_n}\frac{e^{zL_n}-1}{z},
 \qquad K_n(0)=L_n.
 \tag{44.24}
$$

因 $S_n$ 实值，$W_n:=\int_{I_n}S_n(y)^4dy=\int|S_n(y)|^4dy$ 的精确展开为

$$
 W_n=
 \sum_{\rho_1,\ldots,\rho_4}
 c_{\rho_1}c_{\rho_2}
 \overline{c_{\rho_3}c_{\rho_4}}
 K_n(a+i\omega),
 \qquad
 V_n\le W_n,
 \tag{44.25}
$$

其中四个指标都遍历同一个 $|\operatorname{Im}\rho_j|\le T_n$ 的完整实际谱，重数已经在每个 $c_\rho$ 中计入。精确核满足

$$
 |K_n(a+i\omega)|
 \le e^{\max\{at_n,a(t_n+L_n)\}}
 \min\left\{L_n,\frac2{|a+i\omega|}\right\},
 \tag{44.26}
$$

约定 $2/0=+\infty$。因此定义绝对值充分上界

$$
 U_n=\sum_{\rho_1,\ldots,\rho_4}
 |c_{\rho_1}c_{\rho_2}c_{\rho_3}c_{\rho_4}|
 |K_n(a+i\omega)|,
$$

则 $V_n\le W_n\le U_n$；若某个两两不交窗口族满足
$\sum_nQ_n^2/U_n=\infty$，也足以消费 (44.15)。这是可能很强的绝对值条件，不允许把真实相位抵消删掉后声称它不存在。

必须同时保留四项的实部 $a$、原相位 $e^{i\omega t_n}$、趋于 $1/L_n$ 的近共振尺度 $|\omega|\lesssim1/L_n$ 以及正部 $Q_n$ 的归一化。只计固定单位频率窗口的四元组，或只取各边缘实部/频率的分别最优值，都没有给出 (44.25) 所需的同一四元组界。Tao--Trudgian--Yang，*New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach*，arXiv:2501.16779v1，Definition 56、Remark 57 及 Theorems 63--64 研究实际 ζ 零点的单位尺度无权加法能量；它提供相关工具线索，却没有支付这里带同窗核、阻尼系数、真实相位与正侧归一化的 $Q_n^2/V_n$ 或 $\Lambda_n$ 发散。固定尺度的幂指数不能静默代入本题随 $n$ 缩小的 $1/L_n$ 频差。

**来源、复用范围与未决边界。** §43 的定义、同一窗口高斯抽取和两侧指数是本条 (44.6) 的直接上游；§34.1 的严格原负阶段窗口支付 (44.17)，§40.9 的准确相位路线和 §41 的实际 CM 跨块联合桥保持原状。Devin，*Chebyshev’s bias for analytic $L$-functions*，arXiv:1706.06394v4，Proposition 4.5 (4)--(8)，是 (44.3)--(44.8) 的同一实际 $\psi$ 显式公式和截断高谱尾输入。Tao--Trudgian--Yang 的上述结果只作为四频检索方向和适用边界，不被当作本条已支付的定理。高斯积分、有限多项式消根、Cauchy--Schwarz、截平不等式和整数胞估计都是成熟中间工具；本条新增的消费者是：在完整实际谱上把 $\Lambda_n$ 或 $Q_n^2/V_n$ 的同窗、不交发散接回原负 $\vartheta$ 整数谐和与全方向几何预算。

本条没有证明真实 ζ 在 $b>1/2$ 且边界未取得时存在满足 $\sum\Lambda_n=\infty$ 的不交窗口，也没有证明较强的 $\sum Q_n^2/V_n=\infty$。它没有把 $Q_n/L_n=T_n^{-o(1)}$ 或 $\|S_n\|_\infty=e^{o(t_n)}$ 误报成发散：这些读数至多给单窗尺度，不能排除长度证书的可和衰减。无条件半端点的实际相位和谐和条件仍未由本条支付；即便 (44.17) 对所有方向成立，§41 所列同一 $Y$ 上实际 CM 方向的联合桥和 $\nu(R_{1/2}(\alpha))$ 满测问题仍未解。所有结论继续使用原 $q_H$、全部有限地方、原点对和同一个成功整数。

用白话说，完整谱路线保留了所有真实零点，不再要求选中的高根控制余谱。§43 的高斯抽取只说明两侧能量在 $T_n$ 的幂指数上不能太小；Devin 的显式公式则说明同一窗口内的实际余项和固定阈值成本相对正能量趋于零。剩下的真实问题是正能量占据了多长的对数时间。$Q_n^2/V_n$ 对极高尖峰很敏感，截平后的 $\Lambda_n$ 把这些尖峰截掉，保留一半正能量对应的长度；若在不重复计时的窗口族上其和发散，就把同一实际 $\psi$ 的负值压到同一个整数 $H$，得到原 $\vartheta(H)<H$ 的无穷谐和，再消费 §34.1 的全方向窗口。真实 ζ 是否满足这个截平发散条件，仍需要保留四频近共振、实部、系数相位和正侧归一化的联合估计；文献线索尚未替它付款，实际无条件半端点和 CM 满测也仍未裁定。

## 追加锚（本行以下为增补区）

## 45. 精确主计数与固定右侧能量界仍容许指定窗口列的全宽度集中

**定义 45.1（抽象位置谱、完整原系数与实际截窗矩）。** 固定 $1/2<b<1$、$0<\kappa<1$，记

$$
 c=b-\frac12,\qquad r=\kappa^{-1},\qquad
 q=\frac{1+r}{2},\qquad d=\frac{r-1}{2},\qquad
 C(U)=\frac{U}{2\pi}\log\frac{U}{2\pi}-\frac{U}{2\pi}.
 \tag{45.1}
$$

以下 $\mathcal Z_*$ 是另立的抽象复位置集合，不表示实际 $\zeta$ 零点。位置简单指每个复位置的重数为 $1$；允许两个不同实部的位置具有相同虚部。要求 $\mathcal Z_*$ 局部有限、位于 $0<\operatorname{Re}\rho<1$、$\operatorname{Im}\rho\ne0$，并在共轭及 $\rho\mapsto1-\rho$ 下封闭。以正虚部的全部复位置计数，定义

$$
 N_*(U)=\#\{\rho\in\mathcal Z_*:0<\operatorname{Im}\rho\le U\}.
 \tag{45.2}
$$

对固定 $\sigma>1/2$，令 $W_\sigma(U)$ 为 $\operatorname{Re}\rho\ge\sigma$、$|\operatorname{Im}\rho|\le U$ 的位置虚部多重集，按位置保留虚部的重复次数，并定义有序四元组能量

$$
 E_1(W)=\#\{(u_1,u_2,u_3,u_4)\in W^4:
                  |u_1+u_2-u_3-u_4|\le1\}.
 \tag{45.3}
$$

对每个截断 $T$，完整函数始终取为

$$
 F_T(y)=-\sum_{\substack{\rho\in\mathcal Z_*\\
                         |\operatorname{Im}\rho|\le T}}
                 \frac{e^{(\rho-b)y}}{\rho}\in\mathbb R.
 \tag{45.4}
$$

系数准确是 $-1/\rho$，共轭、反射、旧块和临界线背景全部进入同一个截断；求和集合、实部与相位均不依观察宽度重新选取。给定 $T_n=e^{t_n}$，在同一个区间 $I_n=[t_n,rt_n]$ 上，对每个实宽度 $1\le s\le t_n$ 定义截窗概率

$$
 \begin{aligned}
 y_n&=qt_n,&
 Z_{n,s}&=\int_{t_n}^{rt_n}
                    e^{-(y-y_n)^2/(2s^2)}\,dy,\\
 d\mu_{n,s}(y)&=\frac{\mathbf1_{I_n}(y)}{Z_{n,s}}
                     e^{-(y-y_n)^2/(2s^2)}\,dy,&
 M_{n,s}&=\mathbb E_{\mu_{n,s}}F_{T_n},\\
 V_{n,s}&=\mathbb E_{\mu_{n,s}}(F_{T_n}-M_{n,s})^2,&
 K_{n,s}&=\frac{\mathbb E_{\mu_{n,s}}(F_{T_n}-M_{n,s})^4}
                       {V_{n,s}^2}\quad(V_{n,s}>0).
 \end{aligned}
 \tag{45.5}
$$

**定理 45.2（一个固定谱上的计数、能量与全宽度反模型）。** 对定义 45.1 的每个固定 $b,\kappa$，存在一次构造的 $\mathcal Z_*$ 及同一列 $T_n\to\infty$，使

$$
 \sup_{\rho\in\mathcal Z_*}\operatorname{Re}\rho=b,
 \qquad \operatorname{Re}\rho<b\quad(\rho\in\mathcal Z_*),
 \tag{45.6}
$$

$$
 N_*(U)=C(U)+O(1),\qquad
 N_*(U+1)-N_*(U)\ll\log(U+2),
 \tag{45.7}
$$

且每个固定 $\sigma>1/2$、每个 $\varepsilon>0$ 均有

$$
 E_1(W_\sigma(U))\ll_{\varepsilon,\sigma,b,\kappa}U^\varepsilon
 \qquad(U\ge2).
 \tag{45.8}
$$

与此同时，充分大 $n$ 的全部 $1\le s\le t_n$ 都有 $V_{n,s}>0$，并且

$$
 \begin{gathered}
 \sup_{1\le s\le t_n}V_{n,s}\longrightarrow0,
 \qquad
 \sup_{1\le s\le t_n}\frac{|\log V_{n,s}|}{t_n}\longrightarrow0,\\
 \sup_{1\le s\le t_n}\frac{|M_{n,s}|}{\sqrt{V_{n,s}}}\longrightarrow0,
 \qquad
 \inf_{1\le s\le t_n}\frac{K_{n,s}}{t_n}\longrightarrow\infty.
 \end{gathered}
 \tag{45.9}
$$

这里 (45.7) 保留 Riemann--von Mangoldt 的指定主计数 $C$；它是构造谱的计数结论，没有断言实际 $\zeta$ 具有 $O(1)$ 计数余项。(45.9) 在同一指定窗口列上同时量化所有宽度，因而任何选择 $s_n\in[1,t_n]$ 都不能在这列上使 $K_{n,s_n}=O(t_n)$，更不能使 $K_{n,s_n}=o(s_n)$。结论不排除另选 $T$ 子列。

证明。所有渐近均在下述同一构造中令 $n\to\infty$；涉及宽度的 $o(1)$ 一致于整个 $[1,t_n]$。常数可以依赖固定 $b,\kappa$ 和有限低段，不能依赖 $n,s$。

先固定临界线基准。取足够大的整数 $\ell_0$，在 $C$ 严格递增的高处分支定义

$$
 \lambda_\ell=C^{-1}(\ell)\quad(\ell\ge\ell_0),
 \qquad
 \mathcal Z_0=\{\tfrac12\pm i\lambda_\ell:\ell\ge\ell_0\}.
 \tag{45.10}
$$

其正位置计数为 $C(U)+O(1)$。由

$$
 C'(U)=\frac1{2\pi}\log\frac U{2\pi},\qquad
 C''(U)=\frac1{2\pi U},
 \tag{45.11}
$$

均值定理给单位计数 $O(\log(U+2))$，求和分部给

$$
 \sum_{\lambda_\ell\le T}\frac1{|1/2+i\lambda_\ell|}
 \ll\log^2(T+2).
 \tag{45.12}
$$

这只是给定函数 $C$ 的反函数计数，不调用真实零点的任何解析性质。

共同参数按 $a_n\to h_n\to\delta_n$ 的顺序选取。置 $\delta_0=c/4$。第 $n$ 步，先取正整数 $D_n$ 足够大，使

$$
 a_n=\frac{2q}{D_n}\le
 \min\left\{\frac18,\frac1{n+10},
             \frac{\delta_{n-1}}{n+10},\frac c{n+10}\right\}.
 \tag{45.13}
$$

此后固定 $a_n$，再取正整数 $k_n$ 足够大，由

$$
 h_ne^{h_n}=\frac{2k_n}{D_n}
 \tag{45.14}
$$

唯一确定 $h_n>0$，并置

$$
 G_n=2\pi e^{h_n},\qquad t_n=\frac{h_n}{a_n},\qquad
 T_n=e^{t_n},\qquad m_n=\lfloor e^{\sqrt{h_n}}\rfloor.
 \tag{45.15}
$$

选取时同时要求

$$
 \begin{gathered}
 h_n\ge n^2+H_0,\qquad
 \log(1/a_n)\le\frac{\sqrt{h_n}}n,\qquad
 \log t_n\le\frac{h_n}{4},\\
 \frac{a_n^3m_n}{h_n^2}\ge n^2,\qquad
 \frac{m_nt_n}{G_n^2}\le\frac1n,\qquad
 \frac{m_n}{G_n}\le2^{-n},\qquad
 \frac{m_n^2}{G_nh_n^2}\le\frac1{100},\\
 2G_n+10<T_n,\qquad
 h_n>h_{n-1}+1,\qquad G_n>2T_{n-1}+10\quad(n>1).
 \end{gathered}
 \tag{45.16}
$$

其中 $H_0$ 是只依赖固定数据的足够大常数；首步不使用带 $n-1$ 的条件。最后才定义

$$
 \delta_n=\min\left\{\frac{\delta_{n-1}}2,
                         \frac{a_ne^{-4h_n}}{h_n}\right\},
 \qquad \beta_n=b-\delta_n.
 \tag{45.17}
$$

这些条件能共同实现。对于已固定的 $a_n,D_n,\delta_{n-1},T_{n-1}$，(45.14) 的正解随整数 $k_n$ 无界；(45.16) 每一条件都在该解的一个尾部成立。具体地，$e^{\sqrt h}$ 胜过 $h$ 的任意固定幂，而 $e^h$ 胜过 $e^{A\sqrt h}$ 的任意固定倍；固定 $a_n$ 的大小只决定此次尾部从何处开始。$\delta_n$ 后置，不对 $h_n$ 加任何上界。因此

$$
 a_n\to0,\quad \delta_n\downarrow0,\quad
 \frac{\delta_{n-1}}{a_n}\ge n+10,\quad
 \frac c{a_n}\ge n+10,\quad
 \delta_nt_n\le e^{-4h_n},\quad
 \log t_n=o(h_n).
 \tag{45.18}
$$

新位置和基准的替换采用同一 $h_n$。令

$$
 \Delta_n=\frac{4\pi}{h_n},\qquad
 \gamma_{n,j}=G_n+\Delta_nj\quad(0\le j<m_n),\qquad
 \ell_n=\lfloor C(G_n)\rfloor.
 \tag{45.19}
$$

对每个 $j$，从 $\mathcal Z_0$ 移除 $\lambda_{\ell_n+2j}$、$\lambda_{\ell_n+2j+1}$ 上的两个临界线位置及其共轭，放入四个不同位置

$$
 \beta_n\pm i\gamma_{n,j},\qquad
 1-\beta_n\pm i\gamma_{n,j}.
 \tag{45.20}
$$

$\mathcal Z_*$ 定义为全部这些替换与全部未移除基准位置的并。以下证明替换支撑彼此不交，故此定义一次完成，此后不随 $T$ 或 $s$ 改写。

计数须逐位置配对。Taylor 公式和 (45.11) 给

$$
 C(\gamma_{n,j})=C(G_n)+2j+
             O\left(\frac{m_n^2}{G_nh_n^2}\right),
 \tag{45.21}
$$

误差一致于整个块，且趋零。这里的线性项准确是 $2j$，因为 $h_n=\log(G_n/(2\pi))$。$\ell_n$ 的取整误差小于 $1$，故对 $v=0,1$ 有

$$
 |C(\gamma_{n,j})-(\ell_n+2j+v)|\le2
 \tag{45.22}
$$

对足够大的 $H_0$ 成立。反函数的均值定理于是给一个固定常数 $C_0$，使

$$
 |\lambda_{\ell_n+2j+v}-\gamma_{n,j}|\le\frac{C_0}{h_n}.
 \tag{45.23}
$$

确实，在 $[G_n-1,2G_n]$ 上 $C'\asymp h_n$；从 (45.22) 先把反函数值夹在该区间，再应用均值定理即可。增大 $H_0$ 后，每个块全部新旧配对支撑都在

$$
 J_n=\left[G_n-\frac{C_0}{h_n},
        G_n+\Delta_n(m_n-1)+\frac{C_0}{h_n}\right]
       \subset(G_n-1,2G_n).
 \tag{45.24}
$$

由 (45.16)，各 $J_n$ 两两不交且依次升高；移除的索引没有重复。把每个新正位置分别配给一个旧正位置，完整通过一个块时正位置净增为零。任意截断 $U$ 上未完成的配对，必须有旧高度落在 $[U-C_0/h_n,U+C_0/h_n]$。该区间由 $C'\asymp h_n$ 只含 $O(1)$ 个基准高度；并且至多一个 $J_n$ 能含此类未完成配对。因此任意 $U$ 都有 $N_*(U)-N_0(U)=O(1)$，统一常数不随块数增长。这证明 (45.7)，包括其单位计数。

每个四元组 (45.20) 共轭及反射闭合。由 $0<\delta_n<c/4$ 可知 $1/2<\beta_n<b<1$，而 $0<1-\beta_n<1/2$；位置重数均为 $1$。支撑升高使谱局部有限，$\beta_n\uparrow b$ 证明 (45.6)。固定 $\sigma>1/2$ 后，基准与左反射均不进入 $W_\sigma$。若 $G_n\le U<G_{n+1}$，则

$$
 |W_\sigma(U)|\le2\sum_{j\le n}m_j\le2nm_n,
 \qquad
 \frac{\log(2nm_n)}{\log U}
 \le\frac{\log(2n)+\sqrt{h_n}}{h_n+\log(2\pi)}\longrightarrow0.
 \tag{45.25}
$$

部分块及块间长空隙也满足此界。于是平凡计数 $E_1(W)\le|W|^4$ 就给 (45.8)，无需任何频差或独立性假设。$\sigma\ge b$ 时集合为空；(45.8) 只声称上界。

接着核算同一完整函数的矩。固定 $n$，简记 $h,a,t,G,m,\delta,\beta,\Delta$，置 $y_0=qt$、$x=y-y_0$。当前右块及其共轭的准确贡献为

$$
 B_n(y)=2\operatorname{Re}\sum_{j<m}
          \frac{-1}{\beta+i\gamma_{n,j}}
                    e^{-\delta y+i\gamma_{n,j}y},
 \qquad R_n(y)=F_{T_n}(y)-B_n(y).
 \tag{45.26}
$$

$R_n$ 包括全部旧右块、全部已入截断的左反射、全部未移除临界线背景；没有删去其中任何位置。(45.16)、(45.24) 保证当前块全部进入 $T_n$，未来块全部在 $T_n$ 之外。因为 $\sum_jm_j/G_j\le1$，旧右块在 $I_n$ 上的绝对和至多 $C e^{-\delta_{n-1}t}$；首步旧块为空。每个反射位置的衰减缺口准确是

$$
 b-(1-\beta_j)=2c-\delta_j\ge\frac{7c}{4}>c.
 \tag{45.27}
$$

其全部绝对和至多 $C e^{-ct}$；临界线部分由 (45.12) 至多 $C t^2e^{-ct}$。因此

$$
 \|R_n\|_{L^\infty(I_n)}
 \le C\left[e^{-\delta_{n-1}t}+(1+t^2)e^{-ct}\right]
 \le e^{-3h}.
 \tag{45.28}
$$

最后一个不等式同时使用 (45.18)、$\log t\le h/4$，并由足够大的固定 $H_0$ 吸收常数。这里的 $C$ 可先由 (45.12) 及 $\sum m_j/G_j\le1$ 固定，不依赖尚未选取的未来块。

原系数在证明内的近似也须相对矩支付。均匀于 $j<m$，有

$$
 \frac{-1}{\beta+i\gamma_{n,j}}
       =\frac{i}{G}+O\left(\frac{1+m/h}{G^2}\right).
 \tag{45.29}
$$

令 $P_n^0(y)=2\operatorname{Re}\{(i/G)\sum_{j<m}e^{i\gamma_{n,j}y}\}$。由 (45.18)，在整个实际 $I_n$ 上

$$
 \|B_n-P_n^0\|_\infty\le\eta_n,
 \qquad
 \eta_n=C_\kappa\left[
          \frac{m(1+m/h)}{G^2}+\frac{m}{G}e^{-4h}\right].
 \tag{45.30}
$$

这只用于估计，(45.4)、(45.26) 的系数仍准确保留。为预先固定相对尺度，记 $p=2,4$ 时

$$
 A_p(s)=\left(\frac{m^{p-1}h}{G^ps}\right)^{1/p},
 \quad
 A_2(t)=\frac{\sqrt{ma}}G,\quad
 A_4(t)=\frac{m^{3/4}a^{1/4}}G.
 \tag{45.31}
$$

(45.15)、(45.16) 直接给

$$
 \frac{e^{-3h}+\eta_n}{A_p(t)}\longrightarrow0
 \qquad(p=2,4).
 \tag{45.32}
$$

例如系数误差除以 $A_2(t)$ 至多
$C\sqrt m(1+m/h)/(G\sqrt a)$，其对数为 $-h+O(\sqrt h+\log(1/a))\to-\infty$；除以 $A_4(t)$ 同样成立。其余两项更小。因为 $A_p(s)\ge A_p(t)$，这是全部宽度共同的相对误差预算，未以峰高 $m/G$ 代替实际范数。

在实际截窗上，直接换元得到

$$
 Z_{n,s}=s\int_{-dt/s}^{dt/s}e^{-u^2/2}\,du,
 \qquad c_\kappa s\le Z_{n,s}\le C s
 \quad(1\le s\le t).
 \tag{45.33}
$$

故密度处处至多 $C_\kappa/s$。取足够小的固定 $\epsilon>0$，令 $w=\epsilon h/m$。则 $w\to0$，$[-w,w]\subset[-dt,dt]$，且峰区 $|x|\le w$ 上密度至少 $c_\kappa/s$，一致于全部宽度。

(45.13)--(45.15) 的校准准确给

$$
 Gqt=2\pi k_n,\qquad \Delta qt=2\pi D_n,\qquad
 \gamma_{n,j}=\frac{2\pi(k_n+D_nj)}{qt}.
 \tag{45.34}
$$

因此令 $\Omega=G+(m-1)\Delta/2$，有有限几何和恒等式

$$
 \begin{aligned}
 \sum_{j<m}e^{i\gamma_{n,j}(y_0+x)}
   &=e^{i\Omega x}\mathcal D_m(x),\\
 \mathcal D_m(x)&=\frac{\sin(m\Delta x/2)}{\sin(\Delta x/2)},
 \qquad \mathcal D_m(0)=m,\\
 P_n^0(y_0+x)&=-\frac2G\mathcal D_m(x)\sin(\Omega x).
 \end{aligned}
 \tag{45.35}
$$

商式 $\mathcal D_m$ 在全部可去奇点按连续延拓解释。在 $|x|\le w$ 上 $\mathcal D_m(x)\ge m/2$，但实函数还含快速振荡的 $\sin(\Omega x)$，中心本身为零，并非处处同号峰。由于 $\Omega w\to\infty$，直接积分 $\sin^2$、$\sin^4$ 的三角恒等式给

$$
 \int_{-w}^{w}|\sin(\Omega x)|^p\,dx
       \ge c_p w\qquad(p=2,4),
 \tag{45.36}
$$

边界余项为 $O(1/\Omega)$。结合实际密度下界，得到

$$
 \|P_n^0\|_{L^p(\mu_{n,s})}\ge c_\kappa A_p(s)
 \qquad(p=2,4).
 \tag{45.37}
$$

(45.30)--(45.32) 和范数三角不等式遂给准确 $B_n$ 同样的下界。

二阶上界直接用实际复系数的周期正交。写 $d_j=-1/(\beta+i\gamma_{n,j})$，令

$$
 P_n(y)=2\operatorname{Re}\sum_{j<m}d_je^{i\gamma_{n,j}y},
 \qquad B_n(y)=e^{-\delta y}P_n(y).
 \tag{45.38}
$$

由 (45.34)，$qt$ 是一个周期，正、负整数频率均互异且不为零，故任意完整周期准确有

$$
 \int_v^{v+qt}P_n(y)^2\,dy=2qt\sum_{j<m}|d_j|^2.
 \tag{45.39}
$$

$I_n$ 的长度 $(r-1)t<2qt$；非负周期函数在该区间的积分至多两个完整周期之和。在 $I_n$ 上 $e^{-\delta y}\le1$，且 $|d_j|\ll1/G$，故

$$
 \mathbb E_{\mu_{n,s}}B_n^2
 \le\frac{C_\kappa}{s}\int_{I_n}B_n^2\,dy
 \le\frac{C_\kappa mt}{G^2s}.
 \tag{45.40}
$$

这一步不需要大筛接口，也没有用全轴高斯代替截窗概率。

设 $Q_p(H)=\mathbb E_{\mu_{n,s}}|H|^p$。由 (45.28)、(45.32)、(45.37)，$R_n$ 相对准确 $B_n$ 的二、四阶范数均为 $o(1)$，所以

$$
 Q_p(F_{T_n})=(1+o(1))Q_p(B_n)\quad(p=2,4),
 \tag{45.41}
$$

$$
 \frac{c_\kappa mh}{G^2s}\le Q_2(F_{T_n})
           \le\frac{C_\kappa mt}{G^2s},\qquad
 Q_4(F_{T_n})\ge\frac{c_\kappa m^3h}{G^4s}.
 \tag{45.42}
$$

这控制的是完整函数在实际概率空间上的矩；(45.42) 二阶两端的比值允许为 $t/h=1/a$，没有声称它们固定倍数等价。

均值单独支付截窗端点。把

$$
 f_\delta(y)=\frac{\mathbf1_{I_n}(y)}{Z_{n,s}}
         e^{-(y-y_0)^2/(2s^2)-\delta y}
 \tag{45.43}
$$

在 $I_n$ 外延零。区间内它是单峰函数，$\sup f_\delta\le C_\kappa/s$；计入两端跳跃后的全变差至多 $2\sup f_\delta$。Stieltjes 分部积分因而给

$$
 \left|\int_{\mathbb R}e^{i\gamma y}f_\delta(y)\,dy\right|
 \le\frac{\operatorname{Var}(f_\delta)}{|\gamma|}
 \le\frac{C_\kappa}{|\gamma|s}.
 \tag{45.44}
$$

用 $\gamma_{n,j}\ge G$、$|d_j|\ll1/G$ 和 (45.28)，得到

$$
 |M_{n,s}|\le\frac{C_\kappa m}{G^2s}+e^{-3h},
 \qquad
 \sup_{1\le s\le t}\frac{|M_{n,s}|}{\sqrt{Q_2(F_{T_n})}}
 \le\frac{C_\kappa\sqrt m}{G\sqrt h}
             +\frac{C_\kappa e^{-3h}}{A_2(t)}\longrightarrow0.
 \tag{45.45}
$$

这里包括 $s=t$ 时不可删去的端点质量。由 $V=Q_2-M^2$，有
$V_{n,s}=(1+o(1))Q_2(F_{T_n})>0$。又在概率空间上 $\|F\|_4\ge\|F\|_2$，所以 (45.45) 亦给 $|M|/\|F\|_4\to0$。再次用范数三角不等式，得

$$
 \mathbb E_{\mu_{n,s}}(F_{T_n}-M_{n,s})^4
       =(1+o(1))Q_4(F_{T_n}).
 \tag{45.46}
$$

因此中心化没有损失 (45.42) 的相对二阶及四阶尺度。

最后由 (45.42)、(45.45) 得

$$
 \frac{c_\kappa mh}{G^2s}\le V_{n,s}
       \le\frac{C_\kappa mt}{G^2s},
 \qquad
 \log V_{n,s}=-2h+o(h)
 \quad(1\le s\le t),
 \tag{45.47}
$$

其中 $\log m=\sqrt h+o(1)$、$\log G=h+\log(2\pi)$、$\log t=o(h)$。由 $a_n\to0$ 及 $t=h/a$，对数结论给 $\sup_s|\log V|/t\to0$；由 (45.16) 的 $mt/G^2\le1/n$ 得 $\sup_sV\to0$。均值结论已在 (45.45) 支付。中心化四阶下界除以方差上界的平方，准确给

$$
 K_{n,s}\ge c_\kappa\frac{mhs}{t^2},\qquad
 \inf_{1\le s\le t}\frac{K_{n,s}}t
       \ge c_\kappa\frac{mh}{t^3}
       =c_\kappa\frac{a^3m}{h^2}
       \ge c_\kappa n^2\longrightarrow\infty.
 \tag{45.48}
$$

同一共同递归同时支付了块分离、中心相位、计数曲率、原系数近似、完整背景和全部宽度；不存在把不同实现上分别可达的界拼接的问题。这完成 (45.9)。$\square$

附于定理 45.2 的来源与适用边界如下。有限几何和的 Dirichlet 核、Taylor 公式、反函数均值定理、求和分部、周期正交、截窗归一化、变差积分及范数三角不等式均是成熟中间工具，不作为本条新增结论。$E_1$ 的虚部多重集、容差 $1$ 定义与 Tao--Trudgian--Yang，*New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach*，[arXiv:2501.16779v1](https://arxiv.org/html/2501.16779v1)，Definition 7 一致；其 Definition 56、Remark 57 讨论实际 $\zeta$、固定 $\sigma$ 及虚部重数。本条只借用这一术语，(45.8) 由 (45.25) 的平凡计数独立给出，不调用该文的零密度或能量指数定理，也不把固定尺度比较换成随窗缩小的频差估计。本条的 repo-derived 数学内容是 (45.10)--(45.20) 定义的同一个固定谱同时满足 (45.6)--(45.9) 的共同构造；不主张这些经典输入或该构造的文献优先性。

用白话说，先在临界线上铺出具有准确主计数的密集背景，再在极稀疏的高度上把成对背景位置移成一右一左。每次只移动很短的高度距离，所以任意截断处的计数误差始终有界。右侧块的总人数在高度的幂指数上极少，足以满足每个固定实部阈值的能量上界；但一个右块内部仍能在预先固定的窗中心附近同相叠加，形成包络很窄、内部快速正负振荡的波包。块高选定后再取足够小的实部缺口，使当前波包尚未衰减；先前的缺口则让所有旧块在新窗口内衰减。即使允许高斯宽度从 $1$ 一直选到整个对数窗尺度，四阶集中都无法在指定窗口列上被宽度选择消除。该结论处理的是一个固定谱的共同实现，不是逐窗换谱，也不是仅找到一个坏宽度。

这个反模型只否定由 (45.6)--(45.8) 这些抽象数据直接保证指定窗口列存在有利宽度的推断；它不证明所有 $T$ 都失败，也不排除模型自身另有有利 $T$ 子列。尤其 $\mathcal Z_*$ 未被赋予 Euler 乘积、实际 $\zeta$ 的解析函数或算术显式公式，不能把 (45.4) 代入 §44 的同一实际 $\psi$ 关系。真实 $\zeta$ 仍需另证：在同一实际窗口上，把实部缺口、原 $-m_\rho/\rho$ 系数、四频近共振、真实相位与正侧能量归一化联合控制，从而取得可供 §44 消费的不重复计时的参与长度发散；或者找到另一个保留全部实际条件的充分路线。固定 $\sigma$ 的无权能量幂界与主计数本身没有给出这条联合关系。

因此 §§42--44 的实际条件结论保持原范围：取得边界的消费者没有被反驳，未取得边界下真实原负阶段的半端点谐和占用仍未支付，$\sum_H\eta_H/H$ 的无条件发散仍未由此得到。即便以后取得完整全方向几何预算发散，§41 在同一 $Y$ 上实际 CM 方向的分箱凝聚或足够的跨块联合能量桥仍须另证，实际 $\nu(R_{1/2}(\alpha))$ 满测仍未裁定。原 $q_H$、CM 实际点对、全部有限地方及每个事件中的同一个成功整数均保持原义，未被抽象谱替代。

## 追加锚（本行以下为增补区）

## 46. 人工参考谱的同主部单调双实现与有限／余有限负占用

本节固定一个人工参考谱，给出两个连续非负计数的共同构造。这里的“同主部”指各自的误差变换与同一个参考变换之差均为整函数；它不表示完整变换相等，也不表示保留普通素数、实际零点残差或任意指定的实际芽。负占用的有限与余有限均按对数时间的 Lebesgue 测度理解。

**定义 46.1（参考函数、可变正核与两种尾部）。** 固定实数 $1/2<b<1$ 和整数 $m>4$，置

$$
\begin{gathered}
c=b-\frac12,\qquad
\beta_n=b-\frac{c}{n+1},\qquad
a_n=e^{-n^4},\qquad
\rho_{n,\pm}=\beta_n\pm in\quad(n\ge1),\\
f_0(z)=\sum_{n\ge1}a_ne^{\beta_nz}\cos(nz),\qquad
F_0(s)=\int_0^\infty f_0(y)e^{-sy}\,dy
\quad(\operatorname{Re}s>b).
\end{gathered}
\tag{46.1}
$$

以下 $\beta_n$ 只属于这个人工谱，与 §§43–44 的实际零点序列及原过滤参数无关。对实数 $y\ge1$ 定义

$$
\begin{gathered}
\phi(y)=y^{3/2},\qquad w(y)=e^{-y^2},\\
K_y(\theta)=\sum_{k\in\mathbb Z}e^{-k^2/y^m}e^{ik\theta},
\qquad K(y)=K_y(\phi(y)),\\
u_+(y)=w(y)+(f_0(y)-w(y))K(y),\\
u_-(y)=-w(y)+(f_0(y)+w(y))K(y),\\
d(\theta)=\operatorname{dist}(\theta,2\pi\mathbb Z),\qquad
U_* =\{y\ge1:d(\phi(y))<4y^{1-m/2}\}.
\end{gathered}
\tag{46.2}
$$

**定理 46.2（同一参考谱的有限／余有限双实现）。** 存在整数 $Y_0\ge8$，使所有 $y\ge Y_0$ 同时满足

$$
\begin{gathered}
\max_{j\in\{+,-\}}|u_j(y)|\le\frac{e^y}{4},\qquad
\max_{j\in\{+,-\}}|u_j'(y)|\le\frac{e^y}{2},\qquad
4y^{1-m/2}\le1,\\
\max\{|(f_0(y)-w(y))K(y)|,|(f_0(y)+w(y))K(y)|\}
\le\frac{w(y)}2\quad(y\notin U_*).
\end{gathered}
\tag{46.3}
$$

为使两个计数完全确定，取满足 (46.3) 的最小整数 $Y_0\ge8$，令 $X=e^{Y_0}$，并对 $j\in\{+,-\}$ 置

$$
\begin{gathered}
q_j=\frac{X+u_j(Y_0)}{X-1},\\
S_j(x)=
\begin{cases}
0,&0\le x\le1,\\
q_j(x-1),&1\le x\le X,\\
x+u_j(\log x),&x\ge X,
\end{cases}
\qquad
g_j(y)=S_j(e^y)-e^y\quad(y\ge0).
\end{gathered}
\tag{46.4}
$$

这两个实际定义的函数具有下列共同性质与相反的负占用：

1. $S_j$ 非负、连续、局部绝对连续且非减；其 Stieltjes 测度非负且相对于 $dx$ 绝对连续，并且

   $$
   dS_j(x)=S_j'(x)\,dx,\qquad
   \frac12\le S_j'(x)\le\frac32
   \quad\text{对几乎所有 }x\ge1.
   \tag{46.5}
   $$

   不要求密度在补接点连续。

2. 当 $x\to\infty$ 时，

   $$
   S_j(x)-x=O\!\left(x^b(\log x)^{m/2}\right)
   =O_\varepsilon(x^{b+\varepsilon})
   \quad(\text{每个 }\varepsilon>0).
   \tag{46.6}
   $$

3. 误差的 Laplace 变换及其等价的普通 Mellin 变换

   $$
   G_j(s)=\int_0^\infty g_j(y)e^{-sy}\,dy
   =\int_1^\infty(S_j(x)-x)x^{-s-1}\,dx
   \quad(\operatorname{Re}s>b)
   \tag{46.7}
   $$

   初始绝对收敛，且 $G_+-F_0$、$G_--F_0$ 分别延拓为单值整函数。$F_0,G_+,G_-$ 的全部极点恰为 $\rho_{n,\pm}$，均为简单非实极点，在每一点的完整主部都是

   $$
   \frac{a_n/2}{s-\rho_{n,\pm}}.
   \tag{46.8}
   $$

   留数非零；三个变换在全部实点正则。非实极点实部的上确界为 $b$，没有极点取得它，实点 $b$ 本身也正则。

4. Mellin–Stieltjes 变换

   $$
   M_j(s)=\int_1^\infty x^{-s}\,dS_j(x)
   \quad(\operatorname{Re}s>1)
   \tag{46.9}
   $$

   初始绝对收敛，且 $M_j(s)-1/(s-1)-sF_0(s)$ 整。$M_j$ 的全部主部为

   $$
   \frac1{s-1}\quad(s=1),\qquad
   \frac{\rho_{n,\pm}a_n/2}{s-\rho_{n,\pm}}
   \quad(s=\rho_{n,\pm}).
   \tag{46.10}
   $$

   这些留数也全部非零，没有其他极点；$M_j-1/(s-1)$ 在全部实点正则。两个变换 $M_+,M_-$ 之差整。

5. 令

   $$
   D_j=\{y\ge0:g_j(y)<0\}.
   $$

   则

   $$
   |D_+|<\infty,\qquad
   |[0,\infty)\setminus D_-|<\infty.
   \tag{46.11}
   $$

   等价地，$S_+(x)<x$ 的对数占用 $\int_1^\infty\mathbf1_{\{S_+(x)<x\}}\,dx/x$ 有限，而 $S_-(x)\ge x$ 的对数占用有限。特别地 $|D_-|=\infty$；这里得到的是测度余有限，强于仅有无穷多次负值，并不声称某一有限时刻后处处为负。

**证明。** 以下所有常数允许依赖固定的 $b,m$，不依赖正在求和的 $n,k$。

（甲）参考函数的解析增长与全部主部。在 $|z|\le R$ 上，第 $r$ 阶导数级数由
$C_r\sum_na_n(1+n)^re^{bR+nR}$ 控制，因此 $f_0$ 是整函数。写 $z=t+iv$、$t\ge0$，由
$n|v|\le n^4/2+C|v|^{4/3}$ 得

$$
|f_0(t+iv)|\le A\exp\{bt+C|v|^{4/3}\},\qquad
|f_0(y)|+|f_0'(y)|\le Ae^{by}\quad(y\ge0).
\tag{46.12}
$$

这里实轴上界使用 $\beta_n\le b$；$\beta_1$ 不能作为全级数的指数上界，因为 $\beta_n\uparrow b$。

对 $\sigma=\operatorname{Re}s>b$，逐项 Laplace 积分的绝对总量至多
$\sum_na_n/(\sigma-\beta_n)<\infty$。故

$$
F_0(s)=\frac12\sum_{n\ge1}a_n
\left(\frac1{s-\rho_{n,+}}+\frac1{s-\rho_{n,-}}\right)
=\sum_{n\ge1}\frac{a_n(s-\beta_n)}{(s-\beta_n)^2+n^2}.
\tag{46.13}
$$

在避开所列极点的任意紧集 $|s|\le R$ 上，充分大的 $n$ 的成对项为 $O_R(a_n/n^2)$，故该级数正常收敛。所列极点无有限聚点；每一点只有其自身的一项有极点，留数恰为 $a_n/2\ne0$。这证明参考变换的全部主部、实轴正则与未取得上确界，不在实轴另添 $b$ 极点。

（乙）正核、可变参数的导数成本及槽外符号。令 $a=y^{m/2}$。周期高斯的第 $k$ 个 Fourier 系数由普通高斯积分给出：

$$
\frac{\sqrt\pi a}{2\pi}\int_{\mathbb R}
 e^{-a^2t^2/4}e^{-ikt}\,dt=e^{-k^2/a^2}.
$$

两个周期级数均绝对收敛，因而

$$
K_y(\theta)=\sqrt\pi y^{m/2}
\sum_{\ell\in\mathbb Z}
\exp\!\left(-\frac{y^m(\theta-2\pi\ell)^2}{4}\right)>0.
\tag{46.14}
$$

这只是共同构造中使用的经典高斯 Fourier 恒等式。由高斯和与积分的比较，对 $q=0,1,2$ 有

$$
\sum_{k\in\mathbb Z}|k|^qe^{-k^2/y^m}
\le C_qy^{m(q+1)/2}\quad(y\ge1),
\tag{46.15}
$$

其中 $q=0$ 时 $k=0$ 项取 $1$。在每个实紧区间上可逐项求导，得到

$$
\begin{aligned}
K'(y)&=\sum_{k\in\mathbb Z}e^{-k^2/y^m+ik\phi(y)}
 \left(mk^2y^{-m-1}+\frac32iky^{1/2}\right),\\
|K(y)|&\le Cy^{m/2},\\
|K'(y)|&\le C\left(y^{m/2-1}+y^{m+1/2}\right)
\le Cy^{m+1/2}.
\end{aligned}
\tag{46.16}
$$

因此可变宽度与可变相位的代价均已计入；结合 (46.12) 和 $w'=-2yw$，两种尾部同时满足

$$
|u_j(y)|\le Ce^{by}y^{m/2},\qquad
|u_j'(y)|\le Ce^{by}y^{m+1/2}.
\tag{46.17}
$$

因 $b<1$，这两个量均为 $o(e^y)$。

将 (46.14) 的每个指数分成两半，一半提出最近距离，另一半的高斯格点和在 $a\ge1$ 及一个周期内一致有界，得

$$
0<K_y(\theta)\le Cy^{m/2}
 \exp\!\left(-\frac{y^m d(\theta)^2}{8}\right).
\tag{46.18}
$$

当 $y\notin U_*$ 时，右端至多 $Cy^{m/2}e^{-2y^2}$。从而

$$
|(f_0(y)\pm w(y))K(y)|
\le Cy^{m/2}e^{by-2y^2}=o(w(y))
\quad(y\to\infty,\ y\notin U_*).
$$

这与 (46.17) 一起证明 (46.3) 确有解，最小整数 $Y_0$ 因而有定义；固定此 $Y_0$ 后，在 $[Y_0,\infty)\setminus U_*$ 上有严格符号

$$
u_+(y)\ge\frac{w(y)}2>0,\qquad
u_-(y)\le-\frac{w(y)}2<0.
\tag{46.19}
$$

（丙）全部槽的总长度。置 $U=U_*\cap[Y_0,\infty)$。按距离最近的 $2\pi\ell$ 分槽；由 (46.3)，每个相关槽内
$|y^{3/2}-2\pi\ell|<1$。除有限个低槽外，$\ell\ge1$ 且 $y$ 与
$y_\ell=(2\pi\ell)^{2/3}$ 一致可比，该槽包含在

$$
|\phi(y)-2\pi\ell|\le C y_\ell^{1-m/2}
$$

所定义的区间内。因 $\phi'(y)=3y^{1/2}/2$，中值定理给该槽的长度上界

$$
C y_\ell^{(1-m)/2}=C'\ell^{(1-m)/3}.
\tag{46.20}
$$

$m>4$ 使其对 $\ell$ 可和，故 $|U|<\infty$。由 (46.19)，
$D_+\subseteq[0,Y_0]\cup U$，且 $[0,\infty)\setminus D_-\subseteq[0,Y_0]\cup U$。有限补接只占有限对数时间，得到 (46.11)。核在槽外仍严格正，本证明没有将它当作紧支撑核。

（丁）分别转动模态所用的支与扇区。需要证明的核心修正是

$$
E_K(s)=\int_{Y_0}^\infty f_0(y)(K(y)-1)e^{-sy}\,dy
\quad(\operatorname{Re}s>b)
\tag{46.21}
$$

具有整延拓。固定 $\alpha_0=\pi/(4m)$；在 $|\arg z|\le\alpha_0$、$|z|\ge Y_0$ 上使用右半平面主支 $\operatorname{Log}z$，以此定义 $z^{3/2}$。$z^{-m}$ 是普通整数幂，所有路径均避开 $0$。对 $\epsilon\in\{1,-1\}$、$k\ge1$ 置

$$
B_{\epsilon,k}(z,s)
=f_0(z)\exp\{-sz-k^2z^{-m}+i\epsilon k z^{3/2}\}.
\tag{46.22}
$$

正模态只转入上扇区，负模态只转入下扇区。在
$z=re^{i\epsilon u}$、$0\le u\le\alpha_0$ 上，

$$
\begin{gathered}
\operatorname{Re}z^{-m}=r^{-m}\cos(mu)\ge \kappa_0r^{-m},
\qquad \kappa_0=\cos(\pi/4)>0,\\
\left|e^{i\epsilon kz^{3/2}}\right|
=e^{-kr^{3/2}\sin(3u/2)}.
\end{gathered}
\tag{46.23}
$$

两类模态因此分别衰减；不能把两类模态一并转入同一个上扇区。

（戊）有限内弧、无穷射线及紧一致性。令 $A_\epsilon$ 是从 $Y_0$ 到 $Y_0e^{i\epsilon\alpha_0}$ 的圆弧，$L_\epsilon$ 是从 $Y_0e^{i\epsilon\alpha_0}$ 沿辐角 $\epsilon\alpha_0$ 指向无穷的射线。定义

$$
\widetilde E_K(s)=\sum_{\epsilon=\pm1}\sum_{k\ge1}
\left(\int_{A_\epsilon}B_{\epsilon,k}(z,s)\,dz
     +\int_{L_\epsilon}B_{\epsilon,k}(z,s)\,dz\right).
\tag{46.24}
$$

在任意 $|s|\le R$ 上，有限内弧的 $f_0(z)e^{-sz}$ 有统一界，模态因子至多
$e^{-\kappa_0k^2/Y_0^m}$。故内弧积分的模态级数绝对且紧一致收敛。

射线上置 $\kappa_1=\sin(3\alpha_0/2)>0$；由几何级数估计，$r\ge Y_0$ 时

$$
\sum_{k\ge1}e^{-\kappa_0k^2/r^m-\kappa_1kr^{3/2}}
\le\frac{e^{-\kappa_1r^{3/2}}}{1-e^{-\kappa_1Y_0^{3/2}}}.
$$

再由 (46.12)，所有射线模态的积分绝对总量在 $|s|\le R$ 上统一受控于

$$
A_R\int_{Y_0}^\infty
\exp\{-\kappa_1r^{3/2}+Cr^{4/3}+(b+R)r\}\,dr<\infty.
\tag{46.25}
$$

这里 $4/3<3/2$。各个有限弧积分和射线积分均是 $s$ 的整函数；上述可积控制和内弧高斯控制允许积分、模态求和换序，并保证所得级数在每个 $s$ 紧集上一致收敛。因此 (46.24) 是单值整函数。此论证只对单个模态作 $z$ 的解析延拓，没有假设可变参数的整个 Fourier 和在全部复 $z$ 平面整。

（己）外弧归零与初始半平面的回接。写 $s=\sigma+it$、$\sigma>b$，$\delta=\sigma-b>0$。取 $\kappa_2>0$ 使
$\sin(3u/2)\ge \kappa_2u$ 对 $0\le u\le\alpha_0$ 成立。在半径 $L$ 的外弧 $z=Le^{i\epsilon u}$ 上，(46.12)、(46.23) 给出

$$
|B_{\epsilon,k}(z,s)|\le A\exp\left\{
-\delta L\cos u+CL^{4/3}u^{4/3}+|t|Lu
-\kappa_0k^2/L^m-\kappa_2kL^{3/2}u\right\}.
\tag{46.26}
$$

对整个 $u\in[0,\alpha_0]$，当 $L$ 足够大时

$$
CL^{4/3}u^{4/3}+|t|Lu
\le\frac{\kappa_2}{2}L^{3/2}u,
$$

因为在 $u>0$ 除以 $L^{3/2}u$ 后，上界为
$CL^{-1/6}\alpha_0^{1/3}+|t|L^{-1/2}\to0$，而 $u=0$ 时两边均为零。使用 $k\ge1$ 吸收此项，再对模态求和并乘弧长，全部外弧积分绝对总量至多

$$
CL^{m/2+1}e^{-\delta L\cos\alpha_0}\longrightarrow0.
\tag{46.27}
$$

在初始半平面的任意紧集上，$\delta$ 有统一正下界、$|t|$ 有统一上界，故这里也紧一致。

每个 $B_{\epsilon,k}$ 在相应环扇形内关于 $z$ 全纯。对有限环扇形应用 Cauchy 定理，令 $L\to\infty$ 并使用 (46.27)，得到

$$
\int_{Y_0}^\infty B_{\epsilon,k}(y,s)\,dy
=\int_{A_\epsilon}B_{\epsilon,k}(z,s)\,dz
 +\int_{L_\epsilon}B_{\epsilon,k}(z,s)\,dz.
$$

原实射线上的模态求和也绝对可积：由 (46.12)、(46.15)，

$$
\sum_{\epsilon=\pm1}\sum_{k\ge1}
\int_{Y_0}^\infty|f_0(y)|e^{-\sigma y-k^2/y^m}\,dy
\le C\int_{Y_0}^\infty e^{-(\sigma-b)y}y^{m/2}\,dy<\infty.
\tag{46.28}
$$

所以可将上述等式求和；$K-1$ 正是这些非零模态之和，得到
$\widetilde E_K=E_K$ 于 $\operatorname{Re}s>b$。至此既证明整性，也证明它确为原修正积分的延拓，而非只构造一个无回接的整函数。

（庚）两个误差分别回到同一个参考。背景项

$$
V(s)=\int_{Y_0}^\infty w(y)(1-K(y))e^{-sy}\,dy
$$

直接定义整函数：在 $|s|\le R$ 上被积函数的绝对值至多
$e^{-y^2+Ry}(1+Cy^{m/2})$。有限段修正

$$
C_j(s)=\int_0^{Y_0}(g_j(y)-f_0(y))e^{-sy}\,dy
$$

也整，因为它只在固定紧区间积分。由 (46.2)、(46.4)，在初始半平面有

$$
G_+=F_0+\widetilde E_K+V+C_+,\qquad
G_-=F_0+\widetilde E_K-V+C_-.
\tag{46.29}
$$

故两个差 $G_j-F_0$ 各自整，而非仅仅 $G_+-G_-$ 整。结合（甲），全部非实极点、非零留数和完整主部均逐一保留，实轴没有新奇点。

（辛）有限补接的正性与全域斜率。由 (46.3)，$|u_j(Y_0)|\le X/4$，从而

$$
q_j>0,\qquad
|q_j-1|=\frac{|1+u_j(Y_0)|}{X-1}
\le\frac{1+X/4}{X-1}\le\frac12
\quad(X\ge6).
\tag{46.30}
$$

这里 $Y_0\ge8$ 保证 $X\ge6$。在 $1<x<X$ 上 $S_j'=q_j\in[1/2,3/2]$；在 $x>X$ 上由链式法则，

$$
S_j'(x)=1+x^{-1}u_j'(\log x)\in[1/2,3/2].
\tag{46.31}
$$

两个定义在 $x=1,X$ 分别取共同值 $0,X+u_j(Y_0)$，故没有跳跃原子；有限段与光滑尾部在每个紧区间连续拼接成绝对连续函数。由正斜率与 $S_j(1)=0$，计数非负、非减，且 (46.5) 在全部 $x\ge1$ 几乎处处成立。增长式 (46.6) 则由 (46.17) 得到。

（壬）Mellin–Stieltjes 的下端项。由 (46.5) 可知 (46.9) 在 $\operatorname{Re}s>1$ 绝对收敛；由 (46.17) 可知 (46.7) 在 $\operatorname{Re}s>b$ 绝对收敛。在 $\operatorname{Re}s>1$ 分部积分，因 $S_j(1)=0$、$S_j(x)=O(x)$，两端边界项均已确定，得到

$$
\begin{aligned}
M_j(s)&=s\int_1^\infty S_j(x)x^{-s-1}\,dx
       =\frac{s}{s-1}+sG_j(s)\\
&=\frac1{s-1}+sF_0(s)+H_j(s),\qquad
H_j(s)=1+s(G_j-F_0)(s).
\end{aligned}
\tag{46.32}
$$

$H_j$ 整；其中常数 $1$ 来自 $s/(s-1)=1+1/(s-1)$，不能因主项写作 $x$ 就漏掉。故 (46.10) 列出了全部完整主部；$\rho_{n,\pm}\ne0$，其留数全部非零。普通误差变换 $G_j$ 的留数是 $a_n/2$，Stieltjes 变换的留数是 $\rho_{n,\pm}a_n/2$，两种约定不同。

保留的极点还说明：不存在任何固定 $d<b$ 使 $g_j(y)=O(e^{dy})$。否则其 Laplace 积分在 $\operatorname{Re}s>d$ 全纯，却必须与具有某个 $\beta_n>d$ 极点的上述延拓相同，矛盾。因此也不存在以某个更小的 $d<b$ 为中心的全部 $O_\varepsilon(e^{(d+\varepsilon)y})$ 上界族。这一结论与 (46.6) 相容，不要求边界 $b$ 由某个极点取得。$\square$

来源与新增范围。上述共同构造只把经典高斯 Fourier 积分、Cauchy 轮廓变形及正常收敛作为中间工具，不另主张它们或一般 Tauberian 定理的新证明。Broucke–Debruyne–Vindas，*On the absence of remainders in the Wiener–Ikehara and Ingham–Karamata theorems: a constructive approach*，*Proc. Amer. Math. Soc.* **149** (2021), 1053–1060，[arXiv:2001.01635v2](https://arxiv.org/abs/2001.01635v2)，Theorem 1、Lemma 3 及 Example 1，提供高频相位整延拓与正主项保持单调的成熟背景；其固定振幅余弦结论不直接承担 (46.21) 的可变核、双向模态求和或外弧估计。Callewaert–Neyt–Vindas，*On a space of functions with entire Laplace transforms and its connection with the optimality of the Ingham–Karamata theorem*，*Complex Analysis and Operator Theory* **19** (2025), Article 85，[arXiv:2407.15547v2](https://arxiv.org/abs/2407.15547v2)，Theorem 1.2、Corollary 1.3 及 Theorem 2.1，给出整 Laplace 空间的余项最优性和稠密逼近；紧矩形上的近似本身不给指定参考的精确模整函数保留及全尾符号时长。这里的成果定位为本卷推导的受限综合（repo-derived）：把明确的未取得非实参考谱、可变窄正核、完整主部、全域单调斜率和有限／余有限负占用同时实现；不将成熟输入重新列为独立成果，不主张全球文献优先性。

**注记 46.3（观察纤维与实际 θ／CM 的未决桥）。** 定理 46.2 说明：在这个人工参考的模整函数类中，全部非实主部、实轴正则、未取得谱上确界、任意 $\varepsilon$ 的增长上界和连续非负计数仍不能决定负对数占用。它保留的是变换模整函数的等价类；整修正可以改变正则部分的值及延拓域的定量增长，没有断言两个完整 Laplace 函数、完整局部芽或 Euler–Dirichlet 恒等式相同。

实际普通素数的测度固定为

$$
d\vartheta(x)=\sum_{p\ \mathrm{prime}}(\log p)\,\delta_p,
\qquad
d[\vartheta(e^y)]=\sum_{p\ \mathrm{prime}}(\log p)\,\delta_{\log p}.
\tag{46.33}
$$

这里的两个 $dS_j$ 则相对于 $dx$ 绝对连续，既没有这些固定原子，也没有整数胞内的真实阶梯结构。参考误差留数 $a_n/2$ 与真实显式公式零点项的残差 $-m_\rho/\rho$ 不同，参考位置 $\rho_{n,\pm}$ 也不是被指定的实际 ζ 零点；$m_\rho$ 在此指实际零点重数，与窄核参数 $m$ 无关。因此本定理没有给任意实际芽造出同主部实现。

就本条轮廓路线而言，回接一个给定实际芽还缺解析代表的桥：需在该芽模整函数的类中找到代表 $h$，证明其右侧固定扇区增长能被所用相位衰减压住，并在实轴上支付保持计数单调的导数成本。对 $f_0$，这分别由 $e^{-n^4}$ 的系数给出 (46.12)，再由 $b<1$ 给出 (46.17) 的 $o(e^y)$。实际 $\vartheta(e^y)-e^y$ 有跳跃，不能直接作为这些轮廓上的全纯函数；实际零点级数的代数级系数也没有给出本条的扇区正常收敛。这里只指出尚缺的输入，不推出其他解析化方法不存在。

此外，§43 的实际未取得分支允许 $b=1$；本条的单调性证明使用固定的 $b<1$，没有支付该端点。连续参考的对数占用也不能替代 §44 所需的同一个实际 $\vartheta(H)<H$ 整数谐和。§41 的实际 CM 点、全部原有限地方、原 $q_H$、同一 $Y=C_M\times\mathbb T^2$ 上的跨块联合条件和同一个成功整数均保持原义；本条补接参数 $Y_0$ 只是一个实对数阈值，不是该 CM 空间。实际 θ 的占用发散、给定实际芽的共同实现及原 CM 满测桥仍未解决。

用白话说，极点和它们的全部主部记录了变换中不能由整函数消掉的谱成分，却没有记录误差在正负两侧分别停留多久。这里先固定那套人工谱，再用越来越窄、越来越高的正脉冲把误差集中到总长度有限的槽里；槽外残留小到能被 $e^{-y^2}$ 这一层底色压过，给底色取正号或负号便得到有限或余有限的负占用。分别转动正负模态证明这种集中对参考变换只增加整函数，所以原极点逐个留下；脉冲高度和斜率只付多项式成本，仍小于 $x$ 主项的斜率预算，有限补接也付了同样的斜率界，故两个计数始终单调。真实素数没有被搬动：其固定的 $\log p$ 原子和实际残差并不是这些连续参考函数的对象，实际 θ 与 CM 所缺的同一对象、同一整数联合桥仍需另行证明。

## 追加锚（本行以下为增补区）

## 47. 固定人工谱的整数 log n 原子、单值 Euler 双实现与相反谐和占用

**定义 47.1（一次固定的谱、核与参考变换）。** 固定 $1/2<b<1$ 及整数 $m>4$。对 $n=1,2,\ldots$，依次确定

$$
\begin{gathered}
Y_n=2^n,\qquad \theta_n=0,\qquad
\beta_n=b-\frac{b-1/2}{n+1},\qquad L_n=e^{nY_n},\\
j_n=\left\lceil\frac{Y_nL_n}{\pi}\right\rceil+1,\qquad
\gamma_nY_n+\arctan\frac{\beta_n}{\gamma_n}=j_n\pi,\\
\frac{(j_n-1/2)\pi}{Y_n}<\gamma_n<\frac{j_n\pi}{Y_n},\qquad
\rho_n=\beta_n+i\gamma_n,\qquad A_n=\frac{4\gamma_n}{\sqrt{Y_n}}.
\end{gathered}
\tag{47.1}
$$

方程的唯一性及存在性在下面证明。记 $\Gamma=\{\rho_n,\bar\rho_n:n\ge1\}$。对实 $y$ 定义

$$
\begin{aligned}
f_n(y)&=-\frac{e^{\rho_n y}}{\rho_n}
         -\frac{e^{\bar\rho_n y}}{\bar\rho_n},\\
K_n(y)&=\sum_{k\in\mathbb Z}e^{-k^2/y^m}e^{ikA_ny^{3/2}}
                       &&(y>0),\\
f(y)&=\sum_{Y_n\le y}f_n(y),\qquad
h(y)=\sum_{Y_n\le y}f_n(y)K_n(y) &&(y\ge0).
\end{aligned}
\tag{47.2}
$$

激活和为空时取零，故无需定义 $K_n(0)$。$g_n(z)$ 表示 $f_n$ 的全纯延伸，即在第一式中把 $y$ 换成 $z$；共轭只作用于参数 $\rho_n$，不作用于变量 $z$。固定参考为

$$
F(s)=\sum_{n\ge1}\left\{
-\frac{e^{-(s-\rho_n)Y_n}}{\rho_n(s-\rho_n)}
-\frac{e^{-(s-\bar\rho_n)Y_n}}{\bar\rho_n(s-\bar\rho_n)}
\right\}.
\tag{47.3}
$$

这里的谱是人工选定的非实谱，整数支撑也不预指普通素数。

**定理 47.2（同谱、整数原子与 Euler 除子的确定性双实现）。** 对定义 47.1 的每一组固定参数，存在按以下证明唯一指定的两个整数集合 $\mathcal A_+,\mathcal A_-\subseteq\{8,9,\ldots\}$，使每个整数在各集合中至多出现一次。置

$$
\begin{gathered}
\Theta_\eta(x)=\sum_{a\in\mathcal A_\eta,\ a\le x}\log a,
\qquad B_\eta(x)=\Theta_\eta(x)-\lfloor x\rfloor,
\qquad \eta\in\{+,-\},\\
G_\eta(s)=\int_1^\infty(\Theta_\eta(x)-x)x^{-s-1}\,dx,
\qquad
Z_\eta(s)=\prod_{a\in\mathcal A_\eta}(1-a^{-s})^{-1}.
\end{gathered}
\tag{47.4}
$$

这些变换和乘积起初均取 $\operatorname{Re}s>1$。结论如下。

（一）存在非负连续、局部绝对连续的中间计数 $S_\eta$，满足 $S_\eta(1)=0$、全域几乎处处 $1/2\le S_\eta'\le3/2$，且

$$
\begin{gathered}
S_\eta(x)=x+O\!\left(x^b(\log x)^{m/2}\right),\qquad
\Theta_\eta(x)-S_\eta(x)=O(\log x),\\
\sum_{H\ge1:\,\Theta_+(H)<H}\frac1H<\infty,
\qquad
\sum_{H\ge1:\,\Theta_-(H)\ge H}\frac1H<\infty.
\end{gathered}
\tag{47.5}
$$

因此负整数占用对 $+$ 有限谐和质量，对 $-$ 的补集有有限谐和质量；后者称调和意义的余有限，不声称通常意义的有限补集。相应地

$$
\int_{\{x\ge1:B_+(x)<0\}}\frac{dx}{x}<\infty,
\qquad
\int_{\{x\ge1:B_-(x)\ge0\}}\frac{dx}{x}<\infty.
\tag{47.6}
$$

（二）$F$ 是全平面亚纯函数，仅在 $\Gamma$ 有简单极点，主部分别为 $-1/[\rho_n(s-\rho_n)]$ 及其参数共轭式。两个连续普通 Mellin 误差与 $F$ 之差各自整；两个 $G_\eta-F$ 则各自在 $\operatorname{Re}s>0$ 全纯。以 $B_\eta$ 取代普通误差仍只增加该半平面全纯函数。因此这些离散误差的全部主部仍准确为

$$
-\frac1{\rho_n(s-\rho_n)},\qquad
-\frac1{\bar\rho_n(s-\bar\rho_n)}.
\tag{47.7}
$$

其谱实部上确界为未取得的 $b$，误差变换在正实轴正则；这里的正则性不包括 Euler 函数在 $1$ 的极点。

（三）$Z_\eta$ 均有到 $D=\{\operatorname{Re}s>1/2\}$ 的单值亚纯延拓。各自仅在 $1$ 有一个简单极点，仅在 $\Gamma$ 有简单零点，无其他零极点。两者的负对数导数具有同一完整主部：$1$ 处留数 $+1$，$\Gamma$ 各处留数 $-1$。共享的是零极点及其重数和负对数导数的主部，不要求两个 Euler 函数相等、完整芽相等，亦不要求它们在 $1$ 的函数留数相等。

**证明。** 全部参数首先由 (47.1) 固定，以下不按紧集、模态或实变量重新选择它们。

（甲）根、激活接点与局部绝对连续性。令 $Y=Y_n$、$\beta=\beta_n$、$j=j_n$。指定根区间的左端大于 $L_n$；函数
$\gamma Y+\arctan(\beta/\gamma)$ 的导数为 $Y-\beta/(\gamma^2+\beta^2)>0$。其左端值小于 $j\pi$，右端值大于 $j\pi$，故唯一根存在，且 $\gamma_n>L_n$。由根方程

$$
\beta_n\cos(\gamma_nY_n)+\gamma_n\sin(\gamma_nY_n)=0,
\qquad
f_n(y)=-\frac{2e^{\beta_n y}
[\beta_n\cos(\gamma_n y)+\gamma_n\sin(\gamma_n y)]}
{\beta_n^2+\gamma_n^2},
\tag{47.8}
$$

得到 $f_n(Y_n)=0$。$K_n$ 及其任意固定阶导数的级数在 $y>0$ 的实紧区间由高斯尾正常控制。在每个有界实区间内仅有有限项激活，且各项在接点的函数值为零。逐项零延伸后分段光滑、连续且局部绝对连续，故 $f,h$ 亦如此；接点允许导数跳跃，没有函数跳跃或分布 $\delta$ 项。记

$$
\mathcal G=\sum_n\gamma_n^{-1}<\sum_ne^{-n2^n}<\infty,
\qquad
\mathcal J=\sum_nY_n^{-1/2}=\sqrt2+1,
\qquad
N(y)=\#\{n:Y_n\le y\}\le\log_2y.
\tag{47.9}
$$

高斯和估计给出，对 $y\ge2$，

$$
|f(y)|\le2\mathcal G e^{by},\qquad
|h(y)|\le C_m\mathcal G e^{by}y^{m/2}.
\tag{47.10}
$$

当 $\operatorname{Re}s>b$ 时，可绝对交换激活和与 Laplace 积分，直接积分得到 $\mathcal Lf=F$。在 $|s|\le R$ 上，充分大的 $n$ 满足 $|s-\rho_n|,|s-\bar\rho_n|\ge\gamma_n/2$，相应一对项至多

$$
\frac{4e^{(b+R)Y_n}}{\gamma_n^2}.
\tag{47.11}
$$

故在避开极点的紧集上正常收敛。$\beta_n$ 严格递增、$\gamma_n\to\infty$，所以 $\Gamma$ 无有限聚点且各点互异。展开激活因子得到

$$
-\frac{e^{-(s-\rho_n)Y_n}}{\rho_n(s-\rho_n)}
=-\frac1{\rho_n(s-\rho_n)}+\text{在 }\rho_n\text{ 附近全纯的函数}.
\tag{47.12}
$$

其余项在该点附近正常收敛且全纯；这证明 (47.3) 的全部准确主部。

（乙）逐谱正负模态及内弧角积分。先在 $\operatorname{Re}s>b$ 定义

$$
E_n(s)=\int_{Y_n}^\infty f_n(y)(K_n(y)-1)e^{-sy}\,dy.
\tag{47.13}
$$

固定 $n$，暂记 $Y=Y_n$、$\gamma=\gamma_n$、$A=A_n$、$g=g_n$。令

$$
\alpha=\frac{\pi}{4m},\quad a=\cos(m\alpha)=\frac1{\sqrt2},\quad
q=\frac{\sin\alpha}{\alpha},\quad d=\sin\alpha.
$$

对 $k\ne0$ 写 $j=|k|$、$\epsilon=\operatorname{sign}k$。只在扇区 $0\le\epsilon\arg z\le\alpha$、$|z|\ge Y$ 中使用主支 $z^{3/2}$，并置

$$
Q_k(z,s)=g(z)e^{-sz-k^2z^{-m}+ikAz^{3/2}}.
$$

正模态向上转，负模态向下转。若 $z=re^{i\epsilon u}$、$0\le u\le\alpha$、$|s|\le R$，置 $D_R=b+R$，则

$$
\begin{aligned}
|Q_k(z,s)|
&\le\frac2\gamma e^{D_Rr-a j^2/r^m}
 \exp\{\gamma r\sin u-jAr^{3/2}\sin(3u/2)\}\\
&\le\frac2\gamma e^{D_Rr-a j^2/r^m}
 \exp\{-(4j\sqrt{r/Y}-1)\gamma r\sin u\}.
\end{aligned}
\tag{47.14}
$$

这里 $\sin(3u/2)\ge\sin u\ge qu$，两种转向所得估计相同。$g$ 中两个指数的最坏增长 $e^{\gamma r\sin u}$ 始终与衰减相位一起估计。

令 $I_k$ 为从 $Y$ 到 $Ye^{i\epsilon\alpha}$ 的有向内弧积分。保留角积分，得到

$$
\begin{aligned}
\sup_{|s|\le R}|I_k(s)|
&\le\frac{2Y}{\gamma}e^{D_RY-a j^2/Y^m}
 \int_0^\alpha e^{-3j\gamma Yqu}\,du\\
&\le\frac{2}{3qj\gamma^2}e^{D_RY-a j^2/Y^m}.
\end{aligned}
\tag{47.15}
$$

将和在 $j=Y^{m/2}$ 附近分开，前段用调和和、后段用单调高斯积分，给出

$$
S_m(Y):=\sum_{j\ge1}\frac{e^{-a j^2/Y^m}}j
\le C_m(1+\log Y),\qquad
\sum_{k\ne0}\sup_{|s|\le R}|I_k(s)|
\le\frac{C_m e^{D_RY}(1+\log Y)}{\gamma^2}.
\tag{47.16}
$$

角积分带来的 $1/(j\gamma Y)$ 因子是全谱可和估计的一部分，不能先对 $g$ 单独取内弧最大值。

（丙）射线的全紧集界。令 $R_k$ 为从 $Ye^{i\epsilon\alpha}$ 沿同一射线到无穷的积分。写 $t=r/Y\ge1$，则

$$
4j\sqrt t-1\ge2j\sqrt t+j,\qquad
\sup_{t\ge0}(D_Rt-2dt^{3/2})=\frac{D_R^3}{27d^2}=:B_R.
$$

由于 $j\gamma\ge1$，(47.14) 的射线指数至多 $B_RY-j\gamma dr$。因此

$$
\begin{aligned}
\sup_{|s|\le R}|R_k(s)|
&\le\frac{2e^{B_RY}}\gamma\int_Y^\infty e^{-j\gamma dr}\,dr
 =\frac{2e^{B_RY-j\gamma dY}}{dj\gamma^2},\\
\sum_{k\ne0}\sup_{|s|\le R}|R_k(s)|
&\le\frac{4[-\log(1-e^{-2d})]}{d\gamma^2}e^{B_RY}.
\end{aligned}
\tag{47.17}
$$

被舍去的高斯因子不超过 $1$。各射线积分在 $s$ 紧集上有统一可积尾界，故为整函数；内弧积分亦整，两者的模态和正常收敛。这些界对每个 $n$ 有效，没有令 $\gamma_n$ 依赖 $R$。

（丁）全部模态的外弧回接。写 $s=\sigma+i\tau$、$\delta=\sigma-b>0$。在半径 $T$ 的外弧上，当 $A\sqrt T\ge2(\gamma+|\tau|)$ 时，结合两指数的增长与模态相位至少留下

$$
|Q_k(Te^{i\epsilon u},s)|
\le\frac2\gamma
 e^{-\delta T\cos\alpha-a j^2/T^m}
 e^{-(j/2)AT^{3/2}\sin u}.
$$

乘弧长并积分角变量，外弧积分 $O_{k,T}$ 满足

$$
|O_{k,T}(s)|\le
\frac4{qj\gamma A\sqrt T}
 e^{-\delta T\cos\alpha-a j^2/T^m},\qquad
\sum_{k\ne0}|O_{k,T}(s)|\le
\frac{8S_m(T)}{q\gamma A\sqrt T}e^{-\delta T\cos\alpha}\longrightarrow0.
\tag{47.18}
$$

在初始半平面的紧集上也一致趋零。因此不是仅对每个固定模态回接。有限环扇形的边界取实轴向外、外弧、射线向内、内弧向内，Cauchy 定理给出

$$
\int_Y^\infty Q_k(y,s)\,dy=I_k(s)+R_k(s).
\tag{47.19}
$$

下扇区虽有相反几何定向，零积分及上述等式仍相同。原实轴上也可绝对交换 $n,k$ 与积分，因为

$$
\sum_n\int_{Y_n}^\infty |f_n(y)|e^{-\sigma y}
 \sum_k e^{-k^2/y^m}\,dy
\le C_m\mathcal G\int_2^\infty e^{-(\sigma-b)y}y^{m/2}\,dy<\infty.
\tag{47.20}
$$

所以 $E_n=\sum_{k\ne0}(I_k+R_k)$ 确实延拓 (47.13)。综合 (47.16)、(47.17)，取 $C_R=1+D_R+B_R$，有

$$
\sup_{|s|\le R}|E_n(s)|
\le\frac{C_m e^{C_RY_n}(1+\log Y_n)}{\gamma_n^2}.
\tag{47.21}
$$

常数 $C_m$ 仅依赖 $m$；$b,R$ 的依赖已纳入 $C_R$。由 $\gamma_n>e^{nY_n}$，充分大的 $n$ 的右端受常数倍 $e^{-nY_n/2}$ 控制，故

$$
E(s):=\sum_nE_n(s)\quad\text{整},\qquad
\mathcal Lh(s)=F(s)+E(s)\quad(\operatorname{Re}s>b).
\tag{47.22}
$$

这里的 $n$ 和在每个复紧集绝对一致；稍大圆盘上的 Cauchy 导数估计还允许任意固定阶 $s$ 导数逐项相加。全部非零模态的总修正是整函数，(47.12) 的每一个简单主部原样保留。

（戊）一次固定构造的导数成本。在实轴上
$f_n'(y)=-2e^{\beta_n y}\cos(\gamma_n y)$。由 (46.15) 的高斯矩界，直接微分 $K_n$ 给出

$$
|K_n'(y)|\le C_m\left[y^{m/2-1}+A_n y^{m+1/2}\right]\quad(y\ge2).
$$

使用 $\sum_n A_n/\gamma_n=4\mathcal J$，在几乎所有非接点及相应单侧导数上得到

$$
\begin{aligned}
|h'(y)|
&\le C_m e^{by}\left[y^{m/2}N(y)
 +\mathcal G y^{m/2-1}+4\mathcal J y^{m+1/2}\right]\\
&\le C_m e^{by}\left[y^{m/2}\log(2+y)+y^{m+1/2}\right]
=o(e^y).
\end{aligned}
\tag{47.23}
$$

接点不要求经典导数存在；（甲）的局部绝对连续性保证几乎处处估计可积分。因 $b<1$，(47.10) 同样给出 $h=o(e^y)$。

（己）确定槽的总长度与槽外底色。置

$$
U_n=\{y\ge Y_n:\operatorname{dist}(A_ny^{3/2},2\pi\mathbb Z)
             <4y^{1-m/2}\},\qquad U=\bigcup_{n\ge1}U_n.
\tag{47.24}
$$

$m\ge5$、$y\ge2$ 保证阈值 $4y^{1-m/2}\le\sqrt2<\pi$。在每个二进区间 $[L,2L]$、$L\ge Y_n$ 中，相位导数为 $(3/2)A_n\sqrt y\asymp A_n\sqrt L$。可能相交的中心数至多 $C(A_nL^{3/2}+1)$；每个槽包含在 $|A_ny^{3/2}-2\pi\ell|<4L^{1-m/2}$ 的原像内，其长度至多 $CA_n^{-1}L^{(1-m)/2}$。即使中心在区间边界外，该计数仍包括与区间相交的槽。因此

$$
\begin{aligned}
|U_n\cap[L,2L]|&\le C_m\left[L^{2-m/2}
                         +A_n^{-1}L^{(1-m)/2}\right],\\
|U_n|&\le C_m\left[Y_n^{2-m/2}
                         +A_n^{-1}Y_n^{(1-m)/2}\right],\qquad
|U|\le\sum_n|U_n|<\infty.
\end{aligned}
\tag{47.25}
$$

第二行沿 $L=2^jY_n$ 求几何和；第一项对 $n$ 可和正是因为 $m>4$，第二项使用 $A_n^{-1}=\sqrt{Y_n}/(4\gamma_n)$ 亦可和。

Poisson 恒等式给出确定的正核

$$
K_n(y)=\sqrt\pi\,y^{m/2}\sum_{\ell\in\mathbb Z}
 \exp\!\left[-\frac{y^m(A_ny^{3/2}-2\pi\ell)^2}{4}\right]>0.
\tag{47.26}
$$

直接复用 (46.18) 的周期一致估计，若 $y\ge Y_n$ 且 $y\notin U_n$，则 $K_n(y)\le Cy^{m/2}e^{-2y^2}$。故所有激活项在 $U$ 外同时满足

$$
|h(y)|\le C_m\mathcal G e^{by}y^{m/2}e^{-2y^2}
=o(e^{-y^2}).
\tag{47.27}
$$

令 $w(y)=e^{-y^2}$、$u_\pm(y)=h(y)\pm w(y)$。由 (47.23)、(47.27)，$u_\pm,u_\pm'=o(e^y)$，且最终在 $U$ 外 $u_+\ge w/2>0$、$u_-\le-w/2<0$。核没有被当作紧支撑核，槽内也没有预设符号或质量。

（庚）线性补接及全局计数斜率。取满足以下全部条件的最小整数 $y_0\ge2$：对 $y\ge y_0$，两种符号都有 $|u_\eta(y)|\le e^y/4$、几乎处处 $|u_\eta'(y)|\le e^y/2$，且 $U$ 外 $|h(y)|\le w(y)/2$。前述极限保证该整数存在。令 $X=e^{y_0}$，定义

$$
q_\eta=\frac{X+u_\eta(y_0)}{X-1},\qquad
S_\eta(x)=
\begin{cases}
q_\eta(x-1),&1\le x\le X,\\
x+u_\eta(\log x),&x\ge X.
\end{cases}
\tag{47.28}
$$

$X\ge e^2>6$，所以

$$
q_\eta>0,\qquad
|q_\eta-1|\le\frac{1+X/4}{X-1}\le\frac12.
$$

两段的函数值在 $X$ 相同，且在每个紧区间拼成绝对连续函数。前段斜率为 $q_\eta$，后段几乎处处斜率为 $1+x^{-1}u_\eta'(\log x)$，均在 $[1/2,3/2]$ 内。这证明全域斜率、$S_\eta(1)=0$、非负性及 (47.5) 的连续增长式。还得到

$$
\begin{gathered}
E_+=\{x\ge1:S_+(x)<x\},\qquad
E_-=\{x\ge1:S_-(x)\ge x\},\\
L_\pm:=\int_{E_\pm}\frac{dx}{x}\le y_0+|U|<\infty.
\end{gathered}
\tag{47.29}
$$

这是 $dx/x=dy$ 及尾部严格符号的直接结果。

令 $v_\eta(y)=S_\eta(e^y)-e^y$。$v_\eta-u_\eta$ 支撑于 $[0,y_0]$，故

$$
\begin{gathered}
W(s)=\int_0^\infty e^{-y^2-sy}\,dy,\qquad
C_\eta(s)=\int_0^{y_0}(v_\eta(y)-u_\eta(y))e^{-sy}\,dy,\\
F_{S_\pm}(s):=\int_1^\infty(S_\pm(x)-x)x^{-s-1}\,dx
=F(s)+E(s)\pm W(s)+C_\pm(s).
\end{gathered}
\tag{47.30}
$$

等式起初在 $\operatorname{Re}s>b$ 成立。$W$ 在每个 $s$ 紧集由高斯尾支配，$C_\eta$ 是固定有限段积分，二者均整。因此两个连续误差分别与同一个 $F$ 相差整函数，不是仅证明两误差之差整。

（辛）固定 $\pm1$ 缓冲的确定贪心及有限追赶。取固定整数 $N=8$，令

$$
U(n)=S_+(n)+1,\qquad V(n)=S_-(n)-1,\qquad
Q_+(N-1)=Q_-(N-1)=0.
$$

由全域斜率，$S_-(7)\ge3$，且 $\log N>3/2$。对每个整数 $n\ge N$，按下式一次决定是否将它收入相应集合：

$$
\begin{aligned}
Q_+(n)&=Q_+(n-1)+(\log n)\,\mathbf1_{\{Q_+(n-1)<U(n)\}},\\
Q_-(n)&=Q_-(n-1)+(\log n)\,\mathbf1_{\{Q_-(n-1)+\log n\le V(n)\}}.
\end{aligned}
\tag{47.31}
$$

触发的整数分别组成 $\mathcal A_\pm$，所以 $Q_\eta(n)=\Theta_\eta(n)$，每整数只有一个 $\log n$ 跳跃机会。未引入随机相位、重复原子或预先给定的种子集合。置

$$
\begin{gathered}
c=\log N-\frac32>0,\quad u_0=U(N-1)>0,\quad v_0=V(N-1)\ge0,\\
C_0=\max(u_0,v_0),\qquad K=N+\lceil C_0/c\rceil.
\end{gathered}
\tag{47.32}
$$

局部绝对连续性及斜率给 $\Delta U(n),\Delta V(n)\in[1/2,3/2]$。对 up 递推设 $d_n=Q_+(n)-U(n)$，初值 $d_{N-1}=-u_0$。首次到达非负值前每步都触发，若尚未追上，则

$$
d_n=-u_0+\sum_{k=N}^n(\log k-\Delta U(k))
\ge-u_0+(n-N+1)c.
$$

$(K-N+1)c>C_0$ 保证至迟在 $K$ 追上。首次追上时由触发条件有 $0\le d_n<\log n$。此带随后不变：不触发时 $d_n\ge0$ 且 $d_n=d_{n-1}-\Delta U(n)<\log n$；触发时下界为 $\log n-3/2>0$，触发条件又给上界 $d_n<\log n$。

对 down 递推设 $e_n=V(n)-Q_-(n)$，初值 $e_{N-1}=v_0\ge0$，仅在整跳可容纳时加入，故始终 $e_n\ge0$。任何不触发的一步立即满足 $e_n<\log n$；若至 $K$ 仍未入带，则每步均触发，导致

$$
e_K=v_0+\sum_{k=N}^K(\Delta V(k)-\log k)
\le v_0-(K-N+1)c<0,
$$

矛盾。入带后，不触发仍由条件得 $e_n<\log n$；触发则
$0\le e_n<\log(n-1)+3/2-\log n\le3/2<\log n$。因此对所有 $n\ge K$，

$$
U(n)\le Q_+(n)<U(n)+\log n,\qquad
V(n)-\log n<Q_-(n)\le V(n).
\tag{47.33}
$$

追赶及不变带完全由递推支付，没有使用待证的占用结论。对实数 $x\in[n,n+1)$、$n\ge K$，$\Theta_\eta(x)=Q_\eta(n)$，而
$0\le S_\eta(x)-S_\eta(n)\le(3/2)(x-n)$，故

$$
|\Theta_\eta(x)-S_\eta(x)|\le\log x+\frac52.
\tag{47.34}
$$

（壬）整胞厚化、谐和计费与 floor 基准。$g_\eta(x)=S_\eta(x)-x$ 为 $1/2$-Lipschitz。若 $n\ge K$ 且 $Q_+(n)<n$，由 (47.33) 得 $g_+(n)<-1$，从而对整胞 $[n,n+1)$ 有 $g_+(x)<-1/2$，整胞属于 $E_+$。若 $Q_-(n)\ge n$，则 $g_-(n)\ge1$，整胞上 $g_-(x)>1/2$，属于 $E_-$。令

$$
I_+=\{n\ge K:Q_+(n)<n\},\qquad
I_-=\{n\ge K:Q_-(n)\ge n\}.
$$

同号的整胞互不相交，于是

$$
\sum_{n\in I_\pm}\log(1+1/n)
=\int_{\bigcup_{n\in I_\pm}[n,n+1)}\frac{dx}{x}\le L_\pm,
\qquad
\sum_{n\in I_\pm}\frac1n\le2L_\pm,
\tag{47.35}
$$

其中 $\log(1+1/n)\ge1/(n+1)\ge1/(2n)$。加回有限初段得到 (47.5)。特别地 $-$ 的负整数集合的调和和发散，因为其补集的调和和有限。

在每个整数胞 $[n,n+1)$ 上，$B_\eta(x)=Q_\eta(n)-n$ 恰为常数，故错误符号集就是上述整数集的整胞并；(47.35) 同时证明 (47.6)。相对于实基准则

$$
\Theta_\eta(x)-x=B_\eta(x)-(x-\lfloor x\rfloor).
\tag{47.36}
$$

二者不能冒称同号，例如 $0\le B_\eta(x)<1$ 时小数部分能改变符号。固定缓冲所做的是把错误整数提升为连续错误集内的整个胞，不是对有限测度集合作裸整数采样。

（癸）Mellin 舍入与完整主部转移。记 $R_\eta=\Theta_\eta-S_\eta$，由 (47.34) 及有限初段有 $R_\eta=O(1+\log x)$。因此

$$
H_\eta(s)=\int_1^\infty R_\eta(x)x^{-s-1}\,dx
\quad\text{在 }\operatorname{Re}s>0\text{ 全纯},\qquad
G_\eta=F_{S_\eta}+H_\eta.
\tag{47.37}
$$

对任一紧集 $\operatorname{Re}s\ge\varepsilon>0$，每个固定阶导数的被积函数由
$C(1+\log x)^{r+1}x^{-1-\varepsilon}$ 支配，故上述全纯性和逐阶求导严格成立。由 (47.30)，$G_\eta-F$ 在这个半平面全纯。若改用 $B_\eta$ 的普通 Mellin 变换，还要加

$$
J(s)=\int_1^\infty(x-\lfloor x\rfloor)x^{-s-1}\,dx,
\tag{47.38}
$$

它同样只需在 $\operatorname{Re}s>0$ 全纯。舍入修正与 floor 修正没有被称为全平面整函数；例如常数尾的 Mellin 变换含 $X^{-s}/s$，仅凭这种界不能排除非正半平面的奇性。

所有 $\rho_n$ 均在 $\operatorname{Re}s>0$，故 (47.7) 原样保留，且 $G_\eta$ 及加上 $J$ 的变换在正实轴无极点。$\beta_n\uparrow b$ 而无一项等于 $b$。增长式还给出任意 $\varepsilon>0$ 的 $\Theta_\eta(x)-x=O_\varepsilon(x^{b+\varepsilon})$；不存在任何固定 $d<b$ 使其为 $O(x^d)$。否则原积分在 $\operatorname{Re}s>d$ 全纯，与某个 $\beta_n>d$ 的非零主部矛盾。这里没有把未取得上确界改成一个实轴奇点。

（子）Stieltjes 输入、Euler 高次尾及常数下端项。在 $\operatorname{Re}s>1$，$\Theta_\eta(1)=0$、$\Theta_\eta(x)=O(x)$ 保证分部积分两端均已确定，得到

$$
D_\eta(s):=\sum_{a\in\mathcal A_\eta}(\log a)a^{-s}
=\int_1^\infty x^{-s}\,d\Theta_\eta(x)
=\frac{s}{s-1}+sG_\eta(s).
\tag{47.39}
$$

连续 $S_\eta(1)=0$ 也给相同下端约定；两 Stieltjes 输入之差为 $sH_\eta$。在 $\rho_n$ 的完整普通主部恰是简单主部 $-1/[\rho_n(s-\rho_n)]$，乘 $s$ 后的完整奇部为 $-1/(s-\rho_n)$。此处简单性已证，未把只知留数的高阶极点误用为同一规则。

Euler 乘积在 $\operatorname{Re}s>1$ 由绝对正常收敛的
$\sum_{a\in\mathcal A_\eta}\sum_{k\ge1}a^{-ks}/k$ 定义，是非零全纯函数。逐项求导给

$$
-\frac{Z_\eta'}{Z_\eta}=D_\eta+T_\eta,
\qquad
T_\eta(s)=\sum_{a\in\mathcal A_\eta}\sum_{k\ge2}(\log a)a^{-ks}.
\tag{47.40}
$$

在 $\operatorname{Re}s\ge1/2+\varepsilon$ 上，绝对和至多

$$
\frac1{1-N^{-1/2-\varepsilon}}
\sum_{a\ge N}(\log a)a^{-1-2\varepsilon}<\infty.
\tag{47.41}
$$

因此 $T_\eta$ 在 $D$ 全纯，不改变人工谱的任何主部。设 $\mathcal H_\eta=G_\eta-F$，定义其延拓

$$
\begin{aligned}
\mathcal L_\eta(s)
&=\frac{s}{s-1}+sF(s)+s\mathcal H_\eta(s)+T_\eta(s)\\
&=\frac1{s-1}+sF(s)
  +\bigl[1+s\mathcal H_\eta(s)+T_\eta(s)\bigr].
\end{aligned}
\tag{47.42}
$$

括号在 $D$ 全纯；其中常数 $1$ 来自 $s/(s-1)$，不能漏掉。$F$ 在 $1$ 正则，故 $\mathcal L_\eta$ 仅在 $1$ 留数 $+1$、在 $\rho_n,\bar\rho_n$ 留数 $-1$，且全为简单极点。

（丑）整数留数所保证的严格单值延拓。令 $D^*=D\setminus(\{1\}\cup\Gamma)$。该域道路连通。取基点 $s_*=2$，以原 Euler 乘积的非零值 $Z_\eta(2)$ 归一化，定义

$$
\widetilde Z_\eta(s)=Z_\eta(2)
 \exp\!\left(-\int_{2}^{s}\mathcal L_\eta(w)\,dw\right),\qquad s\in D^*.
\tag{47.43}
$$

任意闭合分段光滑路 $\gamma\subset D^*$ 的凸包紧含于半平面 $D$；离散极点在其中只有有限个。留数定理及绕数给

$$
\frac1{2\pi i}\int_\gamma\mathcal L_\eta(w)\,dw
=\operatorname{Ind}(\gamma,1)
 -\sum_{a\in\Gamma}\operatorname{Ind}(\gamma,a)\in\mathbb Z.
\tag{47.44}
$$

式中仅有限项非零。故 (47.43) 的指数与道路无关，定义单值非零全纯函数。它在 $\operatorname{Re}s>1$ 与原乘积具有相同负对数导数及相同基点值，因而相等。

在每个被删点 $a$ 的小圆盘内写
$\mathcal L_\eta(s)=r_a/(s-a)+\ell_a(s)$，其中 $\ell_a$ 全纯，$r_1=1$、$r_a=-1$ 对 $a\in\Gamma$。取 $\ell_a$ 的局部原函数 $P_a$，则穿孔圆盘上

$$
\widetilde Z_\eta(s)=c_a(s-a)^{-r_a}e^{-P_a(s)},\qquad c_a\ne0.
\tag{47.45}
$$

整数 $r_a$ 使该式单值，并在中心给出相应简单极点或简单零点。所有别处由指数表示保证非零全纯，故无额外零极点。这证明（三）。两套 $\mathcal L$ 的主部相消，$Z_+/Z_-$ 还可消去共同零极点而成为 $D$ 上处处非零的全纯函数；这不要求该比值恒为 $1$。特别地，(47.45) 的非零局部因子未被共同除子固定，不能进一步断言两个 $Z$ 在 $1$ 的函数主部系数相同。$\square$

**注记 47.3（成熟输入、综合范围与未付算术桥）。** (47.26) 使用经典 theta／Poisson 恒等式，可从 NIST DLMF [20.2.E3](https://dlmf.nist.gov/20.2.E3) 的 Fourier 展开及 [20.7.E32](https://dlmf.nist.gov/20.7.E32) 的模变换取得；参数对应为 $z=A_ny^{3/2}/2$、$\tau=i/(\pi y^m)$，所以 $q=e^{-1/y^m}$。高斯矩估计、Cauchy 轮廓变形、正常收敛、带缓冲的贪心追踪及整数留数的指数积分是共同构造中的成熟工具，不另列为独立新定理。

§46 所引 Broucke–Debruyne–Vindas，*On the absence of remainders in the Wiener–Ikehara and Ingham–Karamata theorems: a constructive approach*（2021），及 Callewaert–Neyt–Vindas，*On a space of functions with entire Laplace transforms and its connection with the optimality of the Ingham–Karamata theorem*（2025），提供整 Laplace 变换及单调余项的背景。它们不直接给出本条逐谱的 $\gamma_n^{-2}(1+\log Y_n)$ 估计、整数 $\log n$ 原子、缓冲整胞桥或跨全部人工零点的单值 Euler 实现；这些在 (47.14)–(47.45) 中承担各自推导。

Broucke–Vindas，*A new generalized prime random approximation procedure and some of its applications*，[arXiv:2102.08478v2](https://arxiv.org/abs/2102.08478v2)，Theorem 1.2 的输入计数须非减、右连续、趋于无穷，在 $1$ 为零并满足 Chebyshev 上界 $O(x/\log x)$；结论允许选择自由实支撑，连续输入时还可选严格递增序列，但不指定整数支撑。Corollary 2.2 对指定支撑 $v_k$ 除了间距界，还要求尾和条件

$$
\sum_{v_k\ge h(t)}\frac{(v_k-v_{k-1})^2}{v_k\log v_k}
\ll\frac{\log(t+1)}t,
\qquad h(t)=\log(t+1)\log\log(t+e),\quad t>0.
\tag{47.46}
$$

对整数格，该左端包含发散的 $\sum_{k\ge k_0}1/(k\log k)$，故不能套用。该推论的脚注还明确允许支撑点重复，并不保证每点至多一次。本条只用 (47.31)–(47.35) 支付所需确定整数化，没有从自由支撑或该推论借取未满足的条件。

Hilberdink–Lapidus，*Beurling zeta functions, generalised primes, and fractal membranes*，[arXiv:math/0410270v1](https://arxiv.org/abs/math/0410270v1)，§1.1 的广义整数按生成元的分解重数计数；其 Theorem 2.1 在 $0\le\alpha<1$ 及 $\psi(x)=x+O_\varepsilon(x^{\alpha+\varepsilon})$ 下给 $\operatorname{Re}s>\alpha$ 的零自由延拓，$1$ 处为简单极点，逆向还要求负对数导数的增长控制。这不直接支付跨本条人工 $\rho_n$ 的延拓，后者由 (47.42)–(47.45) 单独建立。

这里的普通整数 Euler 乘积可以在 $\operatorname{Re}s>1$ 展开为

$$
Z_\eta(s)=\sum_{r\ge1}c_\eta(r)r^{-s},\qquad
c_\eta(r)=\#\left\{(\nu_a)_{a\in\mathcal A_\eta}:
 \nu_a\in\mathbb Z_{\ge0},\ (\nu_a)\text{ 有限支撑},
 \prod_a a^{\nu_a}=r\right\}.
\tag{47.47}
$$

对固定 $r$ 只有有限个分解，但 $c_\eta(r)$ 不保证为 $0$ 或 $1$；不同所选整数之间可有乘法关系，且只选一次生成元不意味着唯一因式分解。故这些集合是整数生成元集合，可以按上述重数约定解释，不能称为普通素数集合，$Z_\eta$ 也不是实际 Riemann $\zeta$。

本条成果定位为 repo-derived 的受限综合，不主张全球文献原创：对同一固定人工谱，同时保留每个简单普通误差主部 $-1/[\rho(s-\rho)]$、整数单次 $\log n$ 原子、单值 Euler 零极点除子，并实现相反的负整数谐和占用。形式 $-1/\rho$ 与简单零点显式公式的形式一致，不把人工 $\rho$ 识别为实际零点。保留主部与除子允许正则部分改变，未保留任意给定实际完整芽、实际 $\zeta$、功能方程或 Riemann–von Mangoldt 计数。

关键未付算术桥是把这些可自由选择的整数生成元及其分解重数，接回实际普通素数的指定原子、唯一因式分解和同一个实际 $\vartheta$；还缺给定实际谱及完整芽的共同实现。单调导数预算用了固定 $b<1$，没有支付 $b=1$。§41 的实际 CM 点、全部原有限地方、原 $q_H$、同一 $Y=C_M\times\mathbb T^2$ 上跨块联合条件与同一成功整数仍保持原义；本条没有建立实际 $\vartheta(H)<H$ 的谐和占用发散或原 CM 满测桥。整数原子与单值 Euler 结构缩小了人工反例的自由度，没有完成这些实际目标。

用白话说，即使把同一套人工非实谱的全部误差主部固定下来，把跳跃放回整数且每个整数只许跳一次 $\log n$，再要求对应 Euler 乘积在右半平面单值亚纯并具有同一套简单零点和同一个简单极点，仍能让一套误差只在谐和总量有限的整数上为负，另一套则除谐和总量有限的整数外都为负：窄脉冲让谱留在总时长有限的槽中，槽外由正负微小底色决定符号，固定缓冲的追踪又把这种连续符号差异传到完整整数胞，而实际普通素数及 CM 的联合桥仍未建立。

## 追加锚（本行以下为增补区）

## 48. 有限素因子 Hall 类的单位 Abel 容量与真实素数识别

**定义 48.1（有限素因子 Hall 条件、独立性与容量）。** 本节局部记号 $A\subset\{2,3,\ldots\}$ 是整数生成元集，不替换定义 24.1 的同余类集合。记 $\mathcal P$ 为真实素数集，$S(a)=\{p\in\mathcal P:p\mid a\}$。称 $A$ 满足有限素因子 Hall 条件 $H(A)$，若对每个有限 $B\subset A$ 都有

$$
|B|\le\left|\bigcup_{a\in B}S(a)\right|.
\tag{48.1}
$$

记 $\mathbb N_0^{(A)}$ 为有限支撑的非负整数指数族；称 $A$ 乘法独立，若

$$
\iota_A:\mathbb N_0^{(A)}\longrightarrow\mathbb N_{\ge1},\qquad
(e_a)\longmapsto\prod_{a\in A}a^{e_a}
\tag{48.2}
$$

是单射。独立性蕴含 $H(A)$：对 $v(a)=(v_p(a))_{p\in\mathcal P}$，有限独立向量的秩不超过其坐标并集的大小。反向不成立，例如 $A=\{6,36\}$ 满足 $H(A)$（两元的素因子并集为 $\{2,3\}$），却有 $36=6^2$。因此 $H(A)$ 允许重复分解，不能把下式的系数在整个 $H$ 类中写成 $\{0,1\}$。这里的唯一表示只要求在所生成的乘法幺半群内成立，不要求每个正整数都被生成。对 $\operatorname{Re}s>1$ 定义

$$
Z_A(s)=\prod_{a\in A}(1-a^{-s})^{-1},\qquad
\mathcal C(A)=\limsup_{\sigma\downarrow1}(\sigma-1)Z_A(\sigma),\qquad
\Theta_A(x)=\sum_{\substack{a\in A\\a\le x}}\log a.
\tag{48.3}
$$

乘积在该半平面的绝对收敛将在下证中说明；容量沿实数 $\sigma>1$ 取上极限，定义不预设亚纯延拓、简单极点或完整 Abel 极限。

**定理 48.2（Hall 类的单位容量刚性及指定遗漏素数的锐亏损）。** 若 $H(A)$ 成立，则对每个实 $\sigma>1$ 有 $Z_A(\sigma)\le\zeta(\sigma)$。若素数 $q\notin A$，更有

$$
\frac{Z_A(\sigma)}{\zeta(\sigma)}
\le\frac{1-q^{-\sigma}}{1-(2q)^{-\sigma}},\qquad
\mathcal C(A)\le\frac{2(q-1)}{2q-1}<1.
\tag{48.4}
$$

因此在 $H(A)$ 类中，

$$
\mathcal C(A)=1\quad\Longleftrightarrow\quad A=\mathcal P.
\tag{48.5}
$$

乘法独立只是严格更强的充分子类；特别地，乘法独立类中的同一单位容量等价式由此作为推论保留。对每个指定的 $q$，(48.4) 的两个界均最优，并由

$$
A_q=(\mathcal P\setminus\{q\})\cup\{2q\}
\tag{48.6}
$$

取等。

**证明。** （甲）Euler 展开与系数。任意 $A\subset\mathbb N_{\ge2}$ 都有 $\sum_{a\in A}a^{-\sigma}<\infty$，且

$$
\sum_{a\in A}\sum_{k\ge1}\frac{|a^{-ks}|}{k}
\le\frac{1}{1-2^{-\sigma}}\sum_{a\in A}a^{-\sigma}<\infty,
\qquad \sigma=\operatorname{Re}s>1.
\tag{48.7}
$$

在每个闭半平面 $\operatorname{Re}s\ge1+\varepsilon$，右侧可用 $\sigma=1+\varepsilon$ 的可和级数控制。因此对数级数及 Euler 乘积局部一致绝对收敛。有限乘积展开后，以实部 $\sigma$ 的绝对收敛作控制，得到

$$
Z_A(s)=\sum_{n\ge1}c_A(n)n^{-s},\qquad
c_A(n)=\#\{e\in\mathbb N_0^{(A)}:\iota_A(e)=n\}.
\tag{48.8}
$$

每个系数有限，因为出现的生成元必须整除 $n$，指数也有上界；但在一般 $H(A)$ 中系数可以大于一，例如 $c_{\{6,36\}}(36)=2$。下面的有限匹配给出指定遗漏素数的统一亏损，不使用系数的单值性。

（乙）有限 Hall 匹配及因子比较。固定有限 $F\subset A$，在左侧顶点 $a\in F$ 与右侧素因子集合 $S(a)$ 之间连边。$H(A)$ 直接给出每个 $B\subset F$ 的 Hall 不等式，故有限 Hall 定理给出单射 $\phi_F:F\to\mathcal P$，满足 $\phi_F(a)\mid a$。这里每个有限 $F$ 单独匹配，不把有限条件升级成全局无限匹配。置 $Z_F(\sigma)=\prod_{a\in F}(1-a^{-\sigma})^{-1}$。真实素数的 Euler 乘积给出精确恒等式

$$
\frac{Z_F(\sigma)}{\zeta(\sigma)}
=\prod_{a\in F}\frac{1-\phi_F(a)^{-\sigma}}{1-a^{-\sigma}}
 \prod_{p\notin\phi_F(F)}(1-p^{-\sigma}).
\tag{48.9}
$$

补积因 $\sum_p p^{-\sigma}<\infty$ 收敛到正数。由于 $\phi_F(a)\le a$，每个配对因子都在 $(0,1]$ 内，补积的每个因子也如此，故该比值至多为 $1$。

固定 $q\notin A$。若 $q\notin\phi_F(F)$，补积中保留 $1-q^{-\sigma}$，于是比值至多为 $1-q^{-\sigma}$。若 $q=\phi_F(a)$，则 $q\mid a$ 且 $a\ne q$；整数性迫使 $a\ge2q$，该配对因子满足

$$
\frac{1-q^{-\sigma}}{1-a^{-\sigma}}
\le\frac{1-q^{-\sigma}}{1-(2q)^{-\sigma}}.
\tag{48.10}
$$

第一种情形的界也不大于 (48.10) 的右端。因此每个有限 $F$ 都满足同一遗漏 $q$ 的界。

（丙）无限截断与单位容量。取 $F_X=A\cap[2,X]$。对每个固定实 $\sigma>1$，

$$
\begin{aligned}
0\le\log\frac{Z_A(\sigma)}{Z_{F_X}(\sigma)}
&=\sum_{\substack{a\in A\\a>X}}\sum_{k\ge1}\frac{a^{-k\sigma}}{k}\\
&\le\frac{1}{1-2^{-\sigma}}\sum_{n>X}n^{-\sigma}
\longrightarrow0.
\end{aligned}
\tag{48.11}
$$

故 $Z_{F_X}(\sigma)\to Z_A(\sigma)$，有限界传到全体 $A$。各个 $X$ 的匹配可以分别选择，不需要相容，更没有调用全局无限匹配。真实 $\zeta$ 的标准单位留数给出 $\lim_{\sigma\downarrow1}(\sigma-1)\zeta(\sigma)=1$，所以

$$
\mathcal C(A)
\le\lim_{\sigma\downarrow1}
 (\sigma-1)\zeta(\sigma)\frac{1-q^{-\sigma}}{1-(2q)^{-\sigma}}
=\frac{1-1/q}{1-1/(2q)}=\frac{2(q-1)}{2q-1}.
\tag{48.12}
$$

这只需上极限。若 $\mathcal C(A)=1$，就不能遗漏任何素数。此时若还含复合生成元 $a$，则 $S(a)\subset A$，取有限集 $B=S(a)\cup\{a\}$ 得 $|B|=|S(a)|+1>|\bigcup_{b\in B}S(b)|=|S(a)|$，直接违反 $H(A)$；这里没有使用乘法独立。因此 $A=\mathcal P$。反向由 $H(\mathcal P)$ 与 $Z_{\mathcal P}=\zeta$ 立即得到。

（丁）最优性与有限常差。对 (48.6) 的任一有限乘法关系，若 $q$ 为奇素数，先取 $q$ 坐标；$q$ 只出现在生成元 $2q$ 中，故其指数差为零，再逐个素数坐标清零其余指数差。$q=2$ 时 $2q=4$ 的 $2$ 坐标系数为 $2$，同样成立。因此 $A_q$ 乘法独立，因而满足 $H(A_q)$，且在 $\operatorname{Re}s>1$ 精确有

$$
\frac{Z_{A_q}(s)}{\zeta(s)}=\frac{1-q^{-s}}{1-(2q)^{-s}},\qquad
\mathcal C(A_q)=\frac{2(q-1)}{2q-1}.
\tag{48.13}
$$

故实轴上界和容量上界都取等。另有

$$
\Theta_{A_q}(x)=\vartheta(x)+\log2\qquad(x\ge2q).
\tag{48.14}
$$

有限常差仍不能识别生成元；即使另给真实 $\vartheta(x)\sim x$，也会有 $\Theta_{A_q}(x)\sim x$ 而 $A_q\ne\mathcal P$。识别与锐界的证明未使用素数定理、函数方程或 $Z_A$ 的亚纯延拓。$\square$

**命题 48.3（删去 $H(A)$ 后的单位留数与同一零极点反例）。** 本节另置

$$
A_0=(\mathcal P\setminus\{3\})\cup\{4,9\}.
\tag{48.15}
$$

则 $A_0\ne\mathcal P$，且既不满足 $H(A_0)$ 也不乘法独立，但 $\mathcal C(A_0)=1$。确实 $B=\{2,4\}\subset A_0$ 的素因子并集只有 $\{2\}$，故 $H(A_0)$ 失败；同时 $4=2^2$。其 Euler 函数延拓到 $\operatorname{Re}s>0$ 后，与真实 $\zeta$ 在该半平面具有相同的全部零点、极点及各自重数，且在 $s=1$ 的留数同为 $1$。此外 $\Theta_{A_0}(x)=\vartheta(x)+\log12$ 对 $x\ge9$ 成立。

**证明。** $2,4\in A_0$ 且 $4=2^2$，所以 (48.2) 不是单射，(48.8) 的 $c_{A_0}(4)=2$：生成元 $4$ 一次与生成元 $2$ 两次被重复计数。由绝对收敛的 Euler 因子消去，在 $\operatorname{Re}s>1$ 有

$$
Z_{A_0}(s)=\zeta(s)R(s),\qquad
R(s)=\frac{1-3^{-s}}{(1-4^{-s})(1-9^{-s})}.
\tag{48.16}
$$

对任意整数 $k\ge2$ 及 $\operatorname{Re}s>0$，$|k^{-s}|<1$，故 $1-k^{-s}$ 不为零。于是 $R$ 在该半平面全纯且处处非零；以 $\zeta R$ 作延拓，便逐点保留 $\zeta$ 的零极点及重数，没有新增零点或极点。并且

$$
R(1)=\frac{2/3}{(3/4)(8/9)}=1,
\qquad \operatorname*{Res}_{s=1}Z_{A_0}(s)=1,
\qquad \mathcal C(A_0)=1.
\tag{48.17}
$$

最后，$x\ge9$ 时权重差为 $\log4+\log9-\log3=\log12$。因此重复分解确能补回遗漏素数造成的质量亏损；同一正半平面零极点和单位留数不能代替 $H(A)$。这里没有断言 $Z_{A_0}$ 满足 $\zeta$ 的函数方程，也没有从该反例推出任何负占用结论。$\square$

**注记 48.4（极点阶数、算术前件与实际联合桥）。** 单位 Abel 容量是 (48.3) 的实轴归一化条件，不能由单极点位置或对数导数的单位留数替代。具体说，若一个 Euler 函数在 $1$ 附近有 $Z(s)=C/(s-1)+O(1)$、$C>0$ 的亚纯展开，则

$$
-\frac{Z'(s)}{Z(s)}=\frac1{s-1}+O(1),\qquad
\operatorname*{Res}_{s=1}Z(s)=C.
\tag{48.18}
$$

当 $Z=Z_A$ 时，上述展开还给出完整实轴 Abel 极限及 $\mathcal C(A)=C$。左侧的留数 $+1$ 记录极点阶数，右侧 $C$ 还取决于函数的归一化和正则因子。独立的 $A_q$ 已使这两种信息分离；而 (48.16) 还使 $-Z_{A_0}'/Z_{A_0}=-\zeta'/\zeta-R'/R$ 的差在 $\operatorname{Re}s>0$ 全纯，同时保持 Euler 函数自身的单位留数，却失去独立性。

§46 的连续模型没有整数生成元 Euler 乘积和有限素因子 Hall 条件这些前件。对确有整数 Euler 结构的人工模型，若供应 $H(A)$ 与精确单位容量，定理 48.2 就锁定 $A=\mathcal P$；乘法独立是其中更强但非必要的充分条件，不必先供应完整函数方程。人工非实主部、实际显式公式中的 $-m_\rho/\rho$ 系数或同一零极点集合，只是各自变换及对数导数层面的约束，不能自动供应 $H(A)$ 或 Euler 函数的单位留数；不同变换的主部也不能未经对应就互换。

本节没有证明原来的 $\sum_{H:\vartheta(H)<H}1/H=\infty$，没有取得 §44 所需的实际负阶段参与长度，也没有支付 §41 在同一 $Y=C_M\times\mathbb T^2$ 上的实际 CM 跨块联合桥。实际 CM 点对、全部原有限地方、原 $q_H$、原过滤和同一个成功整数继续保持原义；识别真实生成元之后，真实 $\vartheta$ 的负谐和占用与同一整数上的 CM 联合成功仍须另外证明。

用白话说，$H(A)$ 只要求每个有限生成元集都能把生成元分配到不同的真实素因子坐标；这个分配只供比较，不说所有整数表示都唯一。把某个真实素数的 Euler 因子移到更大的复合生成元，只能减少实轴上的质量。若素数 $q$ 没有作为生成元出现，有限匹配中它或者空缺，或者只能被分给至少为 $2q$ 的整数；两种情形都受到同一个严格小于满容量的质量上界约束。因而精确满容量迫使每个真实素数都回来，随后 $H(A)$ 自己排除额外复合生成元。删去 $H(A)$ 后，同一个整数可被不同指数族重复计数，$A_0$ 正是靠这种重复把质量补回到一。这里的几何只是非负素因子坐标、有限匹配与容量饱和之间的严格关系，没有赋予它量子起源或物理同构；它也没有控制真实误差在负侧停留多久，更没有给出原 CM 条件与它在同一整数上的联合关系。

来源与新增范围。有限 Hall 匹配是 literature-attested 中间输入：Philip Hall，*On Representatives of Subsets*，*Journal of the London Mathematical Society* **s1-10** (1) (1935), 26–30，DOI [10.1112/jlms/s1-10.37.26](https://doi.org/10.1112/jlms/s1-10.37.26)；所用有限条件是每个左侧子集的邻集大小至少等于其大小，可参见公开的 [Hall's marriage theorem 条件表述](https://en.wikipedia.org/wiki/Hall%27s_marriage_theorem#Combinatorial_formulation)。真实 $\zeta$ 的 Euler 乘积与 $1$ 处单位留数分别见 NIST [DLMF 25.2(iv), (25.2.11)](https://dlmf.nist.gov/25.2#E11) 与 [DLMF 25.2(i)](https://dlmf.nist.gov/25.2#i)，均为成熟输入。本节的 repo-derived 综合范围是把有限素因子 Hall 条件接到 Euler 因子比较，得到指定遗漏 $q$ 的最优亏损、仅用上极限的单位容量识别，并保留实际 $\zeta$ 正半平面零极点和单位留数的删条件反例；乘法独立作为严格更强的可用充分子类，$H(A)$ 的弱化及其边界是本节新增的算术表述。不把 Hall 或 Euler 公式另列为新成果，也不主张全球文献优先性。

## 追加锚（本行以下为增补区）

## 49. 原共同周期上移动 CM 组合的统一分母尾部

**定义 49.1（原模型分母、地方权重与移动组合）。** 保持原 002 定义 13.1、17.1 的实际 $F,E_0,P_1,P_2$、全部 $U_v$、指定实嵌入与 $\alpha$。固定原 $M\ge1$，整数阶段 $H\ge2$ 的周期仍为 $q_H=q(H,H;M)$。本节不改变原有限目标空间或成功整数的含义。置

$$
R_m=[m_1]P_1+[m_2]P_2,\qquad r=\|m\|_2,\qquad
T_{n,m}=[n]R_m,\qquad
m\in\mathbb Z^2\setminus\{0\},\quad n\in\mathbb Z\setminus\{0\}.
\tag{49.1}
$$

原 (16.21) 给出 $\widehat h(R_m)=h_0r^2$，其中 $h_0>0$，故这些点及其任何非零整数倍均非挠。它们不等于 $O$，横坐标也不为零：在原 $y^2=x^3-x$ 上，$x=0$ 的点为二挠点。由原命题 16.2，$F$ 全实且 $[F:\mathbb Q]=8$。在 $\mathcal O_F$ 中定义互素整理想

$$
\begin{gathered}
(x(T))=A(T)B(T)^{-2},\qquad
b_v(T)=\operatorname{ord}_v B(T)=\tfrac12\max(0,-\operatorname{ord}_v x(T)),\\
\|I\|=N_{F/\mathbb Q}(I)^{1/8},\qquad
B(T)^{\le H}=\prod_{p\le H}\prod_{v\mid p}\mathfrak p_v^{b_v(T)},\qquad
B(T)^{>H}=\prod_{p>H}\prod_{v\mid p}\mathfrak p_v^{b_v(T)}.
\end{gathered}
\tag{49.2}
$$

这里 $(x(T))$ 是主分式理想，不要求 $A(T)$ 或 $B(T)$ 主理想。偶指数来自原整方程：若 $\operatorname{ord}_v x<0$，则 $x^3$ 的赋值严格小于 $x$，所以 $2\operatorname{ord}_v y=3\operatorname{ord}_v x$，迫使 $\operatorname{ord}_v x$ 为偶数。此论证包括二进地方。仍取 $\operatorname{ord}_v(\varpi_v)=1$、$e_v=\operatorname{ord}_v p$、$f_v=[k_v:\mathbb F_p]$，于是 $\sum_{v\mid p}e_vf_v=8$、$N(\mathfrak p_v)=p^{f_v}$。$B$ 始终由原整方程的 $x$ 定义；二进处的 $U_v$ 仍由原先固定的极小整模型定义。

**定理 49.2（全系数、同一周期倍数的分母预算）。** 存在只依赖上述固定原数据的 $C>0$ 和整数 $H_0\ge7$，使所有整数 $H\ge H_0$、所有 $m\in\mathbb Z^2\setminus\{0\}$ 及所有 $n\in q_H\mathbb Z\setminus\{0\}$ 同时满足

$$
0\le\log\|B(T_{n,m})^{\le H}\|
\le\log|n|+CH^5r^2,
\tag{49.3}
$$

$$
\left|\log\|B(T_{n,m})^{>H}\|-h_0n^2r^2\right|
\le C\bigl[H^5r^2+\log(2|n|r)\bigr].
\tag{49.4}
$$

特别地，误差对无限的 $n,m$ 范围统一：

$$
\sup_{\substack{m\in\mathbb Z^2\setminus\{0\}\\n\in q_H\mathbb Z\setminus\{0\}}}
\left\{\frac{\log\|B(T_{n,m})^{\le H}\|}{h_0n^2r^2}
+\left|\frac{\log\|B(T_{n,m})^{>H}\|}{h_0n^2r^2}-1\right|\right\}
\le\frac{CH^5}{q_H^2}\longrightarrow0.
\tag{49.5}
$$

这些常数不依赖 $m,n$；允许一个系数为零、$n<0$ 及任意大的 $r$。这里逃出的是分母的对数范数质量，不断言小素数不再整除分母。

**证明。** （甲）先在全部实嵌入上支付坐标高度。取通常的绝对对数高度 $h(x)=h([x:1])$。有限处绝对值为 $|a|_v=p^{-\operatorname{ord}_v(a)/e_v}$，其局部次数权重为 $e_vf_v/8$；八个实嵌入各有权重 $1/8$。故乘积公式的归一化给出准确分解

$$
h(x(T))=2\log\|B(T)\|+a_\infty(T),\qquad
a_\infty(T)=\frac18\sum_{\sigma:F\hookrightarrow\mathbb R}
\log\max(1,|x(\sigma T)|)\ge0.
\tag{49.6}
$$

每个 $\sigma$ 对点对作带独立符号的排列，故 $\sigma T_{n,m}=T_{n,m^\sigma}$，其中 $m^\sigma$ 是 $m$ 的带独立符号排列，仍有 $\|m^\sigma\|_2=r$、$\|m^\sigma\|_\infty=\|m\|_\infty$。原两点都在 $C=E_0(\mathbb R)^0$，因此所有这些共轭点均在 $C$，可使用原圆坐标。不能只取共同换号的两个系数。

横坐标在 $O$ 有二阶极点，以原不变微分圆坐标作局部参数，$x(S)\|\theta(S)\|_{\mathbb T}^2$ 在 $O$ 附近有有限正极限；离开 $O$ 的紧集上 $x$ 有界。因此存在固定 $C_\infty$，对 $S\in C\setminus\{O\}$ 有 $\max(1,|x(S)|)\le C_\infty\|\theta(S)\|_{\mathbb T}^{-2}$。原 (17.5) 对 $q=|n|$、$J=\|m\|_\infty\ge1$ 及每个 $m^\sigma$ 给出

$$
\|\theta(\sigma T_{n,m})\|_{\mathbb T}
=\|n\,m^\sigma\!\cdot\alpha\|_{\mathbb T}
\ge A(|n|\|m\|_\infty)^{-\mu},\qquad
0\le a_\infty(T_{n,m})\le C\log(2|n|r).
\tag{49.7}
$$

这里实极点展开只作为高度分解的成熟中间步骤；$A,\mu$ 是原 (17.5) 的固定常数，不随移动点重选。由原 (12.7)，$-\log2\le h(x(T))-2\widehat h(T)\le2\log2$。结合 (49.6)、原 (16.21) 与典范高度二次性，得到对所有非零整数 $n$、非零 $m$ 已成立的

$$
\left|\log\|B(T_{n,m})\|-h_0n^2r^2\right|
\le C\log(2|n|r),\qquad
\log\|B(S)\|\le\widehat h(S)+\log2.
\tag{49.8}
$$

第二式适用于这里任何非挠 $S\in E_0(F)$，只用 (49.6) 的实项非负及原高度比较，不需要对 $S$ 另设常数。

（乙）在非分歧奇地方使用共同第一层入口。记 $L_p(T)=\frac18\sum_{v\mid p}f_v b_v(T)\log p$，则 $\sum_pL_p(T)=\log\|B(T)\|$。固定 $p\le H$、$p\ne2,7$。原定理 16.3–16.4 给出 $e_v=1$、$n_p\le p^2$、$n_p\mid q_H$，以及 $[n_p]P_j\in U_v(1)$ 对所有 $v\mid p,j$ 成立。因此

$$
S_{p,m}=[n_p]R_m\in U_v(1),\qquad
T_{n,m}=[n/n_p]S_{p,m}.
\tag{49.9}
$$

此处不声称 $[n_p]P_j\in U_v(H)$。第一层已经足够，因为 $1>e_v/(p-1)$。形式对数在该层保赋值，$x=t^{-2}(1+t\mathcal O_v[[t]])$，所以对任意非零整数 $k$、非零 $S\in U_v(1)$ 有 $b_v([k]S)=b_v(S)+v_p(k)$。这是原形式群原理用于任意该层点的整数乘法，不是只对两个生成元的深度公式。

具体地，整形式群的对数有 $\mathcal L(t)=t+\sum_{j\ge2}a_jt^j/j$、$a_j\in\mathcal O_v$。若 $s=\operatorname{ord}_v t>e_v/(p-1)$，由 $v_p(j)\le(j-1)/(p-1)$ 得 $js-e_vv_p(j)>s$ 对 $j\ge2$ 成立，故 $\operatorname{ord}_v\mathcal L(t)=s$；再用 $\mathcal L([k]t)=k\mathcal L(t)$ 即得赋值增量 $e_vv_p(k)$。整数乘法与取负均保该深层子群。这也说明下文的全部赋值计算适用于负 $k$。

所有 $S_{p,m}$ 非挠，故全局和局部均非零；不存在零形式参数被当作有限赋值的情况。将 (49.9) 的公式按 $v\mid p$ 加权，利用 $\sum_{v\mid p}f_v=8$ 及 (49.8)，得

$$
\begin{aligned}
L_p(T_{n,m})
&=L_p(S_{p,m})+v_p(n/n_p)\log p\\
&\le h_0n_p^2r^2+\log2+v_p(n)\log p\\
&\le h_0p^4r^2+\log2+v_p(n)\log p.
\end{aligned}
\tag{49.10}
$$

（丙）在固定的 $2,7$ 处统一选择深层入口。对 $p\in\{2,7\}$、$v\mid p$，设原极小模型坐标为 $x_v$，把固定同构的逆写成 $x=u_v^2x_v+\beta_v$；$u_v\ne0$、$\beta_v\in F_v$ 均已固定。在 $7$ 处就是原模型，可取 $u_v=1,\beta_v=0$。在 $2$ 处不假定原整方程为极小方程，也不假定 $u_v$ 是单位。

选择固定正整数 $s_v$，满足 $s_v>e_v/(p-1)$、$s_v>\operatorname{ord}_v u_v$；若 $\beta_v\ne0$，再要求 $2\operatorname{ord}_v u_v-2s_v<\operatorname{ord}_v\beta_v$。在原 $U_v(s_v)$ 内，极小模型的参数 $t_v$ 给出 $\operatorname{ord}_v x_v=-2\operatorname{ord}_v t_v$，从而

$$
b_v(S)=\operatorname{ord}_v t_v(\iota_v S)-\operatorname{ord}_v u_v,
\qquad
b_v([k]S)=b_v(S)+e_vv_p(k)
\quad(0\ne k\in\mathbb Z).
\tag{49.11}
$$

两式中 $S\ne O$，且 $[k]S$ 非零时使用第二式。形式对数的赋值论证与（乙）相同。坐标比较的误差只是固定的 $-\operatorname{ord}_v u_v$；它不会随 $m$ 增长。一般仿射点上，两种坐标的 $\log\max(1,|x|_v)$ 之差也有固定界，由仿射变换及其逆各用一次非阿基米德三角不等式即得；所选深层将这个有界比较加强为 (49.11) 的准确式。

按原有限商中的阶，固定

$$
c_p=\operatorname{lcm}_{v\mid p,\ j=1,2}d_{v,j}(s_v)
\quad(p=2,7),\qquad
H_0\ge\max\bigl(\{7\}\cup\{s_v:v\mid14\}\bigr).
\tag{49.12}
$$

这些阶有限，来自原定义 13.1 的紧群开子群。由 $U_v(H)\subset U_v(s_v)$，$d_{v,j}(s_v)\mid d_{v,j}(H)$；所以 $H\ge H_0$ 时真正有 $c_p\mid q_H\mid n$，而且 $S_{p,m}=[c_p]R_m\in U_v(s_v)$ 对每个 $m$ 同时成立。入口只由两个固定生成元决定，未使用依赖 $R_m$ 的固定点常数。

这些 $S_{p,m}$ 及其非零整数倍仍非挠。由 (49.11) 和全部地方的次数恒等式 $\sum_{v\mid p}e_vf_v=8$，有

$$
\begin{aligned}
L_p(T_{n,m})
&=L_p(S_{p,m})+v_p(n/c_p)\log p\\
&\le h_0c_p^2r^2+\log2+v_p(n)\log p
\qquad(p=2,7).
\end{aligned}
\tag{49.13}
$$

这里 $7$ 的分歧和 $2$ 的极小模型都已计入，不删去任何原地方。另由 $q_H$ 的原定义，$[n]P_j\in U_v(H)$ 对 $p\le H$ 的所有 $v,j$ 成立，故 $T_{n,m}\in U_v(H)$；这项深层成员性来自 $n$，没有赋给较小的 $n_p$。

（丁）汇总并检查全部统一量词。将 (49.10)、(49.13) 相加，得到

$$
\begin{aligned}
\log\|B(T_{n,m})^{\le H}\|
&\le\sum_{p\le H}v_p(n)\log p
+h_0r^2\left(c_2^2+c_7^2+\sum_{\substack{p\le H\\p\ne2,7}}p^4\right)
+\pi(H)\log2\\
&\le\log|n|+CH^5r^2.
\end{aligned}
\tag{49.14}
$$

最后只用 $r\ge1$、$\sum_{j\le H}j^4\le H^5$、$\pi(H)\le H$；不需要素数密度或移动点的额外界。非负性来自整理想范数。(49.8) 减去这一小素数项，并将 $\log|n|$ 吸收到 $\log(2|n|r)$，即得 (49.3)–(49.4)。

为核实 (49.5) 的上确界，置 $N=|n|\ge q_H$。对 $r\ge1$，$\log r/r^2\le1/(2e)$，且 $\log(2N)/N^2$ 在 $N\ge1$ 上递减。因此

$$
\frac{\log(2Nr)}{N^2r^2}
\le\frac{\log(2q_H)+1/(2e)}{q_H^2},\qquad
\frac{H^5}{N^2}\le\frac{H^5}{q_H^2}.
\tag{49.15}
$$

原 (16.27) 给出固定 $M$ 下 $\log q_H\sim H^2$，故 $\log(2q_H)=O(H^2)$、$H^5/q_H^2\to0$。(49.3)–(49.4) 除以 $h_0N^2r^2$ 后即得 (49.5)，常数对所有 $n,m$ 统一。$\square$

原共振的准确消费者。在本卷原对偶向量 $(K_H(a-q_Hm\cdot\alpha),r_Hm)$ 中，每个非零 $m$ 对应的实际代数点是 $T_{q_H,m}$，并且 $\theta(T_{q_H,m})=q_Hm\cdot\alpha\pmod{\mathbb Z}$。因此无论它是否为所选的一条短共振，其分母都满足

$$
\log\|B(T_{q_H,m})^{\le H}\|\le\log q_H+CH^5\|m\|_2^2,
\qquad
\log\|B(T_{q_H,m})^{>H}\|
=h_0q_H^2\|m\|_2^2\bigl(1+O(H^5/q_H^2)\bigr),
\tag{49.16}
$$

误差对移动 $m$ 一致。原前两条共振若给出两个非零系数向量，可分别调用同一个结论；原周期倍数 $n=kq_H\ne0$ 也在范围内。这里的分母始终是这些实际点的原 $x$ 分母，并未换比较方向或代数点。总分母的主项是同一高度 $\widehat h(T_{n,m})$，而全部实嵌入只占 $O(\log(2|n|r))$；已要求的有限端深进入仍允许主要高度集中在 $p>H$。

本结论没有给出两份尾部分母的 $\gcd$、同一个地方上的联合下界、相互独立性或原 $p_H(\alpha)$ 的下界。各自的范数质量本身不含支持交叠信息：对不同有理素数 $\ell_1,\ell_2>H$，理想 $(\ell_1)^a,(\ell_2)^b$ 可各有任意大的对数范数，而共同因子仍为单位理想；这只是说明从质量数值到交叠需要新前提，不把这些理想当成原点的实现。一般原非零有限目标只要求成功整数落在相应余类，$n$ 不必属于 $q_H\mathbb Z$，所以不能将 (49.3)–(49.5) 扩称为全部成功整数的结论。原 $\sum_{H:\vartheta(H)<H}1/H$ 的发散、(31.2) 及实际同一 $Y$ 上的满测仍未得到证明。

用白话说，每个移动整数系数组合都有一笔由 $n^2\|m\|_2^2$ 决定的总高度。全部实嵌入靠近无穷远点所造成的坐标增长，只能拿走对数大小的份额。对每个小素数，先用原共同约化阶把两个生成元送进第一形式层，再作整数乘法，新增的分母深度只有该整数的素数指数；入口本身的分母用同一高度预算控制。二进和七进处先选一次对两个生成元都有效的深入口，所有移动组合随即共享它。把这些账相加，小素数所占的比例对全部系数和周期倍数都趋于零，因而主要分母质量必须留在截止之外。这并不说那些大素数对两条共振相同，也不说共振不能发生；要得到原满测，仍须把两条共振及跨块覆盖在同一整数、同一目标上的关系接起来。

来源与新增范围。原 002 的 (12.7)、命题 16.2、定理 16.3–16.4、(16.21)、(16.27) 与 (17.5) 分别供应高度比较、全部实共轭的独立符号排列、共同奇素数入口及其 $p^2$ 界、移动组合的准确典范高度、原周期主阶和全部 $q,m$ 的有限型；本节直接复用这些结论。形式参数展开与深层形式对数是 literature-attested 中间输入，见 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[IV §1、IV.5.5、IV.6.3–6.4、VII.2.2](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)；实二阶极点及圆一致化见其 VI §1。原定义 13.1 的极小模型和过滤保持不变。

固定点分母的先例为 Marco Streng，*Divisibility sequences for elliptic curves with complex multiplication*，*Algebra & Number Theory* **2** (2), 183–208，DOI [10.2140/ant.2008.2.183](https://doi.org/10.2140/ant.2008.2.183)：(1.1) 使用互素理想 $A B^{-2}$；§2 的命题 2.8 给出足够深层中的局部赋值增长；§3 的定理 3.21 给出固定非挠点的分母高度渐近。这里不将该固定点的误差常数套给随 $m$ 改变的 $R_m$，也不把其强整除性转给两个独立移动组合。本节的 repo-derived 新增是原过滤、共同周期及移动组合的统一高度预算 (49.3)–(49.5)，以及它对原共振点的 (49.16)；经典高度分解、固定点分母定理、形式群和二阶极点不另列为新成果，不主张全球文献优先性。

## 追加锚（本行以下为增补区）

## 50. 原行格约束下的共同尾部纯夹角界与实际剪切族

**定义 50.1（同一整数上的行格与共同质量）。** 全部数据、原整方程、全部有限地方、原 $U_v$、固定 $M$、$q_H$、$h_0$、$T_{n,u}$ 及理想范数严格沿用 §49。取线性独立的整数行 $m,l\in\mathbb Z^2$，并置

$$
\begin{gathered}
L=\mathbb Zm+\mathbb Zl,\quad D=|\det(m,l)|=[\mathbb Z^2:L]\ge1,\quad
r=\|m\|_2,\quad s=\|l\|_2,\\
\lambda_1(L)=\min_{0\ne z\in L}\|z\|_2,\qquad
\eta(m,l)=|\sin\varphi(m,l)|=\frac{D}{rs},\\
J_L(n)=B(T_{n,m})+B(T_{n,l}),\qquad
\mathcal A_H(n,u)=\log\|B(T_{n,u})^{>H}\|,\qquad
\mathcal G_H(n,L)=\log\|J_L(n)^{>H}\|.
\end{gathered}
\tag{50.1}
$$

这里 $n\in\mathbb Z\setminus\{0\}$，$u\in\mathbb Z^2\setminus\{0\}$；尾部按 (49.2) 截取，$\varphi\in(0,\pi)$ 是通常实夹角，允许钝角。两个整理想的 gcd 是理想和，各素理想指数为两指数的最小值；不要求任何分母理想为主理想。$J_L(n)$ 暂由所列基定义，基无关性在下面证明。共同尾部允许为单位理想，此时 $\mathcal G_H=0$。

**定理 50.2（§49 的统一共同尾部消费者）。** 对任意非零整数 $n$，$J_L(n)$ 只依赖完整行格 $L$，且对每个 $0\ne z\in L$ 都有

$$
J_L(n)\mid B(T_{n,z}),\qquad
\log\|J_L(n)\|\le h_0n^2\lambda_1(L)^2+\log2
\le\frac2{\sqrt3}h_0n^2D+\log2.
\tag{50.2}
$$

存在只依赖固定原数据的 $C_0>0$ 和整数 $H_1$，使置

$$
\epsilon_H=\frac{C_0H^5}{q_H^2}\le\frac12,\qquad
C_H=\frac{2/\sqrt3+\log2/(h_0q_H^2)}{1-\epsilon_H}
\longrightarrow\frac2{\sqrt3}
\tag{50.3}
$$

后，对所有整数 $H\ge H_1$、所有 $n\in q_H\mathbb Z\setminus\{0\}$ 及所有独立整数行 $m,l$ 同时成立 $\mathcal A_H(n,m),\mathcal A_H(n,l)>0$ 与

$$
0\le\frac{\mathcal G_H(n,L)}
 {\sqrt{\mathcal A_H(n,m)\mathcal A_H(n,l)}}
\le C_H|\sin\varphi(m,l)|.
\tag{50.4}
$$

常数不随 $n,m,l$ 变化；(50.4) 没有独立于夹角的加性误差。(50.2) 不要求 $n\in q_H\mathbb Z$，而 (50.3)–(50.4) 的尾部比例只在所写周期倍数范围断言。

**证明。** 先在本消费者内使用原整方程的经典形式群过滤。固定任意有限地方 $v$，暂把 (49.2) 的 $b_v$ 延拓到局部群：在 $O$ 取 $\widetilde b_v(O)=+\infty$，在非零仿射点取 $\widetilde b_v(S)=\tfrac12\max(0,-\operatorname{ord}_v x(S))$，其中 $x(S)=0$ 时取零。对正整数 $a$，令

$$
V_v(a)=\{O\}\cup\{S\ne O:\operatorname{ord}_v x(S)\le-2a\}.
\tag{50.5}
$$

若 $\operatorname{ord}_v x(S)<0$，原方程 $y^2=x^3-x$ 迫使 $2\operatorname{ord}_v y=3\operatorname{ord}_v x$，故 $t=-x/y$ 满足 $\operatorname{ord}_v t=\widetilde b_v(S)>0$。原整方程在 $O$ 的整形式展开给出 $w=-1/y=t^3(1+t\mathcal O_v[[t]])$、$x=t/w=t^{-2}(1+t\mathcal O_v[[t]])$。更具体地，$w=t^3-tw^2$ 在 $t\in\mathfrak m_v$ 时有唯一 $w\in\mathfrak m_v$ 解；导数 $1+2tw$ 为单位。上述负 $x$ 赋值点有 $w\in\mathfrak m_v$，因而确属这一形式圆盘；反向由展开也得到全部这样的点。

原方程的形式加法 $\mathcal F(X,Y)=X+Y+\text{高次整项}$ 和形式逆元 $\mathfrak i(X)=-X+\text{高次整项}$ 在 $\mathfrak m_v$ 收敛，保每个 $\mathfrak m_v^a$。故 $V_v(a)$ 是原局部椭圆群的子群，且对所有局部点 $S,T$ 有

$$
\widetilde b_v(S+T)\ge
\min\{\widetilde b_v(S),\widetilde b_v(T)\},\qquad
\widetilde b_v([-1]S)=\widetilde b_v(S).
\tag{50.6}
$$

当最小值为零时第一式只用非负性；为正时两点在同一 $V_v(a)$，结果为 $O$ 也由 $+\infty$ 约定包括。由此任何正、负或零整数的线性组合都保共同深度。这里仅在负 $x$ 赋值圆盘中使用 $b_v=\operatorname{ord}_v(-x/y)$，不在任意仿射点上使用 $b_v=\max(0,\operatorname{ord}_v(-x/y))$。

这段论证只要求原方程系数整，不要求极小、好约化或 $p\ne2$，所以包括原二进地方及全部分歧地方。$V_v(a)$ 只是证明原 $x$ 分母关系的子群，不替换原先以极小整方程指定的 $U_v(a)$；两者无需相等。此处也没有把 $p\nmid D$ 当成整个局部椭圆群上的可逆性：原 002 §16 的 $p=3$ 两点约化为非零二挠点，$2$ 虽为 $3$ 进单位，$[2]$ 在约化群仍有非零核。

令 $j_v=\min\{b_v(T_{n,m}),b_v(T_{n,l})\}$。对 $z=am+bl\in L$，有 $T_{n,z}=[a]T_{n,m}+[b]T_{n,l}$，所以当 $z\ne0$ 时 (50.6) 给出 $b_v(T_{n,z})\ge j_v$。由原 (16.21)，$\widehat h(T_{n,z})=h_0n^2\|z\|_2^2>0$，故此时点非挠、非零，分母合法。组合过程中 $z=0$ 对应的 $O$ 只参与子群计算，不定义 $B(O)$，也不将零参数的赋值当有限数。

因此在每个素理想上 $j_v\le b_v(T_{n,z})$，得到 (50.2) 的整除式。若 $m',l'$ 是 $L$ 的另一整数基，每个新基行都是旧基行的整数线性组合，故新基两指数的最小值不小于 $j_v$；反过来使用逆整数换基又得相反不等式。两个最小值遂在全部地方相等，证明理想身份的基无关性。这是逐素理想论证，不选择 gcd 的生成元，也不除以行列式。

取最短非零 $z\in L$，刚证的整除与 (49.8)、原 (16.21) 给出

$$
\log\|J_L(n)\|\le\log\|B(T_{n,z})\|
\le\widehat h(T_{n,z})+\log2
=h_0n^2\lambda_1(L)^2+\log2.
\tag{50.7}
$$

本消费者所用的二维 Hermite 步骤也可直接写全。最短向量 $z$ 在自由群 $L$ 中为本原元，否则除以大于一的整数仍在 $L$ 而更短。因此以 Bézout 换基把它补成 $L$ 的基 $z,w$。从 $w$ 减去适当整数倍 $z$，可使 $|\langle w,z\rangle|/\|z\|_2\le\|z\|_2/2$。又因 $w\ne0$，最短性给出 $\|w\|_2\ge\|z\|_2$，所以 $w$ 垂直于 $z$ 的分量长度至少为 $\sqrt3\|z\|_2/2$。基平行四边形面积即 $D$，从而

$$
D\ge\frac{\sqrt3}{2}\|z\|_2^2,
\qquad \lambda_1(L)^2\le\frac2{\sqrt3}D.
\tag{50.8}
$$

这完成任意 $n\ne0$ 的 (50.2)，没有使用周期倍数或尾部渐近。

现在才取 $n\in q_H\mathbb Z\setminus\{0\}$。由 (49.5)，选固定 $C_0,H_1$ 使 (50.3) 成立，且对每个非零整数行 $u$ 同时有

$$
(1-\epsilon_H)h_0n^2\|u\|_2^2
\le\mathcal A_H(n,u)
\le(1+\epsilon_H)h_0n^2\|u\|_2^2.
\tag{50.9}
$$

故两份尾部质量都严格为正。尾部截取保理想整除且不增范数，(50.2) 给出 $0\le\mathcal G_H(n,L)\le(2/\sqrt3)h_0n^2D+\log2$。再用 $D\ge1$、$n^2\ge q_H^2$，有

$$
\begin{aligned}
\frac{\mathcal G_H(n,L)}{\sqrt{\mathcal A_H(n,m)\mathcal A_H(n,l)}}
&\le\frac{(2/\sqrt3)h_0n^2D+\log2}
 {(1-\epsilon_H)h_0n^2rs}\\
&=\frac{2/\sqrt3+\log2/(h_0n^2D)}{1-\epsilon_H}\,\frac D{rs}
\le C_H|\sin\varphi(m,l)|.
\end{aligned}
\tag{50.10}
$$

$\epsilon_H\to0$ 与 $q_H\to\infty$ 来自 (49.5) 及原 (16.27)，故 $C_H\to2/\sqrt3$。尤其当行随 $H,n$ 移动而夹角任意小时，$\log2$ 仍已随 $D/(rs)$ 一起吸收，不遗留单独加性项。$\square$

**推论 50.3（单位行格的实际剪切族及较小份额）。** 对每个整数 $k$，取 $m_k=(k,1)$、$l_k=(k+1,1)$，仍使用同一原数据和同一非零整数 $n$。则对任意这样的 $n$ 精确有

$$
\begin{aligned}
J_{\mathbb Z^2}(n)
&=\gcd\bigl(B([n]P_1),B([n]P_2)\bigr)\\
&=\gcd\bigl(B([n]([k]P_1+P_2)),
             B([n]([k+1]P_1+P_2))\bigr).
\end{aligned}
\tag{50.11}
$$

这里每个 gcd 都指理想和，截取任意 $>H$ 尾部后身份仍成立。对 (50.3) 的全部 $H\ge H_1$、$n\in q_H\mathbb Z\setminus\{0\}$ 和全部 $k\in\mathbb Z$，还有

$$
\begin{gathered}
|\sin\varphi(m_k,l_k)|
=\frac1{\sqrt{k^2+1}\sqrt{(k+1)^2+1}},\\
0\le\frac{\mathcal G_H(n,\mathbb Z^2)}
 {\min\{\mathcal A_H(n,m_k),\mathcal A_H(n,l_k)\}}
\le\frac{1+\log2/(h_0q_H^2)}
 {(1-\epsilon_H)\,[1+\min\{k^2,(k+1)^2\}]}
=O(k^{-2})\quad(|k|\to\infty).
\end{gathered}
\tag{50.12}
$$

$O$ 常数对 $H,n,k$ 统一。这是共同尾部占两份中较小的对数质量之比例，强于只把 (50.4) 原样用于几何平均。

**证明。** 两行行列式为 $-1$，且 $l_k-m_k=(1,0)$、$m_k-k(l_k-m_k)=(0,1)$，故其整数行格恰为 $\mathbb Z^2$。定理 50.2 的换基身份给出 (50.11)，两个新点的高度分别为 $h_0n^2(k^2+1)$、$h_0n^2((k+1)^2+1)$，所以无零点或挠点例外。该格的最短长度为 $1$，由 (50.7) 有 $\mathcal G_H(n,\mathbb Z^2)\le h_0n^2+\log2$；再用 (50.9) 同时下界两份质量，即得 (50.12)。当 $|k|\ge2$ 时，$1+\min\{k^2,(k+1)^2\}\ge k^2/4$，而前面的系数至多 $2(1+\log2/h_0)$，从而所写 $O(k^{-2})$ 对所有移动参数统一。角度恒等式直接来自 $D=1$。$\square$

一般两行不能把几何平均比例直接换成占较小份额的同一纯正弦比例。事实上同一证明支付的是

$$
\frac{\mathcal G_H(n,L)}{\min\{\mathcal A_H(n,m),\mathcal A_H(n,l)\}}
\le C_H\frac D{\min\{r^2,s^2\}}
=C_H|\sin\varphi(m,l)|\max\{r/s,s/r\}.
\tag{50.13}
$$

所以除非另有长度比控制，就必须保留这个额外因子；剪切族的 (50.12) 则已直接用其最短向量和两行准确长度支付所需条件。

适用边界。共同质量的这些上界不供应正下界，尤其不保证共同尾部含任何素理想；允许单位理想不等于已证明原点在某个参数上实现单位理想。剪切族确由实际原代数点组成，却不保证这两行同时实现原先选定的前两条短共振系数。上界也不证明相互独立、原 $p_H(\alpha)$ 下界、(31.2)、$\sum_{H:\vartheta(H)<H}1/H$ 发散或同一实际 $Y=C_M\times\mathbb T^2$ 上的满测。一般原非零有限目标的成功整数仍可能只在相应余类中，不能把周期倍数上的 (50.4)、(50.12) 推到那些整数。这里没有把不同整数、不同地方或各自可达的最优值当作同一实现。

用白话说，两份分母共同含有的每一层素理想，都必须随两行的所有整数加减保留下来。因此约束共同部分的不是所选两行各自有多长，而是它们生成的完整行格里最短的非零组合有多短。这个短组合对应同一 $n$ 上的实际非挠点，其高度给共同部分设定上限；二维面积又把短组合的长度压到行列式尺度。§49 同时保证两份尾部各自接近各自的二次高度，除法后就得到绝对正弦界，钝角也一样。整数行列式至少为一，使固定高度常差也能并入正弦系数，所以极小夹角不会被一个固定加性误差淹没。

剪切族把这个关系说得更具体：两行可以一起越来越长、越来越接近平行，但作差后仍是第一坐标方向，再减去整数倍又得到第二坐标方向；完整行格始终没变，共同分母也精确没变。各自行高却按 $k^2$ 增长，于是共同尾部在较小一份中所占比例至多按 $k^{-2}$ 缩小。这只限制“最多共享多少”，没有支付“至少共享多少”、哪些行实际成为共振，以及跨阶段、跨条件的联合覆盖。

来源与新增范围。原 002 的 (16.21)、本卷 (49.5)、(49.8) 分别供应原点组合的准确二次高度、周期倍数上的全系数统一尾部质量和原分母高度上界，本节直接复用。原整方程在单位元的整展开、形式群与各深度子群是 literature-attested 中间步骤，见 Silverman，*The Arithmetic of Elliptic Curves*，第二版，[IV §§1–3，特别是 IV §1 的负 $x$ 赋值像与 IV §3 的子群](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。负 $x$ 赋值过滤的先例另见 Streng，*Divisibility sequences for elliptic curves with complex multiplication*，[§2](https://msp.org/ant/2008/2-2/ant-v2-n2-p04-s.pdf)，DOI [10.2140/ant.2008.2.183](https://doi.org/10.2140/ant.2008.2.183)。gcd 的整数换基与二维 Hermite 界都是成熟步骤；后者的常数及 Cassels 的出处可参见 [Hermite constant](https://en.wikipedia.org/wiki/Hermite_constant)，本证明已给出所用二维约化。

数域 gcd 高度的更强小量结论不能无条件借来：Silverman，[*Generalized Greatest Common Divisors, Divisibility Sequences, and Vojta’s Conjecture for Blowups*，定理 3](https://arxiv.org/pdf/math/0407415) 明列 Vojta 前提及例外集合；其 [*Common Divisors of Elliptic Divisibility Sequences over Function Fields*，定理 3](https://arxiv.org/pdf/math/0402016) 的常 $j$ 结论属于特征零函数域，不能改作这里的无条件数域结论。本节只用已写明的短行格高度上界；repo-derived 新增范围是它与 §49 原实际点统一预算的联合消费者 (50.4)，以及同一原数据、同一 $n$ 的实际剪切身份和较小份额界 (50.11)–(50.12)。经典形式群、gcd 换基与 Hermite 步骤不另列为新一般理论，也不主张全球文献优先性。

## 追加锚（本行以下为增补区）
