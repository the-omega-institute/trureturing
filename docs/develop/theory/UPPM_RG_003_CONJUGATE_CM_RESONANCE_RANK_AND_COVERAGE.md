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
