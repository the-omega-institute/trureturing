# 原共轭 CM 临界阶段的共振秩、覆盖与联合能量

## 24. 原有限端、真实整数纤维与共振长度

**定义 24.1（固定的原临界阶段）。** 固定 [UPPM-RG 002](UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md) 定义 20.1、21.1、22.1 的全部实际 CM 数据、实方向 $\alpha\in\mathbb T^2$、原有限地方过滤 $U_v$、完整有限目标同胚 $\eta$，以及整数 $M\ge1,a_0\in\mathbb Z$。令

$$
\begin{gathered}
\mathbb T=\mathbb R/\mathbb Z,\qquad
A=\{n\ge1:n\equiv a_0\pmod M\},\qquad
C_M=a_0+M\widehat{\mathbb Z},\\
Y=C_M\times\mathbb T^2,\qquad
\nu=\lambda_{C_M}\otimes m_{\mathbb T^2},\\
c_0>0,\quad \beta,\gamma\ge0,\quad \beta+\gamma>0,\quad c_0^2+2\beta=1,\\
h(n)=\max\left(2,\left\lfloor c_0\sqrt{\log(n+2)}\right\rfloor\right),\qquad
\rho(n)=(n+2)^{-\beta}(\log(n+2))^{-\gamma}.
\end{gathered}
\tag{24.1}
$$

这里两因子上的测度均为归一化 Haar 测度，$q(H,H;M)$ 始终是原全部有限地方条件的共同周期，且 $M\mid q(H,H;M)$，不另选模数。置

$$
\begin{gathered}
\vartheta(t)=\sum_{p\le t}\log p,\qquad
\mathcal H_-=\{H\in\mathbb Z:H\ge7,\ \vartheta(H)<H\},\\
X_H=\left\lfloor\exp\!\left(\frac{(H+1/2)^2}{c_0^2}\right)\right\rfloor,
\qquad Q_H=q(H,H;M),\qquad r_H=\rho(2X_H),\\
J_H=\#\{X_H<n\le2X_H:n\in A\},\qquad
K_H=\frac{MJ_H}{Q_H},\\
m_H=4K_Hr_H^2,\qquad \Delta_H=K_Hr_H^2=\frac{m_H}{4},\\
a_H=\lfloor K_H\rfloor,\qquad \tau_H=K_H-a_H.
\end{gathered}
\tag{24.2}
$$

$\Delta_H$ 表示格的对偶协体积，区别于原定义 21.1 中表示 $q_H/M$ 的 $d_H$。以下均在原定义 21.1 的充分大阶段尾部，并只取满足

$$
H\in\mathcal H_-,\qquad 0<r_H<\frac14,\qquad \Delta_H\ge1
\tag{24.3}
$$

的阶段。原定理 21.2 保证 $\mathcal H_-$ 无界、$\Delta_H\to\infty$、$r_H\to0$，故这些条件仅去掉有限个原好阶段；并且 $K_H=\Delta_H/r_H^2>16$。同一定理保证整块 $h(n)=H$，所以半径 $r_H$ 的子事件仍包含于半径 $\rho(n)$ 的原事件。

**定义 24.2（同源目标上的计数与覆盖）。** 对任意比较方向 $\omega\in\mathbb T^2$，保留定义 24.1 的全部有限端。在块 $X_H<n\le2X_H$ 上令

$$
\begin{aligned}
F_{n,H}(\omega)&=
\begin{cases}
(n+Q_H\widehat{\mathbb Z})\times
 \{z:\|z_j-n\omega_j\|_{\mathbb T}<r_H\ (j=1,2)\},&n\in A,\\
\varnothing,&n\notin A,
\end{cases}\\
V_H(u,z;\omega)&=\sum_{X_H<n\le2X_H}\mathbf1_{F_{n,H}(\omega)}(u,z),\\
B_H(\omega)&=\{(u,z)\in Y:V_H(u,z;\omega)>0\},\\
b_H(\omega)&=\nu(B_H(\omega)),\qquad
\mathcal E_H(\omega)=\int_Y V_H(u,z;\omega)^2\,d\nu,\\
N_H(u)&=\#\{X_H<n\le2X_H:n\in A,\ u\equiv n\pmod{Q_H}\}.
\end{aligned}
\tag{24.4}
$$

每个 $F_{n,H}(\omega)$ 中的有限端与两个实端共用同一个整数 $n$。特别地，$\omega=\alpha$ 时，这些就是原定义 21.1 的事件。对固定 $u$ 还定义

$$
\begin{aligned}
b_H(u;\omega)&=m_{\mathbb T^2}\{z:V_H(u,z;\omega)>0\},\\
e_H(u;\omega)&=\int_{\mathbb T^2}V_H(u,z;\omega)^2\,dm_{\mathbb T^2}(z),\\
m_H(u)&=4r_H^2N_H(u),\qquad
P_H(\omega)=\frac{\sup_{(u,z)\in Y}V_H(u,z;\omega)}{m_H}.
\end{aligned}
\tag{24.5}
$$

**定义 24.3（前两条独立共振的截断乘积）。** 固定 $\omega$ 的一个实提升，定义

$$
\begin{gathered}
\Lambda_H(\omega)=
\left\{\left(\frac{\ell}{K_H},\frac{\ell Q_H\omega-b}{r_H}\right):
\ell\in\mathbb Z,\ b\in\mathbb Z^2\right\},\\
L_H(\omega)=\Lambda_H(\omega)^*
=\{(K_H(a-Q_Hk\cdot\omega),r_Hk):a\in\mathbb Z,\ k\in\mathbb Z^2\}.
\end{gathered}
\tag{24.6}
$$

对偶星号指整数内积对偶，范数取欧氏范数。任意三维满秩格 $L$ 的第 $i$ 个欧氏逐次极小为

$$
\lambda_i(L)=\min\{t>0:
\dim_{\mathbb R}\operatorname{span}(L\cap\overline B(0,t))\ge i\},
\qquad 1\le i\le3.
$$

格的离散性使上述最小值取得。记

$$
\begin{gathered}
\lambda_{i,H}(\omega)=\lambda_i(L_H(\omega)),\qquad
0<\lambda_{1,H}\le\lambda_{2,H}\le\lambda_{3,H},\\
p_H(\omega)=\min(1,\lambda_{1,H}(\omega))
              \min(1,\lambda_{2,H}(\omega)),\\
\mathfrak r_H(\omega)=
\dim_{\mathbb R}\operatorname{span}
 \{v\in L_H(\omega):\|v\|_2<1\}.
\end{gathered}
\tag{24.7}
$$

严格阈值 $1$ 决定这里的共振秩，长度恰为 $1$ 的向量不计入。更换 $\omega$ 的整数提升只重新编号 $b,a$，不改变这两个格及其长度。

## 25. 原严格窗的逐点格计数上界

**定理 25.1（大质量下的第三长度与全部目标上界）。** 对定义 24.1 的每个阶段、每个 $\omega\in\mathbb T^2$，有

$$
\begin{gathered}
\det\Lambda_H(\omega)=\Delta_H^{-1},\qquad
\det L_H(\omega)=\Delta_H,\\
\lambda_{3,H}(\omega)\ge\Delta_H^{1/3}\ge1,\qquad
\mathfrak r_H(\omega)\le2,\\
V_H(u,z;\omega)\le
\min\left\{\lceil K_H\rceil,\frac{108m_H}{p_H(\omega)}\right\}
\quad\text{对每个 }(u,z)\in Y.
\end{gathered}
\tag{25.1}
$$

**证明。** 暂记 $Q=Q_H,K=K_H,r=r_H,\Delta=\Delta_H,m=m_H$，并省去长度的阶段、方向下标。$\Lambda=\Lambda_H(\omega)$ 的基矩阵可取

$$
\mathsf A=
\begin{pmatrix}
1/K&0&0\\
Q\omega_1/r&-1/r&0\\
Q\omega_2/r&0&-1/r
\end{pmatrix}.
$$

其行列式绝对值为 $1/\Delta$。与第二、三列的整数配对强制对偶向量的后两坐标为 $rk$；再与第一列配对，得到第一坐标 $K(a-Qk\cdot\omega)$，即 (24.6)，对偶协体积为 $\Delta$。

在 $L=\Lambda^*$ 中依次选取独立向量 $w_i$，使 $\|w_i\|_2\le\lambda_i$。这是逐次极小定义的直接用法：半径 $\lambda_i$ 内的格向量张成至少 $i$ 维，故总能避开此前的至多 $i-1$ 维张成空间。它们相对任一格基的坐标构成非奇异整数矩阵，行列式绝对值至少为 $1$。Hadamard 不等式于是给出

$$
\Delta\le|\det(w_1,w_2,w_3)|
\le\prod_{i=1}^3\|w_i\|_2
\le\prod_{i=1}^3\lambda_i\le\lambda_3^3.
\tag{25.2}
$$

因此 $\lambda_3\ge\Delta^{1/3}\ge1$。若开单位球中有三个独立向量，其最大长度严格小于 $1$，就与此矛盾，故共振秩至多为二。

下面只使用经典格点计数的上界。Freyer–Lucas，*Interpolating between volume and lattice point enumerator with successive minima*，[arXiv:2105.13090v2](https://arxiv.org/pdf/2105.13090v2)，第 1 页定义 (1.1) 后将任意凸体 $C$ 的逐次极小定义为 $\operatorname{cs}(C)=(C-C)/2$ 的逐次极小；第 3 页 Corollary 1.2 给出

$$
\#(C\cap\mathbb Z^n)
\le\prod_{i=1}^n\left(\frac2{\lambda_i(C,\mathbb Z^n)}+n\right).
\tag{25.3}
$$

这里 $C$ 只须是具有非空内部的紧凸体，不要求关于原点对称。该文第 1 页 (1.2) 的 Minkowski 第二定理，经过格基线性变换并用于三维欧氏单位球，给出

$$
\prod_{i=1}^3\lambda_i(L)
\le\frac{2^3}{\operatorname{vol}(\overline B(0,1))}\det L
=\frac6\pi\Delta<2\Delta.
\tag{25.4}
$$

这些是已有的一般格论输入，以下只将它们用于本条的真实纤维。

令 $D=Q/M\in\mathbb Z_{\ge1}$。写 $u=a_0+Mv$ 后，块内的 $n=a_0+Mt$ 对应连续 $J_H$ 个整数 $t$，而有限端要求 $t\equiv v\pmod D$。欧几里得分解

$$
J_H=a_HD+s_H,\qquad 0\le s_H<D,\qquad s_H/D=\tau_H
$$

逐类给出

$$
\begin{gathered}
N_H(u)\in\{\lfloor K\rfloor,\lceil K\rceil\}\quad(u\in C_M),\\
\lambda_{C_M}(N_H=a_H)=1-\tau_H,\qquad
\lambda_{C_M}(N_H=a_H+1)=\tau_H.
\end{gathered}
\tag{25.5}
$$

当 $\tau_H=0$ 时只有 $N_H=a_H$。因 $K>16$，每个纤维均非空。其最小允许整数记为 $n_0(u)$，所有允许整数准确为

$$
n_0(u)+\ell Q,\qquad \ell=0,\ldots,N_H(u)-1.
\tag{25.6}
$$

这个首项由 $u\bmod Q$ 决定。取 $z$ 的实提升并置

$$
\xi=\left(0,\frac{n_0(u)\omega-z}{r}\right),\qquad N=N_H(u).
$$

每个命中整数唯一对应于 $\xi+\Lambda$ 中的一个点，其时间坐标为 $\ell/K$，空间两坐标属于 $(-1,1)^2$。唯一性是因为两个不同整数提升若均在同一实窗内，其差的绝对值会小于 $2r<1$。反向也成立，故准确的严格窗公式是

$$
V_H(u,z;\omega)=
\#\left((\xi+\Lambda)\cap
 \left([0,(N-1)/K]\times(-1,1)^2\right)\right).
\tag{25.7}
$$

特别地，$V_H\le N\le\lceil K\rceil$。又

$$
N-1\le\lceil K\rceil-1\le K,
$$

所以这些点全在 $[0,1]\times[-1,1]^2$ 中，进而在以 $c=(1/2,0,0)$ 为中心、半径 $3/2$ 的闭球中；角点到 $c$ 的距离恰为 $3/2$。

记 $a_i=\lambda_i(\Lambda)$。将这只闭球平移 $-\xi$，再用 $\mathsf A^{-1}$ 送到整数格。所得紧凸体为

$$
C=\mathsf A^{-1}\bigl(\overline B(c,3/2)-\xi\bigr),\qquad
\operatorname{cs}(C)=\mathsf A^{-1}\overline B(0,3/2).
$$

中心对称化消掉平移，其相对 $\mathbb Z^3$ 的逐次极小恰为 $2a_i/3$。因此 (25.3) 对每个 $\xi$ 都给出

$$
V_H(u,z;\omega)\le\prod_{i=1}^3\left(\frac3{a_i}+3\right).
\tag{25.8}
$$

为把它写成原共振长度，直接核对经典的互反下界。对任意 $i$，在 $\Lambda$ 中取 $i$ 个独立向量，长度至多 $a_i$；在 $\Lambda^*$ 中取 $4-i$ 个独立向量，长度至多 $\lambda_{4-i}$。两张成空间的维数和为 $4>3$，它们不可能正交，否则第二空间的维数至多 $3-i$。所以某对向量具有非零内积。该内积是非零整数，Cauchy–Schwarz 遂给出

$$
a_i\lambda_{4-i}\ge1\qquad(i=1,2,3).
\tag{25.9}
$$

结合 (25.8)、(25.4) 及 $\lambda_3\ge1$，得到

$$
\begin{aligned}
V_H(u,z;\omega)
&\le27\prod_{i=1}^3(1+\lambda_i)
\le216\prod_{i=1}^3\max(1,\lambda_i)\\
&=216\frac{\lambda_1\lambda_2\lambda_3}
 {\min(1,\lambda_1)\min(1,\lambda_2)}
\le\frac{432\Delta}{p_H(\omega)}
=\frac{108m}{p_H(\omega)}.
\end{aligned}
\tag{25.10}
$$

这证明了 (25.1)。这里的球只上包实际命中点，没有把闭球中的额外点计作命中，也没有将 (25.3) 改为任意平移窗中的正格点下界。用白话说，平均命中量足够大时，不可能再有第三条独立的短共振；经典格计数把任一目标上的重复命中上限压到前两条共振宽度乘积的倒数。$\square$

## 26. 同一首中心的双条带与覆盖双边界

**定理 26.1（原阶段的两共振覆盖率）。** 对定义 24.1 的每个阶段和每个方向 $\omega$，记 $p=p_H(\omega)$。则对每个 $u\in C_M$ 有

$$
\frac{p}{108}\frac{N_H(u)}{K_H}
\le b_H(u;\omega)\le\min(1,12p),
\tag{26.1}
$$

而完整目标空间上的覆盖满足

$$
\boxed{\frac{p}{108}\le b_H(\omega)\le\min(1,12p).}
\tag{26.2}
$$

**证明。** 仍暂记 $Q,K,r,m,\lambda_i$，并沿用 (25.6) 的同一个 $u$、同一个 $n_0(u)$。先证上界。如果 $\lambda_1\ge1$，则 $p=1$，由概率不超过 $1$ 即可。

如果 $\lambda_1<1\le\lambda_2$，取长度为 $\lambda_1$ 的非零对偶向量

$$
v_1=(t_1,rk_1),\qquad
t_1=K(a_1-Qk_1\cdot\omega),\qquad
a_1\in\mathbb Z,\quad k_1\in\mathbb Z^2.
$$

$k_1\ne0$，因为 $k_1=0$ 时非零向量长度至少为 $K>16$。若 $z$ 被 (25.6) 的第 $\ell$ 项命中，则由严格实窗及整数 $a_1$ 有

$$
\begin{aligned}
\|k_1\cdot(z-n_0(u)\omega)\|_{\mathbb T}
&\le r\|k_1\|_1+(N_H(u)-1)|a_1-Qk_1\cdot\omega|\\
&\le\sqrt2\,r\|k_1\|_2+|t_1|
\le\sqrt3\,\lambda_1.
\end{aligned}
\tag{26.3}
$$

最后一步是对二元组 $(r\|k_1\|_2,|t_1|)$ 的 Cauchy–Schwarz；同时用了 $N_H(u)-1\le K$，没有以平均长度替换实际项数。非零整数 character $z\mapsto k_1\cdot z$ 是到圆的满射，故将两圆 Haar 推成圆 Haar。因此该纤维覆盖至多为 $\min(1,2\sqrt3\lambda_1)$，从而不超过 $\min(1,12p)$。

余下 $\lambda_2<1$ 时，可选择独立的 $v_i=(t_i,rk_i)$，使

$$
\|v_i\|_2=\lambda_i,\qquad
t_i=K(a_i-Qk_i\cdot\omega),\qquad i=1,2.
\tag{26.4}
$$

确实，先取最短向量，再从半径 $\lambda_2$ 的格向量中避开其直线；第二条长度若严格小于 $\lambda_2$，就与第二逐次极小的定义矛盾。即使两极小相等，这个选择也成立。两条 $k_i$ 均非零。

现在证明 $k_1,k_2$ 在 $\mathbb R^2$ 中独立。反设它们相关，则

$$
(k_1\cdot\omega)k_2-(k_2\cdot\omega)k_1=0.
$$

因此 $v_1\wedge v_2$ 的纯空间分量为零，而时间与空间混合的两个分量组成向量

$$
t_1rk_2-t_2rk_1=Kr(a_1k_2-a_2k_1).
\tag{26.5}
$$

因 $v_1,v_2$ 独立，右端不能为零；括号内是非零整数向量，其欧氏长度至少为 $1$。所以

$$
\|v_1\wedge v_2\|_2\ge Kr=\frac{\Delta_H}{r}>4.
$$

另一方面，欧氏面积上界给出

$$
\|v_1\wedge v_2\|_2\le\|v_1\|_2\|v_2\|_2
=\lambda_1\lambda_2<1,
$$

矛盾。故以 $k_1,k_2$ 为行的整数矩阵 $\mathsf K$ 行列式非零。

每个被覆盖的 $z$ 同时满足两条 (26.3)，而两条带的中心均由当前这个 $u$ 的 $n_0(u)\omega$ 给出。环面同态

$$
\Phi:\mathbb T^2\longrightarrow\mathbb T^2,\qquad
z\longmapsto\mathsf K z
$$

是满射：给定目标的任一实提升 $y\in\mathbb R^2$，$\mathsf K^{-1}y$ 的模整数类就是一个原像；$\mathsf K$ 为整数矩阵保证该同态良定义。其 Haar 推前是归一化 Haar，因为满射使目标上的任意平移都可提升为原群上的平移。这里不要求 $|\det\mathsf K|=1$。

于是两个 character 的联合像服从两圆的乘积 Haar，平移同一个首中心不改变其测度。原纤维的覆盖面积满足

$$
\begin{aligned}
b_H(u;\omega)
&\le\prod_{i=1}^2\min(1,2\sqrt3\lambda_i)\\
&\le\min(1,12\lambda_1\lambda_2)
=\min(1,12p).
\end{aligned}
\tag{26.6}
$$

这只是固定 $u$ 后的空间 Haar 计算，不假设两条轨道、两个共振选择或不同阶段彼此独立。上述单 character 与满射紧群同态的 Haar 性质都是经典中间事实；这里的承重关系是原纤维中两短向量的空间投影确实独立，并且两个条带来自同一首项。

下界只需准确质量与定理 25.1。固定 $u$，每个严格实盒的面积为 $4r^2$，故即使中心重叠，仍有

$$
\int_{\mathbb T^2}V_H(u,z;\omega)\,dm_{\mathbb T^2}(z)
=4r^2N_H(u)=m\frac{N_H(u)}K.
\tag{26.7}
$$

支集外 $V_H=0$，支集内逐点不超过 $108m/p$，从而

$$
m\frac{N_H(u)}K\le\frac{108m}{p}\,b_H(u;\omega).
$$

这给出 (26.1)。再由 (25.5) 的准确分配，

$$
\int_{C_M}N_H(u)\,d\lambda_{C_M}(u)=K,
\qquad \int_Y V_H(\cdot;\omega)\,d\nu=m.
\tag{26.8}
$$

对 (26.1) 积分即得 (26.2)。所有严格窗边界仍按 (24.4) 处理；下界来自对实际计数积分，未假定任何平移窗都含格点。

用白话说，一条共振把同一批允许中心限制在一条带中；两条独立共振把它们限制在两条带的共同部分。大质量排除了两条短共振只是在空间上重复同一方向的可能。两带的共同面积按宽度乘积计，而原平均命中数与逐点重复上限又强迫覆盖至少达到同一乘积的固定比例。常数 $12$ 来自条带估计中的 Cauchy–Schwarz，$108$ 来自经典格点上界，两者均不取最优。$\square$

## 27. 联合能量、峰值与真实 floor/ceil 后果

**定理 27.1（能量与峰值的同一乘积尺度）。** 对定义 24.1 的每个阶段和方向，令

$$
T_H(\omega)=\frac{\mathcal E_H(\omega)}{m_H^2},\qquad
\zeta_H=1+\frac{\tau_H(1-\tau_H)}{K_H^2},\qquad p=p_H(\omega).
$$

则对每个 $u\in C_M$，

$$
\frac{m_H(u)^2}{\min(1,12p)}
\le e_H(u;\omega)
\le\frac{108m_H}{p}\,m_H(u).
\tag{27.1}
$$

并有

$$
\boxed{
\frac1{12p}
\le\frac{\zeta_H}{\min(1,12p)}
\le T_H(\omega)\le P_H(\omega)\le\frac{108}{p}.
}
\tag{27.2}
$$

特别地，$\zeta_H\ge1$ 保留了两个真实整数长度的零频质量，不将 $N_H(u)$ 当作 $K_H$。若取 $p<1/12$，则对每个 $u$ 都有

$$
m_{\mathbb T^2}\{z:V_H(u,z;\omega)=0\}\ge1-12p>0.
\tag{27.3}
$$

**证明。** 在固定 $u$ 的覆盖支集上使用 Cauchy–Schwarz，并使用 (26.7)，得

$$
m_H(u)^2\le b_H(u;\omega)e_H(u;\omega).
$$

定理 26.1 给出 (27.1) 的下界。定理 25.1 的逐点上界乘以 $V_H$ 再积分，给出其上界。由 (25.5)，

$$
\begin{aligned}
\int_{C_M}m_H(u)^2\,d\lambda_{C_M}(u)
&=(4r_H^2)^2\bigl((1-\tau_H)a_H^2+\tau_H(a_H+1)^2\bigr)\\
&=(4r_H^2)^2\bigl(K_H^2+\tau_H(1-\tau_H)\bigr)
=m_H^2\zeta_H.
\end{aligned}
\tag{27.4}
$$

所以对 (27.1) 积分得到 (27.2) 中能量的下界。又由 (26.8)，

$$
\mathcal E_H(\omega)
\le\left(\sup_{u,z}V_H(u,z;\omega)\right)\int_Y V_H\,d\nu
=m_H^2P_H(\omega),
$$

而 $P_H\le108/p$ 已由定理 25.1 给出。因 $\min(1,12p)\le12p$ 且 $\zeta_H\ge1$，也得到最左端的 $1/(12p)$。式 (27.3) 正是 (26.1) 上界的补集测度。

同时，在全支集上使用同一个 Cauchy–Schwarz 还给出

$$
\frac1{b_H(\omega)}\le T_H(\omega),\qquad
\frac{m_H}{12p}\le
\frac{m_H}{b_H(\omega)}\le\frac{108m_H}{p}.
\tag{27.5}
$$

中间的 $m_H/b_H$ 是在被覆盖目标上的条件平均计数。式 (27.1)–(27.5) 使用的都是同一 $V_H$，因而其能量就是原定理 21.3 在方向 $\omega$ 上的准确联合能量；在 $\omega=\alpha$ 时完全相同。这里没有把实两坐标或有限端的二阶关系拆成边缘最优值。

用白话说，覆盖缩小到乘积 $p$ 的尺度时，同样多的命中被挤到这小部分目标上，能量与最大计数便都增加到 $1/p$ 的尺度。这个结论给出的是每个目标上的上界；当 $p<1/12$ 时，每个有限端纤维中反而都有正面积的目标完全没有命中，所以不能补写一个对全部目标严格为正的计数下界。$\square$

**定理 27.2（一条与两条共振的定量区别）。** 对定义 24.1 的每个阶段和方向，恰有以下三种情形：

$$
\begin{array}{c|c|c}
\mathfrak r_H&\text{长度条件}&p_H\\ \hline
0&1\le\lambda_{1,H}&1\\
1&\lambda_{1,H}<1\le\lambda_{2,H}&\lambda_{1,H}\\
2&\lambda_{2,H}<1&\lambda_{1,H}\lambda_{2,H}
\end{array}
\tag{27.6}
$$

在秩零情形，$b_H\ge1/108$ 且 $1\le T_H\le P_H\le108$；在秩一、秩二情形，分别有

$$
\begin{aligned}
\mathfrak r_H=1:\qquad
&\frac{\lambda_{1,H}}{108}\le b_H\le\min(1,12\lambda_{1,H}),\\
&\frac1{12\lambda_{1,H}}\le T_H\le P_H\le\frac{108}{\lambda_{1,H}},\\[2mm]
\mathfrak r_H=2:\qquad
&\frac{\lambda_{1,H}\lambda_{2,H}}{108}
 \le b_H\le\min(1,12\lambda_{1,H}\lambda_{2,H}),\\
&\frac1{12\lambda_{1,H}\lambda_{2,H}}
 \le T_H\le P_H\le\frac{108}{\lambda_{1,H}\lambda_{2,H}}.
\end{aligned}
\tag{27.7}
$$

对任意无界阶段序列 $H_j\in\mathcal H_-$ 和任意方向序列 $\omega_j$，所有下述长度和量均在 $(H_j,\omega_j)$ 取值。如果 $\lambda_2\ge c>0$，令 $c'=\min(1,c)$、$s_1=\min(1,\lambda_1)$，则

$$
\begin{gathered}
\frac{c's_1}{108}\le b\le\min(1,12s_1),\\
\frac1{12s_1}\le T\le P\le\frac{108}{c's_1}.
\end{gathered}
\tag{27.8}
$$

如果 $\lambda_2\to0$，则

$$
\frac b{\lambda_1}\longrightarrow0,\qquad
\lambda_1T\longrightarrow\infty,\qquad
\lambda_1P\longrightarrow\infty.
\tag{27.9}
$$

对任意这样的序列，还有

$$
\begin{aligned}
b\to0
&\ \Longleftrightarrow\ p\to0
\ \Longleftrightarrow\ \lambda_1\to0\\
&\ \Longleftrightarrow\ T\to\infty
\ \Longleftrightarrow\ P\to\infty.
\end{aligned}
\tag{27.10}
$$

**证明。** 定理 25.1 给出 $\lambda_3\ge1$，而严格逐次极小定义使 $\mathfrak r_H$ 等于严格小于 $1$ 的极小值个数，故 (27.6) 穷尽全部情形。将其代入 (26.2)、(27.2)，得到 (27.7) 以及秩零的界；秩零时 $T_H\ge\zeta_H\ge1$。

若 $\lambda_2\ge c$，则

$$
c's_1\le p=s_1\min(1,\lambda_2)\le s_1,
$$

代入相同双边界得 (27.8)。若 $\lambda_2\to0$，尾部为秩二，(27.7) 给出

$$
0\le\frac b{\lambda_1}\le12\lambda_2\to0,\qquad
\lambda_1T\ge\frac1{12\lambda_2}\to\infty,
\qquad P\ge T,
$$

即 (27.9)。最后，由极小值排序有

$$
s_1^2\le p\le s_1.
$$

这证明 $p\to0$ 与 $\lambda_1\to0$ 等价；其余等价性由 (26.2)、(27.2) 的两侧常数直接得到。

这些逐阶段结论对每个方向成立，因而也可固定 $\omega_j=\alpha$，不需方向随机性。但它们不决定原实际 $p_H(\alpha)$ 的趋向。若在一个无界原好阶段子族上另有 $p_H(\alpha)\ge\varepsilon>0$，则 $\lambda_{1,H}(\alpha)\ge p_H(\alpha)\ge\varepsilon$，原定理 21.5 已给出 $\nu(R(\alpha))=1$ 的充分结论。若只知 $p_H(\alpha)\to0$，则这里证明的是阶段覆盖趋零和能量比发散；阶段子事件的 limsup 包含于完整 $R(\alpha)$，不能从小集合的零测反推大集合零测。一般比较方向也不由阶段结论获得跨阶段独立性。

用白话说，最短长度仍能检测是否发生塌缩，但不能独自量出塌缩的速度。第二条长度有正下界时，一条短共振已经给出正确尺度；第二条也趋零时，覆盖还要再乘这第二个小量，重复命中的能量也要再除以它。这是原阶段中一条带与两条交带的区别。$\square$

## 28. 原有限纤维中二阶乘积尺度的精确实例

**定理 28.1（双共振乘积不能统一换成最短长度）。** 在定义 24.1 的全部原有限端和原好阶段上，仅取比较实方向 $\omega=(0,0)$。则

$$
\begin{gathered}
\lambda_{1,H}=\lambda_{2,H}=r_H,\qquad
\lambda_{3,H}=K_H,\qquad
\mathfrak r_H=2,\qquad p_H=r_H^2,\\
V_H(u,z;0)=N_H(u)\,
 \mathbf1_{\{\|z_1\|_{\mathbb T}<r_H,\ \|z_2\|_{\mathbb T}<r_H\}},\\
b_H(u;0)=b_H(0)=4r_H^2=4p_H,\\
T_H(0)=\frac{\zeta_H}{4r_H^2},\qquad
P_H(0)=\frac{\lceil K_H\rceil}{4K_Hr_H^2}.
\end{gathered}
\tag{28.1}
$$

因而沿全部充分大的原好阶段，

$$
\frac{b_H(0)}{\lambda_{1,H}(0)}\to0,\qquad
T_H(0)p_H(0)\to\frac14,\qquad
P_H(0)p_H(0)\to\frac14.
\tag{28.2}
$$

特别地，不存在一个对所有比较方向、所有充分大原好阶段都成立的正统一常数 $c$，使 $b_H(\omega)\ge c\min(1,\lambda_{1,H}(\omega))$；也不存在此范围内统一的 $T_H$ 或 $P_H$ 的 $C/\min(1,\lambda_{1,H})$ 上界。

**证明。** 此时

$$
L_H(0)=K_H\mathbb Z\times r_H\mathbb Z^2.
$$

因 $r_H<1/4$、$K_H>16$，两个独立空间基向量的长度为 $r_H$，而第三个独立向量必须有非零时间坐标，长度至少为 $K_H$；各界均由坐标基达到。这给出全部极小值及共振秩。

所有允许整数的实中心都为 $0$，但有限端的允许整数仍准确保留为 (25.6)，故计数就是 (28.1) 的指标函数乘 $N_H(u)$。所有 $u$ 均有 $N_H(u)>0$，所以每个覆盖截面恰为同一严格开盒，面积 $4r_H^2$。由 (25.5)，

$$
\mathcal E_H(0)=4r_H^2
 \bigl(K_H^2+\tau_H(1-\tau_H)\bigr).
$$

除以 $m_H^2=(4K_Hr_H^2)^2$ 即得 $T_H(0)$。当 $\tau_H>0$ 时，确有 $s_H\ge1$ 个有限余类达到 $N_H=a_H+1=\lceil K_H\rceil$；当 $\tau_H=0$ 时，每个余类都达到 $N_H=K_H=\lceil K_H\rceil$。在实开盒内取 $z$，遂得所列峰值公式。

原好阶段有 $r_H\to0$、$K_H\to\infty$，且

$$
0\le\zeta_H-1\le\frac1{4K_H^2},\qquad
1\le\frac{\lceil K_H\rceil}{K_H}<1+\frac1{K_H}.
$$

这给出 (28.2)。进一步，$b_H/\lambda_{1,H}=4r_H\to0$，而

$$
T_H\lambda_{1,H}=\frac{\zeta_H}{4r_H}\to\infty,
\qquad
P_H\lambda_{1,H}=\frac{\lceil K_H\rceil}{4K_Hr_H}\to\infty,
$$

故所述统一替代界均被此同一方向排除。

这个实例始终保留原 $Q_H,J_H,K_H$、全部有限地方与其同源目标，只用于说明比较族上的乘积尺度确实必要；它没有将零实方向解释成原指定 CM 方向。定理 25.1 所用的 Freyer–Lucas 计数和 Minkowski 第二定理，以及对偶互反、整数楔积、Haar 推前与二阶矩不等式，都是经典中间工具。本卷的综合结论是它们在原临界阶段、同一有限纤维和同一首中心上的双边覆盖、联合能量及计数尺度，不主张一般数几何定理的原创优先权。

用白话说，两条实轨迹完全重合在一个中心时，允许整数再多也只反复覆盖同一小方块。这个方块的面积是两条短宽度的乘积；所有真实 floor/ceil 计数都保留在重复次数里。大质量原好阶段上的定理没有涵盖任意完整块中的 $K<1$ 片段或 $\Delta<1$ 片段，也没有删掉那些片段中的原事件。完整原事件序列与实际 CM 方向的判定仍须各自的跨阶段或算术关系。$\square$

## 追加锚（本行以下为增补区）
