# AURIC FIB 实际配对能量与交叠投影

本文的全部数学陈述与证明均为可错的 **UNEXECUTED conditional symbolic mathematics（未经执行的条件符号数学）**。前提是下列明确指定的实际字模型、同长度注入性、分离界、精确归一化的正谱隙，以及注明出处的恢复蕴涵。本文不提供程序计算、实验、Lean kernel 核验、外部来源认证或全局原创性认证。

相对于 *AURIC FIB actual-word purity and restricted arithmetic*（下称母文）§§45–58，本文的实质增量是：在同一个实际前向算子的移动投影乘积中，利用相邻三投影块共享的端点投影，得到更强的剩余字块收缩、有限配对能量界及完整指数包络的严格改进。*AURIC FIB actual-word half-length structure and middle-letter obstruction*（下称半长伴篇）提供的实际尾字与 Gram 结构只用于明确算术接口。原始全尺度目标仍为 **OPEN**。

## 1. 实际字、相位、测度与恢复模型

在母文的正交基中，固定

$$
A_g=g_0=\frac14\begin{pmatrix}
\sqrt3-i&3+i\sqrt3\\
3-i\sqrt3&-\sqrt3-i
\end{pmatrix},\qquad
J=\operatorname{diag}(-1,1),\qquad g_1=A_gJ,
\qquad\lambda=e^{i\pi/6}.
\tag{1.1}
$$

每次获取的标签是独立公平比特。按时间排列的历史 $h=(h_1,\ldots,h_n)$ 对应

$$
G_h=g_{h_n}\cdots g_{h_1},\qquad F_h=\lambda^{-n}G_h.
\tag{1.2}
$$

空历史对应恒等矩阵。每条历史的概率为 $2^{-n}$，历史及其重数始终保留。令 $\mathsf H,\mathsf G$ 为独立的公平长度 $n$ 历史，定义闭事件的有序配对概率

$$
E_n(r)=\Pr(\|F_{\mathsf H}-F_{\mathsf G}\|_F\le r)
=4^{-n}\sum_{h,g\in\{0,1\}^n}
\mathbf1_{\{\|F_h-F_g\|_F\le r\}},\qquad r\ge0.
\tag{1.3}
$$

这里 $\|\cdot\|_F$ 是未归一化的 Frobenius 范数。对角项也在和式中。母文的实际同长度注入性作为前提，故

$$
E_0(r)=1\ (r\ge0),\qquad E_n(0)=2^{-n}.
\tag{1.4}
$$

同一长度的 $\lambda^{-n}$ 是共同单位标量，因此

$$
\|F_h-F_g\|_F=\|G_h-G_g\|_F.
\tag{1.5}
$$

这一步不允许逐字去掉不同相位。若 $p(h)=\sum_kh_k\pmod2$，则 $\det G_h=(-1)^{n+p(h)}$，且 $\det F_h=\omega^n(-1)^{p(h)}$，其中 $\omega=(-1+i\sqrt3)/2$。两个不同奇偶类在同一长度属于不同的行列式分量，距离恰为 $2$。

恢复陈述沿用母文 Definition 51.1 的原模型：$H=\mathbb C^5$，固定原来的嵌入 $\iota:M_3\to\mathcal B(H)$，在原三维正交基 $S_0$ 中

$$
Q_h=V_{h_n}\cdots V_{h_1}
=\lambda^n S_0(1\oplus F_h)S_0^\dagger.
\tag{1.6}
$$

特别地，单步的 $V_j$ 由 $\lambda S_0(1\oplus\lambda^{-1}g_j)S_0^\dagger$ 给出。有关 $\iota$ 的完整物理实现及母文链接卷中的仪器细节，均不在本文另作认证；下文只条件使用母文明确给出的恢复必要性与因果上界。数学载体不是附加的物理寄存器。

一个允许的完整因果随机控制器 $\mathcal C$ 具有独立的有限或 standard-Borel 共享种子 $S$，终端记录核为 $p_s(z\mid h)$。初始随机状态和新鲜丢弃的随机性均计入该实际核；所有持续存在的随机或历史相关变量均计入所数记录。宽度 $W$ 是完整因果峰值宽度，在同一个种子满测集上可把各层状态集补齐到 $W$。只有终端的一次任意 full-$H$ CPTP 解码 $D^H_{z,s}$；没有中间量子纠正、后选择或保留环境。成功的含义是

$$
\left\|\mathbb E_S2^{-n}\sum_{h,z}p_S(z\mid h)
D^H_{z,S}\circ\iota\circ\operatorname{Ad}_{Q_h}-\iota
\right\|_\diamond\le\varepsilon.
\tag{1.7}
$$

diamond 范数不减半，量化所有有限的未受操作参考系统，解码器不可访问参考；要求是平均通道成功，并非逐种子或逐历史成功。$W_n(\varepsilon)$ 表示该原模型中最小可行峰值宽度。本文不增加读出、重置、后选择、精度或资源权限，也不从解析密度构造新的控制器。

## 2. 紧群、精确谱隙与两个均值子空间

令

$$
K=\{x\in U(2):\det x\in\{1,-1\}\}
=SU(2)\sqcup SU(2)J.
$$

$G_h$ 属于 $K$，而 $F_h$ 一般不在 $K$；配对距离只通过共同相位等式 (1.5) 转移。归一化 Haar 测度 $m_K$ 给每个分量质量 $1/2$，距离为 $d(x,y)=\|x-y\|_F$，左右不变。对有限测度 $\eta$ 定义

$$
T_\eta f(x)=\int_K f(g^{-1}x)\,d\eta(g),\qquad
T_\alpha T_\beta=T_{\alpha*\beta},\qquad
\check\eta(E)=\eta(E^{-1}).
\tag{2.1}
$$

写 $T_g=T_{\delta_g}$。单步实际律及算子是

$$
\mu=\tfrac12(\delta_{A_g}+\delta_{A_gJ}),\qquad
U=T_{A_g},\qquad P=T_\mu=UQ_0.
\tag{2.2}
$$

因为追加最后标签满足 $G_{hj}=g_jG_h$，实际长度 $n$ 律正是 $\mu^{*n}$，不是 Haar 律。$P$ 是酉算子的平均，范数至多一，但不假设正规或单步奇异值谱隙。

对整数 $j\ge0$ 置

$$
J_j=A_g^{-j}JA_g^j,\qquad S_j=T_{J_j},\qquad
Q_j=\tfrac12(I+S_j).
\tag{2.3}
$$

$J_j^2=I$，故 $S_j$ 是自伴酉算子，$Q_j$ 是正交投影，且

$$
Q_j=U^{-j}Q_0U^j.
\tag{2.4}
$$

指定的谱隙只针对下列四原子概率测度：

$$
C_1=J_0J_1,\qquad C_2=J_1J_2,\qquad
\sigma=\tfrac14(\delta_{C_1}+\delta_{C_1^{-1}}
+\delta_{C_2}+\delta_{C_2^{-1}}).
\tag{2.5}
$$

在完整单位向量球面 $S^3\subset\mathbb C^2$ 上取归一化均匀测度，并令 $\mathsf U_gv(z)=v(g^{-1}z)$。全文的 $\gamma$ 精确地是母文 (53.6) 的常数

$$
\gamma=\gamma_{22}
=\min\left\{1,\inf_{\substack{0\ne v\in L^2(S^3;\mathbb C)\\v\perp1}}
\frac{\langle v,(I-\mathsf U_\sigma)v\rangle}{\|v\|_2^2}\right\},
\quad
\mathsf U_\sigma=\tfrac14\sum_{c\in(C_1,C_1^{-1},C_2,C_2^{-1})}\mathsf U_c.
\tag{2.6}
$$

假定母文提供的 $0<\gamma\le1$。不代入数值，不把它换成母文所区分的 $R_1,R_2$ 谱隙，不限制为实函数、单个特征空间或球面商空间。母文提供的来源是其精确生成元的代数性与稠密性，以及所引用的 Bourgain–Gamburd, *A spectral gap theorem in SU(d)*, JEMS **14**(5), 1455–1511，publisher final，Theorem 1 与 density footnote（p. 1455）、归一化 (0.1)（p. 1457），DOI 10.4171/JEMS/337。其 $d=2,k=2$ 的 Hecke 和除以四才是 (2.5)。本文只使用该已指定的供应前提，不打开或独立核实其外部引用。

令 $\chi(x)=\det x$。在整个复 Hilbert 空间中有正交分解

$$
L^2(K;\mathbb C)=\operatorname{span}\{1\}\oplus
\operatorname{span}\{\chi\}\oplus\mathcal H_c,
\tag{2.7}
$$

其中 $\mathcal H_c$ 是分别在两个行列式分量上积分为零的复函数空间。平移只排列分量并保 Haar 测度，所以 $U,S_j,Q_j$ 均保 $\mathcal H_c$，也保全局零均值空间。$\det J_j=-1$，因而

$$
S_j\chi=-\chi,\qquad Q_j\chi=0.
\tag{2.8}
$$

故每个全局零均值 $f=a\chi+f_c$ 都满足 $Q_0f=Q_0f_c\in\mathcal H_c$。常数模式满足 $P1=1$，不应对它宣称衰减；纯行列式模式在一次 $Q_0$ 后为零。

为把 (2.6) 转到 $\mathcal H_c$，在任一分量写 $x=u$ 或 $uJ$，$u\in SU(2)$。映射

$$
(z_1,z_2)\longmapsto
\begin{pmatrix}z_1&-\overline z_2\\z_2&\overline z_1\end{pmatrix}
\tag{2.9}
$$

把完整 $S^3$ 的均匀测度和左作用对应到 $SU(2)$ 的 Haar 测度和左正则作用。分别对两个零均值限制应用 (2.6)，再加上各自 $1/2$ 的权重，得到母文 (54.4) 的确切全复空间结论

$$
\langle v,(I-T_\sigma)v\rangle\ge\gamma\|v\|_2^2
\qquad(v\in\mathcal H_c).
\tag{2.10}
$$

这是对所有这些 Rayleigh 商的下界，不是每个向量的特征值等式。

## 3. 三个正交投影的范数引理

**引理 P1。** 设 $E_0,E_1,E_2$ 是任意复 Hilbert 空间的正交投影，$0<\gamma\le1$。若对每个 $v\in\operatorname{ran}E_1$ 都有

$$
\|(I-E_0)v\|^2+\|(I-E_2)v\|^2\ge\gamma\|v\|^2,
\tag{3.1}
$$

则

$$
\|E_2E_1E_0\|\le\kappa,
\qquad\kappa=1-\gamma/2.
\tag{3.2}
$$

**证明。** 固定 $f$，令 $u=E_0f$。$u=0$ 时结论直接成立。否则定义

$$
S=\|u\|^2>0,\quad v=E_1u,\quad a=u-v,\quad b=v-E_2v,
\quad t=\|a\|^2/S,\quad z=\|b\|^2/S.
$$

这里 $u=v+a$，且 $v\perp a$、$E_2v\perp b$。因此

$$
\langle u,a\rangle=\|a\|^2,\qquad
\|v\|^2/S=1-t,\qquad
\|E_2v\|^2/S=1-t-z.
\tag{3.3}
$$

由 $E_0u=u$ 及 Cauchy–Schwarz，

$$
\|E_0a\|^2\ge\frac{|\langle u,a\rangle|^2}{S}=t^2S.
$$

同时 $0=(I-E_0)u=(I-E_0)v+(I-E_0)a$。在这里只需使用正确的平方范数等式

$$
\|(I-E_0)v\|^2=\|(I-E_0)a\|^2
=\|a\|^2-\|E_0a\|^2\le S(t-t^2).
\tag{3.4}
$$

由于 $v\in\operatorname{ran}E_1$，(3.1) 给出 $\gamma(1-t)\le t-t^2+z$。于是

$$
\begin{aligned}
\|E_2v\|^2/S
&=1-t-z\\
&\le1-\gamma+\gamma t-t^2\\
&=(1-\gamma/2)^2-(t-\gamma/2)^2
\le\kappa^2.
\end{aligned}
$$

再用 $\|u\|\le\|f\|$ 及 $\kappa\ge0$，取平方根和上确界即得 (3.2)。未除以 $\|v\|$、$\|a\|$ 或 $\|b\|$；$v=0$、各投影核及零范围均包含在内。无限维、复标量和 $\gamma=1$ 的端点也均适用。$\square$

此引理使用标准的正交投影几何；其本身不承担全局新意声明。

## 4. 实际时间顺序中的交叠投影收缩

固定

$$
\kappa=1-\gamma/2,\qquad \widehat\xi=-\ln\kappa,\qquad h_*=\ln2,
\qquad R_0=1,
\qquad R_L=\kappa^{2\lfloor(L-1)/2\rfloor}\quad(L\ge1).
\tag{4.1}
$$

由 $0<\gamma\le1$ 得 $1/2\le\kappa<1$ 及 $0<\widehat\xi\le h_*$。

**定理 P2。** 对每个整数 $L\ge0$ 及每个全局零均值的复函数 $f\in L^2(K,m_K;\mathbb C)$，

$$
\|P^Lf\|_2^2\le R_L\|f\|_2^2.
\tag{4.2}
$$

特别地 $R_0=R_1=R_2=1$，$R_3=\kappa^2$。此外对所有 $L\ge0$，

$$
e^{-\widehat\xi L}\le R_L\le\kappa^{-2}e^{-\widehat\xi L}.
\tag{4.3}
$$

**证明。** 由 $P=UQ_0$ 与 (2.4)，逐次把 $U$ 移到左边，或对 $L$ 归纳，得实际前向算子的精确恒等式

$$
P^L=U^LQ_{L-1}\cdots Q_1Q_0\qquad(L\ge1).
\tag{4.4}
$$

无需交换任何两个投影。这个恒等式也不等同于将 $(P^L)^*P^L$ 换成 $(P^*P)^L$。

先在不变复空间 $\mathcal H_c$ 上取 $Q_1v=v$，即 $S_1v=v$。对称四原子测度的 Dirichlet 恒等式给出

$$
\langle v,(I-T_\sigma)v\rangle
=\tfrac14\bigl(\|v-T_{C_1}v\|_2^2+\|v-T_{C_2}v\|_2^2\bigr).
\tag{4.5}
$$

具体地，任意酉 $T_c$ 的平方位移展开为 $2\|v\|^2-2\operatorname{Re}\langle v,T_cv\rangle$，逆元的位移范数相同；四项各带 $1/4$ 再乘 Dirichlet 公式的 $1/2$，得到 (4.5)。$T_{C_1}=S_0S_1$，故

$$
\|v-T_{C_1}v\|_2=\|v-S_0v\|_2=2\|(I-Q_0)v\|_2.
$$

又 $T_{C_2}=S_1S_2$，左乘酉 $S_1$ 并用 $S_1v=v$ 可得

$$
\|v-T_{C_2}v\|_2=\|S_1v-S_2v\|_2
=\|v-S_2v\|_2=2\|(I-Q_2)v\|_2.
$$

因此 (2.10) 恰好变成

$$
\|(I-Q_0)v\|_2^2+\|(I-Q_2)v\|_2^2\ge\gamma\|v\|_2^2.
$$

引理 P1 应用于 $\mathcal H_c$ 上三个投影，给出 $\|Q_2Q_1Q_0\|_{\mathcal H_c\to\mathcal H_c}\le\kappa$。对任意 $j\ge0$，

$$
W_j=Q_{j+2}Q_{j+1}Q_j
=U^{-j}(Q_2Q_1Q_0)U^j,
\qquad\|W_j\|_{\mathcal H_c\to\mathcal H_c}\le\kappa.
\tag{4.6}
$$

这是同一谱隙的酉共轭应用。

全局零均值的 $f=a\chi+f_c$ 先经 $Q_0$，由 (2.8) 得 $Q_0f\in\mathcal H_c$ 且 $\|Q_0f\|\le\|f\|$。当 $L=2k+1$、$k\ge1$ 时，投影幂等性给出

$$
Q_{2k}\cdots Q_0 f
=W_{2k-2}W_{2k-4}\cdots W_0Q_0f.
\tag{4.7}
$$

右边每两个相邻三投影块共享一个端点 $Q_{2j}$；将该端点的相邻两次出现用 $Q_{2j}^2=Q_{2j}$ 合并，恰好得到左边的原顺序乘积。末端的重复 $Q_0$ 也同样合并。故其范数至多 $\kappa^k\|Q_0f\|$。$k=0$ 即 $L=1$ 时仅用 $Q_0$ 的非扩张性。$L=2k+2$ 时，在对应奇长度乘积左侧再加一个投影 $Q_{2k+1}$，范数不增。最后 $U^L$ 酉，平方后正是 (4.2)。$L=0$ 是恒等算子，须单独取 $R_0=1$。纯行列式模式在 $L\ge1$ 已被杀去，$L=0$ 则仍原样保留。

当 $L\ge1$ 时，$d=2\lfloor(L-1)/2\rfloor$ 在奇长度为 $L-1$、偶长度为 $L-2$，故 $L-2\le d\le L$。因 $0<\kappa<1$，有 $\kappa^L\le\kappa^d\le\kappa^{L-2}$，即 (4.3)。$L=0$ 时 (4.3) 直接成立。$\square$

这项改进使用的是同一实际联合实现上的投影，而不是分别可达的两端最优值。$k$ 次谱隙估计只需 $2k+1$ 个实际字母，原因是共享端点的幂等性。它无需新的混合前提、单步奇异值谱隙、整壳分布或 Haar 字律。

母文旧估计的参数为

$$
q=1-\gamma/16,\qquad \xi=-\tfrac13\ln q.
\tag{4.8}
$$

其精确指数比较也保留为

$$
e^{-\xi L}\le q^{\lfloor L/3\rfloor}\le q^{-1}e^{-\xi L}
\qquad(L\ge0).
\tag{4.9}
$$

这是由 $L/3-1\le\lfloor L/3\rfloor\le L/3$ 及 $0<q<1$ 得到的。仅把母文的该估计分配给连续两个剩余块 $L_1+L_2=L$，其指数仍为 $\xi L+O(1)$，因为两个 floor 的和至多 $\lfloor L/3\rfloor$，相差至多一。因此这种单纯分块重用不会改善旧的领先指数；这不是对所有双侧方法的不可能性结论。

## 5. 实际重叠、球体积与有限配对能量

对 $s>0$ 设

$$
B_s(x)=\{y\in K:d(x,y)\le s\},\qquad
V(s)=m_K(B_s(I)),\qquad b_s=\mathbf1_{B_s(I)}/V(s).
$$

定义

$$
\Delta_0=+\infty,\qquad
\Delta_m=\min_{h\ne g\in\{0,1\}^m}\|G_h-G_g\|_F
\quad(m\ge1).
\tag{5.1}
$$

母文 (53.4) 的实际同长度分离供应为 $\Delta_m\ge2^{-m}$；母文 Proposition 46.2 的更强界不影响这里的指数。每个 $\Delta_m$ 都是在所有实际历史上取的最小值，不是对任意范数壳点的断言。

**定理 P3。** 对所有整数 $n\ge0$、$0\le m\le n$ 以及满足

$$
0<r\le1/4,\qquad 4r<\Delta_m
\tag{5.2}
$$

的半径，都有

$$
\begin{aligned}
E_n(r)
&\le\frac{V(2r)^2}{V(r)}
\left[1+R_{n-m}\left(\frac{2^{-m}}{V(2r)}-1\right)\right]\\
&\le16\bigl(r^3+2^{-m}R_{n-m}\bigr).
\end{aligned}
\tag{5.3}
$$

所有球及配对事件都是闭的；初始球分离必须保持 (5.2) 的严格不等式。

**证明。** 对每个 $j\ge0$，用同一个实际前向律定义解析密度

$$
f_{j,r}=P^jb_{2r}
=2^{-j}\sum_{h\in\{0,1\}^j}
\frac{\mathbf1_{B_{2r}(G_h)}}{V(2r)}.
\tag{5.4}
$$

其质量为一。若长度 $m$ 两个不同中心的闭 $2r$ 球相交，三角不等式会给出中心距离至多 $4r$，与 (5.2) 矛盾。所以母文 (55.3) 的初始能量是精确等式

$$
\|f_{m,r}\|_2^2=\frac{2^{-m}}{V(2r)},\qquad
\|f_{m,r}-1\|_2^2=\frac{2^{-m}}{V(2r)}-1\ge0.
\tag{5.5}
$$

$m=0$ 只有一个球，等式仍成立。实际半群关系及 $P1=1$ 给出

$$
f_{n,r}-1=P^{n-m}(f_{m,r}-1).
$$

括号内是全局零均值函数，不要求它一开始就在 $\mathcal H_c$。因此定理 P2 适用；若 $n=m$ 则只用恒等算子。由常数与零均值部分正交，

$$
\|f_{n,r}\|_2^2\le1+R_{n-m}
\left(\frac{2^{-m}}{V(2r)}-1\right).
\tag{5.6}
$$

长度 $m$ 的初始块与剩余 $n-m$ 个字母始终来自同一个公平字卷积律。

将 (5.4) 的平方完全展开，保留每一个有序历史对，得到母文 (55.5) 的精确重叠恒等式

$$
\|f_{n,r}\|_2^2
=4^{-n}\sum_{h,g}
\frac{m_K(B_{2r}(G_h)\cap B_{2r}(G_g))}{V(2r)^2}.
\tag{5.7}
$$

若中心距离 $d(G_h,G_g)\le r$，则闭球 $B_r(G_h)$ 包含在这两个 $2r$ 球的交集中，交集质量至少为 $V(r)>0$。结合 (1.5)，

$$
E_n(r)\le\frac{V(2r)^2}{V(r)}\|f_{n,r}\|_2^2.
\tag{5.8}
$$

将 (5.6) 代入，得 (5.3) 第一行。没有合并历史、丢掉对角、选取不同的初末分布或移除奇偶类。

为完整说明所用常数，对 $\det x=-1$ 的酉矩阵，其特征值为 $z,-\bar z$，故 $\operatorname{Re}\operatorname{Tr}x=0$，$\|I-x\|_F^2=4$。左右不变性说明异分量距离恒为 $2$。当 $0<s<2$，$I$ 附近球仅在 $SU(2)$ 中。写其特征值为 $e^{\pm i\theta}$，弦距离 $t=2\sqrt2\sin(\theta/2)$，归一化 $SU(2)$ 径向测度为 $(2/\pi)\sin^2\theta\,d\theta$。加上分量权重 $1/2$ 并换元，得

$$
V(s)=\frac1{2\sqrt2\pi}\int_0^s t^2\sqrt{1-t^2/8}\,dt
\qquad(0<s<2).
\tag{5.9}
$$

在 $0<s\le1/2$，平方根介于 $1/2$ 与一之间，因此

$$
\frac{s^3}{12\sqrt2\pi}\le V(s)\le\frac{s^3}{6\sqrt2\pi}.
\tag{5.10}
$$

于是 $0<r\le1/4$ 时，$V(2r)/V(r)\le16$，且 $V(2r)\le[8/(6\sqrt2\pi)]r^3<r^3$。令 $R=R_{n-m}$，把 (5.3) 第一行改写为

$$
\frac{V(2r)}{V(r)}\bigl[V(2r)(1-R)+2^{-m}R\bigr].
$$

$0<R\le1$ 使两项非负，上述体积比较立即给出第二行。$\square$

定理包括 $m=0$、$n=m$、$n=m=0$ 及 $n-m\in\{0,1,2\}$；后三种剩余长度不被赋予虚假的严格收缩。有限界不宣称 $r=0$，其精确零半径结果另由 (1.4) 给出。所有 Haar 积分只测解析球交集和 Hilbert 范数；实际有限律仍是每条历史 $2^{-n}$，平滑不是中间仪器操作，也不占用或授权额外存储。

## 6. 安全整数块与整个旧指数包络的比较

**定理 P4。** 对每个固定 $a>0$ 及每个正半径序列 $r_n=\exp(-an+o(n))$，特别是对每个固定 $a,c>0$ 的 $r_n=ce^{-an}$，都有

$$
E_n(r_n)\le\exp(-\widehat b(a)n+o(n)),\qquad
\widehat b(a)=
\begin{cases}
\min\{3a,\ a+\widehat\xi(1-a/h_*)\},&0<a<h_*,\\
h_*,&a\ge h_*.
\end{cases}
\tag{6.1}
$$

母文 Theorem 56.1 的整个旧包络为

$$
b(a)=
\begin{cases}
\min\{3a,\ a+\xi(1-a/h_*)\},&0<a<h_*,\\
h_*,&a\ge h_*.
\end{cases}
\tag{6.2}
$$

定义两个匹配阈值

$$
a_{\rm old}=\frac{\xi}{2+\xi/h_*},\qquad
\widehat a=\frac{\widehat\xi}{2+\widehat\xi/h_*}.
\tag{6.3}
$$

则 $\widehat\xi>3\xi>\xi>0$，$\widehat a>a_{\rm old}$，且 $\widehat a\le h_*/3$。精确的全包络比较是

$$
\begin{aligned}
\widehat b(a)&=b(a)&&\text{当 }0<a\le a_{\rm old}\text{ 或 }a\ge h_*,\\
\widehat b(a)&>b(a)&&\text{当 }a_{\rm old}<a<h_*.
\end{aligned}
\tag{6.4}
$$

若 $0<\gamma<1$，新包络与目标指数 $t(a)=\min\{3a,h_*\}$ 在 $0<a\le\widehat a$ 及 $a\ge h_*$ 匹配，在 $\widehat a<a<h_*$ 严格低于 $t(a)$。若 $\gamma=1$，则新包络在每个 $a>0$ 都与 $t(a)$ 相等；这只是一项条件蕴涵，供应前提没有给出 $\gamma=1$。

**证明。** 当 $0<r\le1/64$，取母文的安全整数

$$
m(n,r)=\min\left\{n,\left\lfloor\frac{\ln(1/(8r))}{h_*}\right\rfloor\right\}.
\tag{6.5}
$$

括号中的 floor 至少为三，故 $0\le m\le n$。若 $m\ge1$，则 $8r\le2^{-m}\le\Delta_m$，从而 $4r<\Delta_m$；$m=0$ 用 $\Delta_0=+\infty$。所以 P3 的全部条件成立。

对所述任意正序列，半径条件最终成立，且

$$
\frac{m(n,r_n)}n\longrightarrow\theta=\min\{a/h_*,1\}.
$$

由 (4.3) 控制所有剩余长度的 floor，包括零长度，

$$
\ln\bigl(2^{-m}R_{n-m}\bigr)
=-h_*m-\widehat\xi(n-m)+O(1)
=-[h_*\theta+\widehat\xi(1-\theta)]n+o(n).
\tag{6.6}
$$

P3 中第一项 $r_n^3$ 的指数为 $3a$，两项和的指数取较小者，得到 (6.1)。固定 $c$ 时 (6.6) 的余项是 $O(1)$，一般次线性半径扰动则为 $o(n)$。$a=h_*$ 时可能只有 $n-m=o(n)$，未必最终等于零，但仍得到指数 $h_*$。

因为 $\kappa=1-\gamma/2<q=1-\gamma/16<1$，

$$
\widehat\xi=-\ln\kappa>-\ln q=3\xi>\xi.
$$

又已证 $\widehat\xi\le h_*$；$\gamma<1$ 时严格小于 $h_*$。函数 $x\mapsto x/(2+x/h_*)$ 在 $x>0$ 严格递增：对 $y>x$ 通分，正分子的差恰为 $2(y-x)$。所以 (6.3) 的阈值严格增加，且 $\widehat a\le h_*/3$，后一个等号恰对应 $\gamma=1$。

对 $0<a<h_*$ 写 $\ell_x(a)=a+x(1-a/h_*)$。旧包络是 $\min\{3a,\ell_\xi(a)\}$，新包络是 $\min\{3a,\ell_{\widehat\xi}(a)\}$。旧的两支在 $a_{\rm old}$ 相交。在 $0<a\le a_{\rm old}$，有 $3a\le\ell_\xi(a)<\ell_{\widehat\xi}(a)$，故两个包络都为 $3a$，包括旧交点。在 $a_{\rm old}<a<h_*$，旧包络为 $\ell_\xi(a)$，而 $3a$ 和 $\ell_{\widehat\xi}(a)$ 都严格超过它，故新包络的最小值也严格超过它。$a\ge h_*$ 时二者均为 $h_*$。这证明对整个旧最小值包络的 (6.4)，并非只比较某个单独供应界。

新两支在 $\widehat a$ 相交。若 $\gamma<1$，则 $\widehat\xi<h_*$、$\widehat a<h_*/3$，且 $a<h_*$ 时 $\ell_{\widehat\xi}(a)<h_*$。所以在 $\widehat a<a<h_*$，新包络同时严格小于 $3a$ 和 $h_*$；在其余已述范围则与 $t(a)$ 相等。若 $\gamma=1$，$\widehat\xi=h_*$，$\ell_{\widehat\xi}(a)=h_*$，于是每个 $a>0$ 均匹配。$\square$

因此旧匹配范围 $0<a\le a_{\rm old}$ 被严格扩展到 $0<a\le\widehat a$，旧的整个未匹配区间内都有严格指数收益。不过当 $\gamma<1$，这仍只是把缺口缩到 $\widehat a<a<h_*$；较弱上界未达到目标，不能据此声称实际目标不成立。

## 7. 同一个控制器与记录上的条件恢复率

为精确说明所使用的母文 Theorem 51.2，固定第 1 节的同一个 $\mathcal C$，定义

$$
\begin{aligned}
m_s(z)&=2^{-n}\sum_h p_s(z\mid h),\\
\overline F_{s,z}&=\frac{2^{-n}\sum_h p_s(z\mid h)F_h}{m_s(z)}
\quad(m_s(z)>0),\\
D_s&=2^{-n}\sum_{h,z}p_s(z\mid h)\|F_h-\overline F_{s,z}\|_F^2,
\qquad D(\mathcal C)=\mathbb E_SD_S.
\end{aligned}
\tag{7.1}
$$

零质量单元的中心置零，贡献也为零。母文的同控制器碰撞逆定理恰为

$$
W E_n(2t)\ge\left(1-\frac{D(\mathcal C)}{t^2}\right)_+^2
\quad(t>0),
\tag{7.2}
$$

且对满足 (1.7) 的控制器，在 $0<\varepsilon<1/4$ 时

$$
D(\mathcal C)\le\frac92\varepsilon,\qquad
W\ge\frac1{4E_n(6\sqrt\varepsilon)},\qquad
W_n(\varepsilon)\ge\frac1{4E_n(6\sqrt\varepsilon)}.
\tag{7.3}
$$

这些是供应的恢复前提，不是由 P2 自行推出的量子操作权限。其同一性可直接见于母文证明：在同一个正质量记录单元，从实际后验独立抽取两条历史，若 $z_{hg}=\operatorname{Tr}(F_g^\dagger F_h)$ 及 $\ell(h,g)=1-|\operatorname{Tr}(Q_g^\dagger Q_h)|^2/9$，则

$$
9\ell(h,g)-\|F_h-F_g\|_F^2=4-|z_{hg}|^2\ge0.
$$

同一后验下的平均平方距离等于两倍方差。母文的纯度必要性于是给出 $2D(\mathcal C)\le9\bar v_n(\mathcal C)\le9\varepsilon$。此纯度必要性以平均通道、原 full-$H$ 解码器的 CPTP 压缩及不可访问参考的纠缠态检验为条件；没有改变控制器或其记录。

碰撞部分也无需选择种子。对固定 $s$，令 $a_s(z)$ 为历史与控制器整场实验同时落入记录 $z$ 且 $\|F_h-\overline F_{s,z}\|_F\le t$ 的无条件质量，$A_s=\sum_za_s(z)$。给定共享种子，独立重抽两场完整实验，包含各自初始状态和新鲜随机性；它们的历史边缘仍是独立公平字。二者都好且记录相同的概率 $\sum_za_s(z)^2$ 至多 $E_n(2t)$。Cauchy–Schwarz 给出 $A_s^2\le W E_n(2t)$，而 Markov 给出 $A_s\ge(1-D_s/t^2)_+$。先取种子平均，再用 Jensen，便得到 (7.2)。取 $t=3\sqrt\varepsilon$，由 $D\le9\varepsilon/2$ 得右边至少 $1/4$，得到 (7.3)。对角项保证分母严格为正。这不把“先选记录再重抽后验”误认为保公平边缘的两场实验，也不要求失真、纯度、解码误差有共同最优控制器。

**定理 P5。** 对每个 $\beta>0$ 及每个 $\varepsilon_n=\exp(-\beta n+o(n))>0$，在上述原恢复前提下，令 $\widehat B(\beta)=\widehat b(\beta/2)$，则

$$
\widehat B(\beta)
\le\liminf_n\frac{\ln W_n(\varepsilon_n)}n
\le\limsup_n\frac{\ln W_n(\varepsilon_n)}n
\le\min\{3\beta/2,h_*\}.
\tag{7.4}
$$

上界精确沿用母文 (57.2) 所供应的合法因果舍入及精确历史构造，不作改动。记

$$
\beta_{\rm old}=2a_{\rm old}=\frac{2\xi}{2+\xi/h_*},\qquad
\widehat\beta=2\widehat a=\frac{2\widehat\xi}{2+\widehat\xi/h_*}
>\beta_{\rm old}.
\tag{7.5}
$$

相对于母文整个下率 $B(\beta)=b(\beta/2)$，新下率在每个 $\beta_{\rm old}<\beta<2h_*$ 严格增加，在 $0<\beta\le\beta_{\rm old}$ 及 $\beta\ge2h_*$ 相等。当 $\gamma<1$，有

$$
\lim_n\frac{\ln W_n(\varepsilon_n)}n=\min\{3\beta/2,h_*\}
\quad\text{若 }0<\beta\le\widehat\beta\text{ 或 }\beta\ge2h_*;
\tag{7.6}
$$

$\widehat\beta<\beta<2h_*$ 仍未匹配。若额外有 $\gamma=1$，则条件结论 (7.6) 对所有 $\beta>0$ 成立，仍不构成完整的有限联合恢复律。

**证明。** $\beta>0$ 保证最终 $0<\varepsilon_n<1/4$。对最小宽度应用同控制器必要性 (7.3)，其半径为 $6\sqrt{\varepsilon_n}=\exp(-\beta n/2+o(n))$，P4 给出 (7.4) 的下界。常数四与六除以 $n$ 后不影响领先对数率。上界仅条件引用已述母文构造。将 P4 的全部比较代入 $a=\beta/2$，即得 (7.5)–(7.6) 及剩余区间。$\square$

更早的整个供应下括号是母文 (57.3) 的

$$
L_{44}(\beta)=\max\{\min(\gamma/64,3\beta/2),\ \min(h_*,\beta/2)\}.
$$

母文 Theorem 57.1 已给出 $B(\beta)>L_{44}(\beta)$ 于 $\gamma/96<\beta<2h_*$，其余 $0<\beta\le\gamma/96$ 及 $\beta\ge2h_*$ 相等。本文比较的对象是更强的整个 $B$，不是把对 $L_{44}$ 的既有改进重算为新成果。解析平滑不产生终端量化器的因果实现、额外读出或参考访问，也不改变原完整因果峰值宽度的资源定义。

## 8. 实际尾字计数与 Gram 球冠的直接推论

本节 D1 是母文精确字典与半长伴篇范数恒等式的 **DIRECT COROLLARY（直接推论）**，不计作新的独立数学内容。

为把计数对象说清楚，取四元数单位 $I_q,J_q,K_q$，满足平方为 $-1$ 及 $I_qJ_q=K_q$，并取

$$
\rho(I_q)=\begin{pmatrix}i&0\\0&-i\end{pmatrix},\quad
\rho(J_q)=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
\rho(K_q)=\begin{pmatrix}0&i\\i&0\end{pmatrix}.
$$

置 $u=K_q$、$v=\sqrt3I_q$，于是 $u^2=-1$、$v^2=-3$、$uv=-vu$。令

$$
\zeta=(1+v)/2,\quad\mathbb E=\mathbb Z[\zeta],\quad
\bar\zeta=1-\zeta,\quad\delta=(1+\zeta)u,
\quad H=\zeta+\delta,\quad H'=\zeta-\delta.
\tag{8.1}
$$

此处的算术字母是 $H,H'$，不与矩阵 $A_g$ 或空间 $H=\mathbb C^5$ 混同。尾字坐标子序为 $\mathcal K=\mathbb E+\mathbb E\delta$，并不把它等同于整个 $\mathbb E+\mathbb E u$。有 $\delta e=\bar e\delta$、$\delta^2=-3$，以及

$$
\begin{aligned}
(E+F\delta)(G+J'\delta)&=EG-3F\overline{J'}+(EJ'+F\bar G)\delta,\\
N(E+F\delta)&=N_E(E)+3N_E(F),\\
N_E(x+y\zeta)&=x^2+xy+y^2.
\end{aligned}
\tag{8.2}
$$

四元数范数正定且乘法性成立，$N(H)=N(H')=4$，$\|\rho(q)\|_F^2=2N(q)$。令 $\mathcal T_m$ 为按原顺序相乘的实际 $m$ 字尾积，$\mathcal T_0=\{1\}$。其生成恰为从 $(1,0)$ 出发的符号关系

$$
(E,F)\longmapsto(E\zeta-3\epsilon F,\ \epsilon E+F\bar\zeta),
\qquad\epsilon=+1\text{ 对应 }H,\quad-1\text{ 对应 }H'.
\tag{8.3}
$$

这仅定义实际字语言，本文不执行该关系，也不枚举状态。母文 Proposition 45.3 的自由积注入性作为前提，故不同同长度字有不同尾积，$|\mathcal T_m|=2^m$。写 $W=E_W+F_W\delta$；所有实际尾积满足 $N(W)=4^m$。

母文 Theorem 45.2 的确切时间字典如下：对 $n\ge1$，令 $b_k=h_{n+1-k}$、$\sigma_k=b_1+\cdots+b_k\pmod2$、$p=\sigma_n$。记 $a=H/2$、$a'=H'/2$、$a_0=a$、$a_1=a'$，则

$$
G_h=(-i)^{n-p}\rho(c_hI_q^p),\qquad
c_h=a\,a_{\sigma_1}\cdots a_{\sigma_{n-1}},\qquad
2^nc_h=H H_{\sigma_1}\cdots H_{\sigma_{n-1}}.
\tag{8.4}
$$

这里 $H_0=H,H_1=H'$，$g_0=(-i)\rho(a)$、$g_1=\rho(aI_q)$。逆映射由 $\sigma_0=0$、$\sigma_n=p$ 及 $b_k=\sigma_{k-1}\mathbin{\mathrm{xor}}\sigma_k$ 后再反转给出。因此每个固定奇偶类恰好包含每个长度 $n-1$ 尾字一次，每条历史仍有质量 $2^{-n}$。式中 $(-i)^{n-p}$ 和右侧 $I_q^p$ 均保留。

**推论 D1。** 对 $n\ge1$，令 $m=n-1$，对 $R\ge0$ 定义有序实际尾对计数

$$
D_m(R)=\#\{(W,V)\in\mathcal T_m\times\mathcal T_m:N(W-V)\le R\}.
\tag{8.5}
$$

则对每个 $r\ge0$，

$$
E_n(r)=\tfrac12\,4^{-m}D_m(4^mr^2/2)
+\tfrac12\mathbf1_{\{r\ge2\}}.
\tag{8.6}
$$

对 $m\ge1$，按实际 $m$ 字尾积索引的 Gram 形式是

$$
G(W,V)=\operatorname{Re}(E_W\bar E_V+3F_W\bar F_V)
=4^m-\tfrac12N(W-V).
\tag{8.7}
$$

所以 (8.5) 中的计数事件也恰好是闭球冠条件

$$
G(W,V)\ge4^m(1-r^2/4).
\tag{8.8}
$$

**证明。** 同一奇偶类中，(8.4) 的标量及右侧 $I_q^p$ 一致，故两条尾积 $W,V$ 的距离平方为

$$
2\,4^{-n}N(H(W-V))=8\,4^{-n}N(W-V)
=2\,4^{-m}N(W-V).
$$

各奇偶类各有 $D_m(4^mr^2/2)$ 个满足距离条件的有序对，每对历史质量 $4^{-n}$。两个同奇偶类总贡献为 $2\,4^{-n}D_m=\tfrac12 4^{-m}D_m$。异奇偶类之间距离恰为 $2$；两个方向共有 $2^{2n-1}$ 个有序对，总质量 $1/2$，且在闭边界 $r=2$ 一并进入。这证明 (8.6)。当 $n=1$，$m=0$，$D_0(R)=1$ 对 $R\ge0$ 成立，故 $E_1(r)=1/2$ 于 $0\le r<2$，$r\ge2$ 时为一。当 $r=0$，注入性给出 $D_m(0)=2^m$，恢复 $E_n(0)=2^{-n}$；$n=0$ 则始终另用 $E_0(r)=1$。

对相同长度范数作正定二次型极化，$N(W-V)=N(W)+N(V)-2G(W,V)=2\cdot4^m-2G(W,V)$，得到 (8.7)，移项便是 (8.8)，等号边界保留。$\square$

特别地，对 $n\ge1$、$0<r\le1/4$，P3 及 (8.6) 给出

$$
D_{n-1}(4^{n-1}r^2/2)
\le32\,4^{n-1}\bigl(r^3+2^{-j}R_{n-j}\bigr)
\tag{8.9}
$$

对每个整数 $0\le j\le n$ 且 $4r<\Delta_j$ 都成立。这里只是把 P3 乘以 $2\,4^{n-1}$；没有新计数定理。它是一般半径上的实际 Gram 球冠控制，不是半长伴篇的单位条目测试。该伴篇的最近尺度尾差范数十二、分块同余、低秩和中间字母障碍都不自行推出任意半径的熵最优计数。

## 9. 原始全尺度目标与未消除的缺口

保留母文 Definition 58.1 的原目标：对 **每个固定 $a,c>0$**，在同一个实际公平时间字律下，证明

$$
E_n(ce^{-an})\le e^{o(n)}\bigl(e^{-3an}+2^{-n}\bigr).
\tag{9.1}
$$

全尺度版本仍为 **OPEN**。P4 不是它的全称完成。当 $0<\gamma<1$ 时，本文已覆盖每个固定 $c>0$ 的 $0<a\le\widehat a$ 和 $a\ge h_*$；对 $\widehat a<a<h_*$，本文给出的上界指数严格小于目标指数，但没有构造目标的反例。若另能给出 $\gamma=1$，P4 条件上会完成 (9.1)；该数值不在供应前提中，也未在本文取得。

母文 Proposition 58.2 的平滑对应仍保留：在所有固定 $a,c>0$ 的尺度族 $r_n=ce^{-an}$ 上，(9.1) 等价于允许固定半径倍数和次指数因子的

$$
\|f_{n,r_n}\|_2^2\le e^{o(n)}
\left(1+\frac{2^{-n}}{V(2r_n)}\right).
\tag{9.2}
$$

由 (9.2) 配合 (5.8)、(5.10) 得到 (9.1)。由 (9.1) 推回平滑界时，先注意 (5.7) 中每个交集质量至多 $V(2r)$，中心距离大于 $4r$ 时交集为空，所以

$$
\|f_{n,r}\|_2^2\le\frac{E_n(4r)}{V(2r)}.
\tag{9.3}
$$

对 (9.1) 使用固定 $4c$，再用 $V(2r)\asymp r^3$ 即得 (9.2)。这里必须有整个固定尺度族；单一半径序列上的结论不能无条件转给其他序列。

初始无交叠的现有证书仍只允许 $m/n\to\min\{a/h_*,1\}$。新剩余块指数虽然从 $\xi$ 增至 $\widehat\xi$，但 $\gamma<1$ 时仍有 $\widehat\xi<h_*$，因此 (6.6) 留下上述缺口。需要额外的实际联合交叠信息、熵最优能量控制或其他论证；仅把旧收缩重复分块、使用必要壳同余或低秩包装不能补回所缺信息。

母文 Theorem 52.1 的精确反射关系也不应被误当闭合递推：若 $f_j=\lambda^{-1}g_j$，则 $f_1=f_0J$，且

$$
E_n(r)=\tfrac12 E_{n-1}(r)+\tfrac12 C_{n-1}(r),\qquad
C_{n-1}(r)=\Pr(\|U_0-JV_0\|_F\le r),
\tag{9.4}
$$

其中 $U_0,V_0$ 是独立的实际长度 $n-1$ 的 $F$ 前缀。反射在第二个前缀左侧，$C_{n-1}$ 是额外相关，不能换成 $E_{n-1}$。$n=1$ 时 $U_0=V_0=I$，反射距离为 $2$，与 D1 端点相符。该恒等式本身不给出 (9.1)。

若 (9.1) 对全部固定 $a,c>0$ 成立，同控制器逆定理与既有因果上界将匹配每个 $\beta>0$ 的领先率。对一般 $\varepsilon_n=e^{-\beta n+o(n)}$，可先固定 $0<a<\beta/2$，最终 $6\sqrt{\varepsilon_n}\le e^{-an}$，由单调性取得下指数 $\min\{3a,h_*\}$，再令 $a\uparrow\beta/2$；不需要 $o(n)$ 对变化的 $a$ 一致。

即使这一条件率全部匹配，也不等于母文 Definition 50.1 与其所指原恢复问题的完整有限 $(n,\varepsilon)$ 联合律。统一有限误差常数、次指数因子、精确正误差平台起点、尖锐首节省误差 $\eta_n$、静态表与逆控制精度及延迟因果兼容性仍有各自义务，且 $W_n(0)=2^n$ 保留。实际配对目标若失败，也不会单独否定操作率：无条件近对簇和可实现因果后验族约束不同。

## 10. 母文与半长伴篇的精确对应

下列对应规定哪些内容是供应前提、哪些在本文使用；所有引用仅按给定正文理解，不打开嵌入链接。

| 母文位置 | 本文中的作用与边界 |
| --- | --- |
| Definition 45.1、Theorem 45.2 | 四元数生成元、实际时间顺序、两奇偶提升及每条历史的 $2^{-n}$ 权重；本文 (8.4) 与 D1 直接采用 |
| Proposition 45.3 | 实际尾字注入性的自由积前提；实际树支持只占距离 $2n$ 整球的 $1/(3\cdot2^n)$，不能当整壳均匀律 |
| Theorem 46.1、Proposition 46.2 | 不同同奇偶历史的分子差范数为正的 $48$ 倍数、异奇偶距离 $2$；本文只需较弱 $\Delta_m\ge2^{-m}$，不把分离界冒充三维熵计数 |
| Definition 47.1、Theorems 47.2–47.3 | 实际尾字递推、$\mu_m=\min_{W\ne V}N(W-V)/12$（$m\ge1$）、正整数且不为二、$\#$ 反序换字与 $\operatorname{Re}F_W=\pm1$ 的范数四十八刚性；不提供一般半径计数 |
| Theorem 48.1、Corollary 48.2 | 条件全 qutrit 桥 $d_n=16\mu_{n-1}/4^n$ 只在 $n\ge3$；$d_1=d_2=2/3$ 独立处理。首节省与平台结论是必要界，不是本文 P5 的新输入 |
| Propositions 49.1–49.3 | 供应的完整长度五表、非实际壳点及有界见证；有限记录 $(\mu_1,\ldots,\mu_7)=(1,1,1,1,3,1,1)$ 不外推任意长度，本文未执行该表或递推 |
| Definition 50.1 | 任意长度可达性、尖锐首节省误差及原联合恢复问题均保留未解 |
| Definition 51.1、Theorem 51.2、Proposition 51.3 | 本文 (1.3)、(1.7)、(7.1)–(7.3) 的同一控制器、同一记录、平均恢复及碰撞必要性；精确宽度端点仍为 $2^n$ |
| Theorem 52.1 | 左反射恒等式 (9.4)，不是仅用 $E_n$ 的闭递推 |
| Definitions 53.1–53.2 | 矩阵 $A_g$、$K$、平移、实际 $P=UQ_0$、共同相位、分离与精确 $\gamma_{22}$ 的全部归一化 |
| Theorem 54.1，特别是 (54.2)–(54.4) | 全局零均值的行列式分解及完整复 $\mathcal H_c$ 上的谱隙转移是继承内容；其旧三字估计由本文 P2 加强 |
| Theorem 55.1，特别是 (55.2)–(55.8) | 实际解析密度、初始无交叠能量、精确重叠及体积公式；P3 只替换剩余块收缩并给出完整证明 |
| Theorem 56.1 | 安全整数块 (6.5)、旧的整个 $b(a)$ 与 floor 指数比较；P4 针对完整旧包络严格比较 |
| Theorem 57.1 | 既有合法因果上界、旧率 $B$、更早下括号 $L_{44}$ 及旧未匹配区间；本文 P5 条件代入新配对界 |
| Definition 58.1、Proposition 58.2、Definition 58.3 | 全尺度目标、平滑对应与联合律边界；本文第 9 节全部保留，不把局部改进报告为全目标完成 |

半长伴篇在自己的算术章节中把 $H,H'$ 记作 $A,B$。下表中的 $A,B$ 仅沿用该算术记号；其矩阵 $G$ 是 Gram 形式，不是实际历史矩阵 $G_h$。为明确这些对应的含义，对 $k\ge1$、$P,R\in\mathcal T_k$，该伴篇的形式定义为

$$
\begin{aligned}
\Omega(P,R)&=\operatorname{Re}(F_P\bar E_R-E_P\bar F_R),\\
G(P,R)&=\operatorname{Re}(E_P\bar E_R+3F_P\bar F_R),\\
K_\zeta(P,R)&=\operatorname{Re}(F_P\bar\zeta\bar E_R-E_P\zeta\bar F_R),\\
L_\pm(P,R)&=K_\zeta(P,R)\pm G(P,R),\qquad
q(P,R)=N(P-R)/12.
\end{aligned}
$$

以下只对应它已经给出的实际索引陈述，不把这些形式当作额外计数估计。

| 半长伴篇位置及明确陈述 | 本文的使用范围 |
| --- | --- |
| §1 | 坐标子序 $\mathcal K$、范数、实际递推和原时间字典；注入性条件上来自母文自由积，支持本文 D1 的实际索引与计数重数 |
| §2 | 实际同余、$F_W=r+jv$ 的整数性、$W^\#=E_W-\bar F_W\delta$ 及最近对刚性，均是继承算术；不产生一般球冠能量 |
| §3，Theorem 3.1 | 端点 $AA,BB,AB,BA$ 的 $F\bmod4\mathbb Z[v]$ 依次为 $1,-1,-v,v$；$r=1$ 必须是 $AA$ 且 $F=1+4tv$，$r=-1$ 必须是 $BB$ 且 $F=-1+4tv$。这些是必要条件，非可达性充分条件 |
| §4，Corollary 4.1 | $r=0$ 等价于实际字串被 $\#$ 固定；奇正长度无此字，长度 $2k$ 恰有 $2^k$ 个 $SS^\#$，含 $k=0$ 空字。这是继承恒等式与注入性的直接推论 |
| §5，Theorems 5.1–5.2 | 实际半长索引上的 $r(PR^\#)=\Omega(P,R)$、$r(PAR^\#)=L_+(P,R)$、$r(PBR^\#)=L_-(P,R)$；正最近见证在首字母 $(A,B)$ 块恰对应条目一。$\Omega,K_\zeta$ 交替、$G$ 为正定四坐标形式产生的半正定 Gram、$L_+^{\mathsf T}=-L_-$、五矩阵秩均至多四；秩界不证明计数或复杂度节省 |
| §5，(5.6)–(5.10) | $G(P,R)=4^k-N(P-R)/2=4^k-6q(P,R)$；$\Omega=0$ 恰为 $P=R$，$G,L_\pm$ 均非零，异首字母块的 $K_\zeta$ 非零。$\Omega,L_\pm$ 的块模四剩余为 $0,1,-1,0$，$G\equiv4\pmod6$；本文只将极化恒等式直接用于 D1 的一般半径阈值 |
| §6，Theorem 6.1 | 对 $k\ge1$，$L_+-L_-=2\cdot4^k-N(P-R)\equiv8\pmod{12}$，所以同一外字配置的两个中间字母选择至多一个有 $r\in\{\pm1\}$。这是配置障碍，不排除整个奇长度；空半字 $k=0$ 的差为二，不能纳入该障碍 |
| §7 | 最近无序对数 $a_m$ 等于 $r=1$ 的实际字数；$0\le a_{2k},a_{2k+1}\le2^{2k-2}$（$k\ge1$），$a_1=1$，不给一般层的正下界；共同尾字填充使差范数乘 $4^{\lvert P\rvert+\lvert S\rvert}$，不能传播缩小尺度的最近对 |
| §8 | 有界符号见证及供应完整长度五表给出 $\mu_5=3,a_5=0$；壳点 $E_*=28-31\zeta,F_\pm=\pm1+4v$ 通过范数、旧同余和新端点过滤却仍非实际点。本文不将壳条件、有限例子或纯幂恒等式外推为任意长度规律 |
| §9 | 可选 $d$–$\mu$ 条件桥限于 $n\ge3$，$n=1,2$ 分开；不作为本文独立的操作宽度证明 |
| §10 | 任意长度集合 $\{m\ge1:\mu_m=1\}$、全序列 $\mu_m$ 及原恢复目标均未解决；本文不宣称解决这些目标 |

P1 的工具是标准 Hilbert 空间几何。P2–P4 是在所给实际模型及精确谱隙上得到的来源相对新综合；P5 是其条件操作后果。D1 只是直接推论。正交投影、Cauchy–Schwarz、对称 Dirichlet 恒等式、卷积、幂等性、极化、球体积及初等指数比较均为标准工具。这里不声称进行了文献穷尽搜索，也不把来源相对增量升级为已经核实的全局原创性或优先权。

## 11. 结论的范围

本文的确定形式是：在明确供应的前提下，以未经执行、可错的符号推导得到 P1–P5 与直接推论 D1。P2 量化所有整数 $L\ge0$ 和所有全局零均值的复 $L^2$ 函数；$\mathcal H_c$ 上的估计不削弱为某个实子空间，行列式模式在 $Q_0$ 被处理，常数模式不衰减。P3 保留 $n\ge0$、$0\le m\le n$、$0<r\le1/4$ 和严格 $4r<\Delta_m$；配对事件及球保持闭边界。

每个固定 $a,c>0$ 的次指数余项可以依赖这些固定参数；本文不声称对变化的 $a,c$ 一致，也不从领先指数推出统一有限 $(n,\varepsilon)$ 估计。$\gamma=1$ 的全尺度推论始终是条件边界，未给出该值；当 $\gamma<1$，残余配对区间 $\widehat a<a<h_*$ 和残余操作区间 $\widehat\beta<\beta<2h_*$ 仍为 OPEN。

所有实际历史、相位、重数、对角对和两个行列式分量保留。Haar 仅用于解析平滑；没有把有限支持的字律换成 Haar 或整壳律，没有把必要同余换成实际可达性，没有把分别最优的估计换成同时可达的对象。有限支持字律与非原子 Haar 在每个有限时刻的奇异性也没有被收缩界消除。

本文不提供尖锐首节省误差、任意长度最近对分类、完整有限联合恢复律、物理实现或有限精度逆控制的资源证书；不推出任何经验神经模型质量、通用学习定理或 kernel 结果。原模型的 full-$H$ 终端 CPTP 解码、独立种子、不可访问参考、平均不减半全参考误差和完整因果宽度权限始终保持。所有数学结论仍受开篇的条件与证据上限约束。

## 追加锚（本行以下为增补区）

## 12. 增补的证据范围与状态

本节以下是对前文第 1–11 节的补充。前文开篇所声明的
**UNEXECUTED conditional symbolic mathematics** 证据范围保持原样：前文的供应
前提、P1–P5、D1 以及由它们继承的恢复蕴涵，没有因本补充而获得 kernel、全局
认证或新的执行状态。

本补充给出普通数学草稿。第 13 节的有限矩阵等式是在所显示的
$\mathbb Q(\sqrt3,i)$ 中的精确有限代数；第 14–15 节给出独立的度量和
计数证明；第 16 节明确标为尚未证明的充分供应条件。它们都不是 Lean
核验、全局认证或对前文状态的重写。所有实际历史、相位、重数、闭事件和
两个行列式分量继续按第 1 节保留。

## 13. 完整 $S^3$ 上的有限表示见证与 $\gamma_{22}$ 的方向

仍取第 2 节的同一个 $A=A_g$、$J$、$J_j=A^{-j}JA^j$ 以及
$C_1=J_0J_1$、$C_2=J_1J_2$。直接相乘得到

$$
C_1=\begin{pmatrix}
-\frac12&\frac{\sqrt3}{4}+\frac{3i}{4}\\
-\frac{\sqrt3}{4}+\frac{3i}{4}&-\frac12
\end{pmatrix},
\quad
C_2=\begin{pmatrix}
-\frac12+\frac{3\sqrt3}{8}i&-\frac{5\sqrt3}{16}-\frac{3i}{16}\\
\frac{5\sqrt3}{16}-\frac{3i}{16}&-\frac12-\frac{3\sqrt3}{8}i
\end{pmatrix}.
\tag{13.1}
$$

这两个矩阵属于 $SU(2)$，且 $C_j^{-1}=C_j^\dagger$。令

$$
X=\frac18\begin{pmatrix}6&-5\sqrt3+9i\\-5\sqrt3-9i&-6\end{pmatrix}.
\tag{13.2}
$$

则 $X=X^\dagger$、$\operatorname{tr}X=0$、$X^2=3I_2$，并且逐项有限
相乘给出

$$
\frac14\left(C_1XC_1^\dagger+C_1^\dagger XC_1\,+C_2XC_2^\dagger+C_2^\dagger XC_2\right)=\frac58X.
\tag{13.3}
$$

为说明 (13.3) 的有限代数内容，可用 Pauli 基底
$\sigma_x,\sigma_y,\sigma_z$ 写共轭作用的实三维矩阵。四项对称平均为

$$
M=\frac1{256}
\begin{pmatrix}
25&63\sqrt3&-18\sqrt3\\
63\sqrt3&-5&-90\\
-18\sqrt3&-90&-20
\end{pmatrix},
$$

而 $q=(-5\sqrt3,-9,6)^{\mathsf T}$ 满足 $Mq=\frac58q$。这与
(13.2) 的坐标完全相同，故 (13.3) 是精确等式而非浮点特征值判断。

在完整单位球面 $S^3\subset\mathbb C^2$ 上，对任意矩阵记
$v_X(z)=z^\dagger Xz$，并取

$$
v(z)=z^\dagger Xz
=\frac34(|z_1|^2-|z_2|^2)
+\frac14\operatorname{Re}\!\left[(-5\sqrt3+9i)\overline z_1z_2\right].
\tag{13.4}
$$

对 $z_1=\sqrt t\,e^{i\alpha}$、$z_2=\sqrt{1-t}\,e^{i\beta}$，归一化球面
测度为 $dt\,d\alpha\,d\beta/(2\pi)^2$。相位积分消去交叉项，故

$$
\int_{S^3}v\,dm=\frac34\int_0^1(2t-1)\,dt=0.
$$

同样计算平方，令 $B=-5\sqrt3+9i$，则 $|B|^2=156$，从而

$$
\begin{aligned}
\|v\|_2^2
&=\frac{36}{64}\int_0^1(2t-1)^2dt
+\frac{2\cdot156}{64}\int_0^1t(1-t)dt\\
&=\frac{36}{64}\cdot\frac13+\frac{312}{64}\cdot\frac16=1.
\end{aligned}
\tag{13.5}
$$

函数 $v$ 是完整 $S^3$ 上的非零、均值零、范数一的复 $L^2$ 函数。对
$\mathsf U_gv(z)=v(g^{-1}z)$，有
$\mathsf U_gv_X=v_{gXg^\dagger}$。因此 (13.3) 在原来的完整球面作用中给出

$$
\mathsf U_\sigma v=\frac58v,
\qquad
\frac{\langle v,(I-\mathsf U_\sigma)v\rangle}{\|v\|_2^2}=\frac38.
\tag{13.6}
$$

这只给出

$$
0<\gamma_{22}\le\frac38<1
\tag{13.7}
$$

中的上界方向；正性沿用前文已明确标出的供应前提。没有证明 $\gamma_{22}=3/8$，
没有证明它是全空间最小商，也没有得到独立的正下界。特别地，不能把
$3/8$ 当作 P1–P4 所需的谱隙下界。

若只在继承的 $0<\gamma=\gamma_{22}\le1$ 和前文条件包络下工作，
$\kappa=1-\gamma/2$、$\widehat\xi=-\ln\kappa$ 满足

$$
\kappa\ge\frac{13}{16},\qquad
0<\widehat\xi\le\ln\frac{16}{13}=:\xi_*<\ln2=:h_*.
\tag{13.8}
$$

故前文阈值

$$
\widehat a=\frac{\widehat\xi}{2+\widehat\xi/h_*}
\le
a_*:=\frac{\ln(16/13)}{2+\ln(16/13)/\ln2}<\frac{h_*}{3}.
\tag{13.9}
$$

对任意 $\widehat a<a<h_*$，同一条件包络的线性支满足

$$
3a>a+\widehat\xi(1-a/h_*),
\qquad
h_*>a+\widehat\xi(1-a/h_*),
$$

所以该包络在这一区间严格低于目标 $\min\{3a,h_*\}$。尤其
$a_*<a<h_*$ 对所有与 (13.7) 相容的正 $\gamma$ 都未被这个包络匹配。
这只是供应包络的未消除区间；它不是原目标的反例。原始的每个固定
$a,c>0$ 的全尺度目标和完整有限联合恢复目标仍为 **OPEN**。相应地，
若沿用前文的率变量 $\widehat\beta=2\widehat a$，则
$\widehat\beta\le2a_*$，其条件操作率的未匹配区间仍为
$\widehat\beta<\beta<2h_*$。

## 14. 任意概率律的三维紧群几何不等式

下面的引理对 $K=SU(2)\sqcup SU(2)J$ 上任意概率律 $\nu$ 成立，因而不把
有限实际字律替换成 Haar 律。取常数 $a_0,b_0>0$，使得由第 5 节的
体积公式，在 $0<s\le1/2$ 时

$$
a_0s^3\le V(s)\le b_0s^3.
\tag{14.1}
$$

**引理 G。** 存在绝对常数 $C_G$，使得对所有充分小的
$0<\delta\le1/8$、所有 $0\le r\le1/8$ 以及 $K$ 上任意概率律 $\nu$，

$$
E_\nu(r):=(\nu\times\nu)\{(x,y):d(x,y)\le r\}
\le C_G(1+r/\delta)^3E_\nu(\delta).
\tag{14.2}
$$

证明如下。取一个极大的 $\delta/2$-分离有限网
$\{x_i\}_{i\in I}$。紧性保证有限性，极大性保证每个点在某个
$B_{\delta/2}(x_i)$ 内。按最小指标打破平局，得到可测分割
$K=\bigsqcup_iA_i$，且 $A_i\subseteq B_{\delta/2}(x_i)$，故
$\operatorname{diam}A_i\le\delta$。置 $p_i=\nu(A_i)$。闭事件的边界
不被删除，因为同一 cell 中的每一对点都满足 $d(x,y)\le\delta$，所以

$$
\sum_i p_i^2\le E_\nu(\delta).
\tag{14.3}
$$

若 $x\in A_i$、$y\in A_j$ 且 $d(x,y)\le r$，则
$d(x_i,x_j)\le r+\delta$。对固定 $i$ 令
$N_i=\{j:d(x_i,x_j)\le r+\delta\}$。网点间的关系是对称的。由于
$r+\delta<2$，相反行列式分量的网点不可能同时出现在 $N_i$ 中；因此
所有这些小球留在同一个三维分量内。网点的开球
$B_{\delta/4}(x_j)$ 两两不交，并包含于
$B_{r+5\delta/4}(x_i)$。当 $\delta$ 足够小时，(14.1) 给出

$$
|N_i|\,a_0(\delta/4)^3
\le b_0(r+5\delta/4)^3
\le C_0(1+r/\delta)^3\delta^3,
\tag{14.4}
$$

其中 $C_0$ 与 $\nu,r,\delta$ 无关。于是最大对称邻居度满足
$\max_i|N_i|\le C_0(1+r/\delta)^3$。再由
$p_ip_j\le(p_i^2+p_j^2)/2$，并按有序邻居求和，得到

$$
\begin{aligned}
E_\nu(r)
&\le\sum_i\sum_{j\in N_i}p_ip_j\\
&\le\sum_i|N_i|p_i^2
\le C_0(1+r/\delta)^3\sum_i p_i^2.
\end{aligned}
$$

结合 (14.3) 即得 (14.2)。当 $r=0$ 时直接由单元对角项和
$E_\nu(0)\le E_\nu(\delta)$ 得到结论；因此 (14.2) 包括闭边界和
$0\le r$ 的端点。

对实际长度 $n$ 的律 $\nu_n=\mu^{*n}$，置

$$
\delta_n=2^{-n/3},\qquad Q_n=2^nE_n(\delta_n).
\tag{14.5}
$$

当 $n$ 足够大使 $\delta_n$ 落入引理 G 的范围时，
$\delta_n^3=2^{-n}$ 和
$(1+x)^3\le4(1+x^3)$ 给出统一的几何界

$$
E_n(r)\le C\,Q_n(2^{-n}+r^3)
\qquad(0\le r\le1/8),
\tag{14.6}
$$

其中 $C$ 为绝对常数。这个界只使用实际律的 cell 质量，保留了所有
历史重数。

## 15. 临界尺度、平滑二范数与精确尾字计数

先证明临界尺度与原全尺度陈述的等价性。若
$Q_n\le e^{o(n)}$，把 $r=ce^{-an}$ 代入 (14.6)，固定的 $a,c>0$
给出

$$
E_n(ce^{-an})\le e^{o(n)}\bigl(e^{-3an}+2^{-n}\bigr).
\tag{15.1}
$$

反过来，在原目标中取 $a=h_*/3$、$c=1$，便有
$ce^{-an}=\delta_n$，所以

$$
Q_n=2^nE_n(\delta_n)\le2e^{o(n)}=e^{o(n)}.
\tag{15.2}
$$

因此

$$
Q_n\le e^{o(n)}\quad\Longleftrightarrow\quad
\text{原目标对每个固定 }a,c>0\text{ 成立}.
\tag{15.3}
$$

这里的 $o(n)$ 可依赖所固定的 $a,c$；(14.6) 中的常数 $C$ 是统一的。
这只是等价改写，不是临界假设的证明。

令 $f_{n,s}=P^nb_s$。由实际前向卷积和闭球交叠的逐项展开，

$$
\|f_{n,s}\|_2^2
=4^{-n}\sum_{h,g}
\frac{m_K(B_s(G_h)\cap B_s(G_g))}{V(s)^2}.
\tag{15.4}
$$

若中心距离不超过 $r$，则 $B_r(G_h)$ 落在两个
$B_{2r}$ 球的交中；反之，交叠非空时中心距离不超过 $2s$。取
$s=2\delta_n$，并用 (14.1)，得到充分大 $n$ 时的两侧关系

$$
Q_n\le C_1\|P^nb_{2\delta_n}\|_2^2,
\tag{15.5}
$$

以及

$$
\|P^nb_{2\delta_n}\|_2^2
\le\frac{E_n(4\delta_n)}{V(2\delta_n)}
\le C_2Q_n.
\tag{15.6}
$$

第一式直接来自 (15.4)：若 $d(G_h,G_g)\le r$，则
$B_r(G_h)\subseteq B_{2r}(G_h)\cap B_{2r}(G_g)$，故

$$
E_n(r)\le\frac{V(2r)^2}{V(r)}\|P^nb_{2r}\|_2^2.
$$

在 $r=\delta_n$ 时，由 $2^n\delta_n^3=1$ 及 (14.1)，
$2^nV(2\delta_n)^2/V(\delta_n)\le64b_0^2/a_0$，即得 (15.5)。
第二式来自 (15.4) 中交叠质量至多 $V(2\delta_n)$，再把 (14.6)
用于 $4\delta_n$。故

$$
Q_n\le e^{o(n)}
\quad\Longleftrightarrow\quad
\|P^nb_{2\delta_n}\|_2^2\le e^{o(n)}.
\tag{15.7}
$$

现在给出不带取整的尾字等式。对 $m\ge0$ 保持第 8 节实际尾字集合
$\mathcal T_m$ 和有序计数

$$
D_m(R)=\#\{(W,V)\in\mathcal T_m^2:N(W-V)\le R\}.
$$

第 8 节的实际时间字典把长度 $n=m+1$ 的每个奇偶类逐一对应于
$\mathcal T_m$，并保留每条历史的质量 $2^{-(m+1)}$。同一奇偶类的
距离平方为 $2\,4^{-m}N(W-V)$，两类之间的距离恰为 $2$。因为
$\delta_{m+1}<2$，异奇偶项不进入临界闭球，故精确地

$$
E_{m+1}(\delta_{m+1})
=\frac12\,4^{-m}
D_m\!\left(\frac{4^m\delta_{m+1}^2}{2}\right).
\tag{15.8}
$$

而

$$
\frac{4^m\delta_{m+1}^2}{2}
=\frac{2^{2m}2^{-2(m+1)/3}}2
=2^{(4m-5)/3}.
$$

所以，不作 floor 或半径舍入，保留 $m=n-1$，有

$$
\boxed{
Q_{m+1}=2^{-m}D_m\!\left(2^{(4m-5)/3}\right)
}\qquad(m\ge0).
\tag{15.9}
$$

端点 $m=0$ 也在此式中成立：约定 $D_0(R)=1$（$R\ge0$），则
$Q_1=1$。式 (15.9) 是实际有序尾对、对角项、原时间顺序和奇偶
分量的精确字典，不是整壳均匀律。

同样，若 $k+\ell=n$，把实际历史按时间写成 $XY$，其中
$X\sim\mu^{*\ell}$ 是最后 $\ell$ 个字母的乘积，
$Y\sim\mu^{*k}$ 是最初 $k$ 个字母的乘积。对两份独立历史
$X'Y'$，双不变性给出严格的时间顺序恒等式

$$
d(XY,X'Y')=d(X'^{-1}X,Y'Y^{-1}).
\tag{15.10}
$$

两项分别由独立的末块和首块产生，故其差律为

$$
\alpha_\ell=\check{(\mu^{*\ell})}*\mu^{*\ell},
\qquad
\beta_k=\mu^{*k}*\check{(\mu^{*k})}.
\tag{15.11}
$$

这里没有交换乘积次序，也没有把两个边缘问题的分别最优值替换为同一联合
实现的最优值。式 (15.10)–(15.11) 只是临界碰撞问题的另一种联合表述。

## 16. 未证明的有限异常 Peter–Weyl 供应条件

下面的条件是一个保留原非对称算子 $P=UQ_0$ 的充分供应者，当前不声称
它对这些生成元成立。令 $\Pi$ 是 $L^2(K;\mathbb C)$ 中有限个完整
Peter–Weyl 左正则等型分量的正交投影，包含常数分量和 $\chi$ 分量；记
其有限秩为 $d_\Pi$。假定存在 $s_n\ge1$，$\log s_n=o(n)$，使

$$
\|P^n(I-\Pi)\|_{2\to2}^2\le s_n\,2^{-n}
\qquad(n\ge1).
\tag{16.1}
$$

这是未证明的充分条件，涉及原来的非正规前向算子及固定有限异常空间，
不是谱半径结论、对称化行走结论或 Shannon 熵结论。

为说明它确实足以供应临界二范数，取任一完整等型分量的标准正交基，
有限和的 reproducing kernel 对角线恒为 $d_\Pi$：左不变性使其为常数，
积分后常数正是秩。因此对任意非负概率密度 $f$，

$$
\|\Pi f\|_2
=\left\|\int_K f(x)(\phi_a(x))_a\,dm_K(x)\right\|_2
\le\int_K f(x)\left(\sum_a|\phi_a(x)|^2\right)^{1/2}dm_K(x)
\le\sqrt{d_\Pi}.
\tag{16.2}
$$

投影 $\Pi$ 与每个左平移、因而与原来的 $P$ 交换。对
$f=b_{2\delta_n}$，由 (14.1) 有
$\|f\|_2^2=V(2\delta_n)^{-1}\le C_3\,2^n$。于是 (16.1)–(16.2)
以及 $(a+b)^2\le2a^2+2b^2$ 给出

$$
\begin{aligned}
\|P^nf\|_2^2
&\le2\|P^n\Pi f\|_2^2
 +2\|P^n(I-\Pi)f\|_2^2\\
&\le2d_\Pi+2s_n2^{-n}\|f\|_2^2
\le2d_\Pi+2C_3s_n=e^{o(n)}.
\end{aligned}
\tag{16.3}
$$

由 (15.7) 和 (14.6)，(16.1) 条件蕴含临界尺度的
$Q_n\le e^{o(n)}$，进而蕴含原全尺度目标。条件 (16.1) 本身仍是
**UNPROVED sufficient supplier**；它没有被当作实际算子的已证性质，也没有
改变主目标仍为临界配对能量这一事实。

## 17. $\gamma$ 见证与实际局部恢复误差的有限对应

这里仅复用固定有限二元 CPTP 定理 59.2 及其在编码 qutrit 上的已发表
应用。为固定生成元与该应用的时间对应，仍取 $A=A_g$、
$g_0=A,g_1=AJ$。同长度的共同相位消去后，约定相对矩阵为
$F_h^{-1}F_k=G_h^{-1}G_k$。由 $J_j=A^{-j}JA^j$、$J_j^2=I$
以及 (1.2) 的实际时间顺序，有

$$
\begin{aligned}
G_{00}^{-1}G_{11}
&=A^{-2}(AJ)(AJ)=A^{-1}JAJ=J_1J_0=C_1^{-1},\\
G_{000}^{-1}G_{101}
&=A^{-3}(AJ)A(AJ)=A^{-2}JA^2J=J_2J_0=(C_1C_2)^{-1}.
\end{aligned}
$$

这里 $C_1C_2=J_0J_1^2J_2=J_0J_2$。由 (13.1) 的精确矩阵及
$SU(2)$ 中逆矩阵与原矩阵的迹相同，

$$
\frac12\operatorname{tr}(J_2J_0)
=\frac12\operatorname{tr}(C_1C_2)=\frac58.
$$

因此实际同一组 $A,J$ 的等奇偶历史 $000,101$ 在编码 qutrit 的
相对矩阵中满足 $\cos\theta=5/8$。对固定且输入无关的公平权重
$p=q=1/2$，定理 59.2 的数值域距离为 $\nu=\cos\theta=5/8$，故

$$
\delta_{1/2}(U)
=1-\sqrt{1-4(1/2)(1/2)(1-\nu^2)}
=1-\nu=\frac38.
\tag{17.1}
$$

这是实际 $000/101$ 这一固定记录、固定公平权重、编码 qutrit 范围内的
**条件 recovery error**。它与 (13.6) 的测试 Rayleigh 商同为
$1-5/8=3/8$。因此在这个具体有限代数实例中可以写成

$$
\gamma_{22}\ \le\ \underbrace{\frac38}_{\text{测试商}}
=\underbrace{\frac38}_{\text{实际 }000/101\text{ 的条件局部误差}}.
\tag{17.2}
$$

等号右侧的局部解释依赖定理 59.2 的固定输入无关公平权重和编码 qutrit
嵌入；它不涉及全局控制器、历史相关的最优记录、全体记忆宽度或终端
CPTP 家族的全局最优。也不允许把公平权重改为输入依赖 Born 权重，或把
这个角度推广为任意角度的谱隙—恢复等式。式 (17.2) 的唯一谱隙结论仍是
变分定义给出的上界 $\gamma_{22}\le3/8$，而非一般的谱隙与恢复误差
相等定理。

## 18. 工具、来源相对性与未解决目标

本补充使用的工具是标准的矩阵系数与 Rayleigh 商计算、紧群上的
Peter–Weyl 分解、最大分离网与 Cauchy–Schwarz 邻居计数、Haar 小球体积
比较，以及第 59.2 节的有限二元 CPTP 定理。它们在这里按实际
$A,J$、实际时间顺序和实际公平字律应用；没有用 Haar 字律替换有限历史，
也没有把与本字母表不相符的 entropy 或 golden-gate 方案作为定理前提。
这些陈述是来源相对的普通数学草稿，不作全局原创性或文献穷尽声明。

目前保留的主问题仍是：对同一实际独立公平历史、相位、重数、闭有序配对
事件，证明每个固定 $a,c>0$ 的 (9.1)，以及在其基础上的完整有限
$(n,\varepsilon)$ 联合恢复律。有限表示见证排除了同一条件包络中
$\gamma_{22}=1$ 的分支，却没有证明或否定临界能量估计。有限异常
Peter–Weyl 条件 (16.1) 是可检验的额外路线，尚未在实际算子上得到。

## 追加锚（本行以下为增补区）

## 19. 原临界配对能量的有限加权自旋表述

本节仍取 (1.1) 的 $A=A_g$、$J=\operatorname{diag}(-1,1)$，
以及 (2.2) 的实际算子 $P=T_AQ_0$。特别地，
$A^*A=I$ 而 $\det A=-1$；不把 $A$ 当作 $SU(2)$ 的元素。
以下所有球、距离、Haar 概率和 $b_r$ 均为第 5 节在完整 $K$ 上的定义。
每条历史仍为 (1.2) 的 $G_h=(AJ^{h_n})\cdots(AJ^{h_1})$，
其质量为 $2^{-n}$。共同的 $\lambda^{-n}$ 只通过 (1.5) 消去。
本节不需要同长度注入性、分离下界或第 2 节的正谱隙前提。

### 19.1 完整中心、表示与非负密度

记 $z=iI$。由于 $K$ 包含 $SU(2)$，与 $K$ 中每个元素交换的矩阵
先与 $SU(2)$ 的对角环面交换，因而是对角矩阵；再与其非对角旋转交换，
两个对角元必须相等。标量 $\alpha I$ 属于 $K$ 当且仅当
$\alpha^4=1$，故

$$
Z(K)=\{I,z,z^2,z^3\},\qquad
K=Z(K)SU(2),\qquad Z(K)\cap SU(2)=\{I,-I\}.
\tag{19.1}
$$

因此 $K/Z(K)\simeq SU(2)/\{I,-I\}$。其不可约酉表示由整数
$\ell\ge0$ 编号；在 $K$ 上写成

$$
\rho_\ell(g)=(\det g)^\ell\operatorname{Sym}^{2\ell}(g),\qquad
 d_\ell=2\ell+1,\qquad \vartheta_\ell(g)=\operatorname{tr}\rho_\ell(g).
\tag{19.2}
$$

这里的 $\vartheta_\ell$ 与第 2 节的一维行列式特征 $\chi$ 不同。
在 $SU(2)$ 上，(19.2) 是偶次对称幂；且
$\rho_\ell(z)=(-1)^\ell i^{2\ell}I=I$。
$SU(2)$ 的不可约表示为各次对称幂，$-I$ 在第 $k$ 次幂上作用为
$(-1)^k$，故 (19.2) 恰好穷尽完整中心作用平凡的不可约表示，且没有重复。
若 $u\in SU(2)$ 的特征值为 $e^{\pm it}$，其权重和给出

$$
\vartheta_\ell(u)=\sum_{j=-\ell}^{\ell}e^{2ijt}
=\frac{\sin(d_\ell t)}{\sin t}.
\tag{19.3}
$$

端点按连续延拓解释。这些特征标是实值的，在 Haar 概率 $m_K$ 下
正交归一：两个行列式分量的积分相同，各占权重 $1/2$，而在
$SU(2)$ 上应用特征标正交关系。

在原复 Hilbert 空间中定义

$$
R_Z=\frac14\sum_{k=0}^3T_{z^k}.
\tag{19.4}
$$

这是中心不变子空间的正交投影，并与 $P$ 交换。若 $f\in L^2(K)$
是非负实函数，则

$$
\frac14\|f\|_2^2\le\|R_Zf\|_2^2
=\frac1{16}\sum_{j,k=0}^3\langle T_{z^j}f,T_{z^k}f\rangle
\le\|f\|_2^2.
\tag{19.5}
$$

左侧只用四个对角项以及全部内积非负；右侧来自正交投影的收缩性。
等价地，$\|f\|_2^2\le4\|R_Zf\|_2^2$。
特别地，这适用于 $f=P^nb_r$。非负限制不可删除：
$f(x)=\det x$ 满足 $\|f\|_2=1$ 而 $R_Zf=0$。
所以中心平凡部分的估计不能由 (19.5) 推成任意复向量的算子范数估计。

### 19.2 原球的 Fourier 系数与实际矩阵幂

采用 Fourier 约定

$$
\widehat f(\rho)=\int_K f(x)\rho(x)\,dm_K(x),\qquad
\widehat{T_gf}(\rho)=\rho(g)\widehat f(\rho).
\tag{19.6}
$$

第二式由 $x=gy$ 换元得到。这个约定同样满足 Plancherel 公式：
其矩阵系数可视为通常逆元约定下反对偶表示系数的转置，Hilbert–Schmidt
范数及不可约维数权重均不变。

对 $0<r<2$，原 Frobenius 球 $B_r(I)$ 完全位于 $SU(2)$ 分量。
事实上，$\det x=-1$ 时特征值为 $\eta,-\overline\eta$，故
$\operatorname{Re}\operatorname{tr}x=0$ 且 $\|I-x\|_F=2$。
在 $SU(2)$ 分量写特征值为 $e^{\pm it}$，则

$$
\|I-u\|_F^2=8\sin^2(t/2),\qquad
\theta_r=2\arcsin\frac r{2\sqrt2},\qquad
V(r)=\frac1\pi\int_0^{\theta_r}\sin^2t\,dt.
\tag{19.7}
$$

这里 $1/\pi$ 已含完整 $K$ 的分量权重，正是 (5.9) 的同一个体积。
球函数是共轭不变的，Schur 引理和 (19.3) 因而给出

$$
\widehat b_r(\rho_\ell)=\beta_\ell(r)I_{d_\ell},\qquad
\beta_\ell(r)=
\frac{\int_0^{\theta_r}\sin(d_\ell t)\sin t\,dt}
{d_\ell\int_0^{\theta_r}\sin^2t\,dt},\qquad \beta_0(r)=1.
\tag{19.8}
$$

定义实际单步矩阵

$$
M_\ell=\rho_\ell(A)\frac{I+\rho_\ell(J)}2.
\tag{19.9}
$$

独立公平比特与原时间顺序精确给出

$$
\mathbb E_h\rho_\ell(G_h)=M_\ell^n.
\tag{19.10}
$$

这是先按最后比特取期望再归纳的矩阵乘积等式，不交换任何不同因子。
应用 Peter–Weyl 和 Plancherel，得到

$$
\|R_ZP^nb_r\|_2^2
=\sum_{\ell=0}^{\infty}d_\ell|\beta_\ell(r)|^2
\|M_\ell^n\|_{\rm HS}^2.
\tag{19.11}
$$

权重是 $d_\ell$，而矩阵空间有 $d_\ell^2$ 个系数；两者不能混为
同一个重数。这里使用实际的 $n$ 次幂，不以特征值模的 $n$ 次幂替代。

### 19.3 有限自旋和与显式双向比较

沿用 (14.5) 的 $\delta_n=2^{-n/3}$、$Q_n=2^nE_n(\delta_n)$，置

$$
L_n=\left\lfloor\frac{2^{n/3}}4\right\rfloor,
\qquad
\mathcal S_n=\sum_{\ell=0}^{L_n}(2\ell+1)
\left\|\left[\rho_\ell(A)\frac{I+\rho_\ell(J)}2\right]^n
\right\|_{\rm HS}^2.
\tag{19.12}
$$

$\mathcal S_n$ 是本节有限加权自旋和，避免与 (2.3) 的 $S_j$ 混用。
取 (5.10) 的明确常数

$$
a_0=\frac1{12\sqrt2\pi},\qquad b_0=\frac1{6\sqrt2\pi},
\qquad a_0r^3\le V(r)\le b_0r^3\quad(0<r\le1/2).
\tag{19.13}
$$

**定理 19.1（有限加权自旋临界等价）。** 对每个整数 $n\ge18$，

$$
\boxed{\quad
\frac{Q_n}{128\pi^2}\le\mathcal S_n
\le\frac{18522\pi^2}{32a_0}\,Q_n.
\quad}
\tag{19.14}
$$

两侧均针对 (1.3) 的原闭 Frobenius 事件、全部有序历史对和全部重数。

证明。暂写 $\delta=\delta_n$、$L=L_n$，则 $\delta\le1/64$。
在 $[0,1/\sqrt2]$ 上，$\arcsin$ 的导数至多 $\sqrt2$，故
$\theta_{2\delta}\le2\delta$。对 $\ell\le L$，

$$
d_\ell\theta_{2\delta}\le
\left(\frac1{2\delta}+1\right)2\delta
=1+2\delta\le\frac{33}{32}<\frac\pi2.
\tag{19.15}
$$

由 $\sin x\ge2x/\pi$（$0\le x\le\pi/2$）和 $\sin t\le t$，
在整个 $0\le t\le\theta_{2\delta}$ 上有
$\vartheta_\ell(t)/d_\ell\ge2/\pi$，包括连续端点 $t=0$。
平均后 $\beta_\ell(2\delta)\ge2/\pi$，所以 (19.11) 给出

$$
\mathcal S_n\le\frac{\pi^2}4\|R_ZP^nb_{2\delta}\|_2^2
\le\frac{\pi^2}4\|P^nb_{2\delta}\|_2^2.
\tag{19.16}
$$

下面只把既有 (15.4)–(15.6) 中需要的几何常数明确化。
取极大 $\delta/2$-分离网，以最近网点及固定的平局规则形成可测单元
$A_i\subseteq B_{\delta/2}(x_i)$，并令 $p_i=\nu_n(A_i)$。
单元直径至多 $\delta$，故 $\sum_i p_i^2\le E_n(\delta)$。
若两点的距离至多 $4\delta$，相应中心距离至多 $5\delta$。
这些邻居中心的开 $\delta/4$ 球两两不交，全部落入
$B_{21\delta/4}(x_i)$。所有体积半径都至多 $1/2$，故每个中心的邻居数至多

$$
\frac{b_0(21\delta/4)^3}{a_0(\delta/4)^3}
=2\cdot21^3=18522.
\tag{19.17}
$$

邻居关系对称，用 $p_ip_j\le(p_i^2+p_j^2)/2$ 按有序邻居求和得到
$E_n(4\delta)\le18522E_n(\delta)$。
由原球交叠公式 (15.4)，

$$
\|P^nb_{2\delta}\|_2^2
\le\frac{E_n(4\delta)}{V(2\delta)}
\le\frac{18522}{8a_0}Q_n.
\tag{19.18}
$$

(19.16) 与 (19.18) 给出 (19.14) 的上界。
这些公式中的 $2\delta$ 平滑半径和 $4\delta$ 配对半径均保持原义；
相反方向仍由 (15.5) 的
$Q_n\le(64b_0^2/a_0)\|P^nb_{2\delta}\|_2^2$ 供应。

为证明有限和的下界，构造非负的有限特征标核，而不估计 (19.11) 的高频尾部。
令

$$
m=\lfloor L/2\rfloor=\left\lfloor\frac1{8\delta}\right\rfloor,
\quad N_m=\sum_{j=0}^m(2j+1)^2,
\quad \mathcal D_m=\sum_{j=0}^m(2j+1)\vartheta_j,
\quad \mathcal F_m=\frac{|\mathcal D_m|^2}{N_m}.
\tag{19.19}
$$

特征标正交性给出 $\int_K\mathcal F_m\,dm_K=1$，且
$\mathcal F_m\ge0$ 处处成立。在原球 $B_\delta(I)$ 上，(19.15) 的
同一正弦界给出 $\mathcal D_m\ge2N_m/\pi$。直接求和有

$$
N_m=\frac{(m+1)(2m+1)(2m+3)}3,
\qquad N_m-(m+1)^3=\frac{m(m+1)(m+2)}3\ge0.
\tag{19.20}
$$

由于 $m+1>1/(8\delta)$，因此

$$
\mathcal F_m(x)\ge\frac{4N_m}{\pi^2}
\ge\frac{\delta^{-3}}{128\pi^2}
\qquad(x\in B_\delta(I)).
\tag{19.21}
$$

将 (19.3) 的有限权重和相乘，逐权重计数得到

$$
\vartheta_j\vartheta_k
=\sum_{\ell=|j-k|}^{j+k}\vartheta_\ell.
\tag{19.22}
$$

具体地，左侧权重 $e^{2iat}$ 的系数是满足 $b+c=a$、
$|b|\le j,|c|\le k$ 的整数对数；右侧系数是同时满足
$|j-k|\le\ell\le j+k$、$|a|\le\ell$ 的整数 $\ell$ 数，两者相等。
该等式在 $SU(2)$ 上成立，并因所有特征标均通过 $K/Z(K)$ 而在 $K$ 上成立。
因此

$$
\mathcal F_m=\sum_{\ell=0}^{2m}d_\ell\kappa_\ell\vartheta_\ell,
\qquad \kappa_\ell\ge0.
\tag{19.23}
$$

还需要上界而不仅是系数的正性。中心性、Schur 引理和正交关系给出
$\widehat{\mathcal F_m}(\rho_\ell)=\kappa_\ell I$。
$\mathcal F_m$ 是非负概率密度，而 $\rho_\ell(x)$ 酉，故

$$
|\kappa_\ell|=
\|\widehat{\mathcal F_m}(\rho_\ell)\|_{\rm op}
\le\int_K\mathcal F_m\,dm_K=1.
\tag{19.24}
$$

对两个独立的原实际历史，(19.10) 给出

$$
\mathbb E_{h,g}\vartheta_\ell(G_h^{-1}G_g)
=\operatorname{tr}\bigl((M_\ell^n)^*M_\ell^n\bigr)
=\|M_\ell^n\|_{\rm HS}^2.
\tag{19.25}
$$

由 $2m\le L$ 和 $0\le\kappa_\ell\le1$，

$$
\mathbb E_{h,g}\mathcal F_m(G_h^{-1}G_g)
=\sum_{\ell=0}^{2m}d_\ell\kappa_\ell\|M_\ell^n\|_{\rm HS}^2
\le\mathcal S_n.
\tag{19.26}
$$

原距离左右不变，所以 $d(G_h,G_g)\le\delta$ 当且仅当
$G_h^{-1}G_g\in B_\delta(I)$。利用 (19.21) 和球外核的非负性，

$$
\mathbb E_{h,g}\mathcal F_m(G_h^{-1}G_g)
\ge\frac{\delta^{-3}}{128\pi^2}E_n(\delta)
=\frac{Q_n}{128\pi^2}.
\tag{19.27}
$$

期望始终是原来的 $4^{-n}\sum_{h,g}$；相同乘积的不同历史和全部对角项
都没有合并或删除。这就证明了另一侧。$\square$

$\ell=0$ 项等于一，故 $\mathcal S_n\ge1$；对角历史对也给出
$Q_n\ge1$。由定理 19.1 和既有 (15.3)、(15.7)，

$$
\log\mathcal S_n=o(n)
\quad\Longleftrightarrow\quad Q_n\le e^{o(n)}
\quad\Longleftrightarrow\quad
\text{(15.3) 的原全尺度配对目标成立}.
\tag{19.28}
$$

其中 $\log\mathcal S_n=o(n)$ 仍是需要证明的必要且充分条件。
(19.14) 给出有限和的等价表述，没有给出该和的次指数估计。
它也不把非负球密度的结论提升为完整复空间上的统一算子衰减。

## 20. 原完整复空间上的相位保持压缩

本节仍在 $L^2(K;\mathbb C)$ 中工作，写
$Q=Q_0=(I+T_J)/2$、$\mathcal H_J=\operatorname{ran}Q$。
为与 (2.5) 对齐，取 $C=C_1=JA^{-1}JA$，并令 $D=AC$。
新的对称平均记作 $\mathsf S$，不改用原来的 $S_j$。

### 20.1 被压缩的实际矩阵

直接将 (1.1) 代入，得到

$$
C=\begin{pmatrix}
-1/2&(\sqrt3+3i)/4\\
(-\sqrt3+3i)/4&-1/2
\end{pmatrix},\qquad
D=\operatorname{diag}\left(\frac{-\sqrt3+i}{2},
\frac{\sqrt3+i}{2}\right).
\tag{20.1}
$$

由 $\operatorname{tr}C=-1$、$\det C=1$，Cayley–Hamilton 给出
$C^2+C+I=0$，而 $C\ne I$。改变非对角项的符号并用 $C^{-1}=-I-C$，
得到 $JCJ=C^{-1}$。$D$ 为对角矩阵，故 $DJ=JD$；定义又给出
$A=DC^{-1}$。其两个对角元为 $e^{5\pi i/6},e^{\pi i/6}$，所以

$$
C^3=I,\qquad D^3=z=iI,\qquad D^{12}=I.
\tag{20.2}
$$

$D$ 在完整 $K$ 中的阶是十二，不能按阶三的元素处理。

置

$$
E_C=\frac{I+T_C+T_C^2}{3},\qquad
\mathsf S=\frac{T_C+T_{C^{-1}}}{2}
=\frac{3E_C-I}{2}.
\tag{20.3}
$$

$C^3=I$ 说明 $E_C^*=E_C=E_C^2$，其像恰为 $T_C$ 的不动向量空间。
因而 $\operatorname{spec}(\mathsf S)\subseteq\{1,-1/2\}$。
由 $JCJ=C^{-1}$，$T_J\mathsf ST_J=\mathsf S$；$D$ 与 $J$ 交换，
所以 $\mathsf S$、$T_D$ 均保持 $\mathcal H_J$。
若 $v\in\mathcal H_J$，则
$T_JT_{C^{-1}}v=T_CT_Jv=T_Cv$，于是

$$
QT_{C^{-1}}Q=\mathsf SQ,\qquad
QT_AQ=T_D\mathsf SQ.
\tag{20.4}
$$

这给出保留原相位的压缩算子

$$
\mathsf B=(QT_AQ)|_{\mathcal H_J}
=(T_D\mathsf S)|_{\mathcal H_J}.
\tag{20.5}
$$

这里没有从 $\mathsf S$ 的两个谱值推断 $T_D\mathsf S$ 的幂衰减：
乘积的反复作用还取决于 $T_D$ 如何移动 $E_C$ 的像。
例如常数函数满足 $\mathsf S1=T_D1=1$，因此完整空间中已经有不衰减向量。
移除常数等有限分量后的情形还需要独立估计。

### 20.2 时间幂、球向量与完整等型截断

**定理 20.1（完整复空间的精确压缩恒等式）。** 对每个整数 $n\ge1$
及每个复函数 $f\in L^2(K)$，

$$
P^n=T_A\mathsf B^{n-1}Q,\qquad
\|P^nf\|_2=\|\mathsf B^{n-1}Qf\|_2.
\tag{20.6}
$$

$\mathsf B^0$ 指 $\mathcal H_J$ 上的恒等算子。
若 $\Pi$ 是任意固定有限个完整 Peter–Weyl 左正则等型分量的投影，
则 $\mathcal H_{J,\Pi}=\mathcal H_J\cap\ker\Pi$ 受 $\mathsf B$ 保持，且

$$
\begin{aligned}
\|P^n(I-\Pi)f\|_2
&=\|\mathsf B^{n-1}Q(I-\Pi)f\|_2,\\
\|P^n(I-\Pi)\|_{2\to2}
&=\|\mathsf B^{n-1}|_{\mathcal H_{J,\Pi}}\|_{2\to2}.
\end{aligned}
\tag{20.7}
$$

证明。$P=T_AQ$ 给出 $n=1$。若 (20.6) 在 $n$ 成立，则
$Q T_A$ 在 $\mathcal H_J$ 上等于 $\mathsf B$，故
$P^{n+1}=T_AQT_A\mathsf B^{n-1}Q=T_A\mathsf B^nQ$。
$T_A$ 是酉算子，遂得范数等式，且没有使用实值、正性或中心限制。
完整等型投影与每个左平移交换，因而与 $Q,T_A,T_D,\mathsf S$ 及其
适当限制均交换。于是 $\mathcal H_{J,\Pi}$ 不变。
第一条截断等式直接来自 (20.6)。在 $\ker\Pi$ 上，$Q$ 正是到
$\mathcal H_{J,\Pi}$ 的正交投影，故其收缩性给出第二条的“$\le$”。
反过来在 $\mathcal H_{J,\Pi}$ 中取单位向量，此时
$Qf=f$、$(I-\Pi)f=f$，取上确界给出“$\ge$”。
若该空间为零，两侧均为零。$\square$

特别地，对第 15 节的原球向量，有

$$
\|P^nb_{2\delta_n}\|_2
=\|\mathsf B^{n-1}Qb_{2\delta_n}\|_2.
\tag{20.8}
$$

没有换成商群球或不同的 Haar 归一化。对 (16.1) 允许的固定 $\Pi$
还须包含常数和行列式分量；其充分条件恰好改写为：存在 $s_n\ge1$，
$\log s_n=o(n)$，使

$$
\|\mathsf B^{n-1}|_{\mathcal H_{J,\Pi}}\|_{2\to2}^2
\le s_n2^{-n}\qquad(n\ge1).
\tag{20.9}
$$

这个全向量统一条件仍未证明。它比只要求 (20.8) 中指定球向量的范数
次指数增长更强；两者不能凭压缩恒等式相互替换。

### 20.3 四个中心扇区的相位

对 $\xi\in\{1,i,-1,-i\}$，定义

$$
\mathcal L_\xi=\{f:T_zf=\xi f\},\qquad
R_\xi=\frac14\sum_{k=0}^3\xi^{-k}T_z^k.
\tag{20.10}
$$

这些是两两正交的闭扇区及其投影，直和为完整 $L^2(K;\mathbb C)$。
本节所有算子以及完整等型投影均保持这些扇区。
置 $W=T_{iD}=T_zT_D$。由 $D^3=z$ 得 $(iD)^3=I$，故 $W^3=I$。
在 $\mathcal L_\xi$ 上，

$$
T_D^3=\xi I,\qquad T_D=\xi^{-1}W,\qquad
\mathsf B|_{\mathcal H_J\cap\mathcal L_\xi}
=\xi^{-1}(W\mathsf S)|_{\mathcal H_J\cap\mathcal L_\xi}.
\tag{20.11}
$$

对应 $\xi=1,i,-1,-i$ 的系数分别为 $1,-i,-1,i$。
因此若 $f_\xi\in\mathcal L_\xi$，完整的时间恒等式是

$$
P^nf_\xi
=\xi^{-(n-1)}T_A
\left((W\mathsf S)|_{\mathcal H_J\cap\mathcal L_\xi}\right)^{n-1}Qf_\xi.
\tag{20.12}
$$

单位相位在单扇区范数中消去，但不能从算子等式中删除。
对 $f=\sum_\xi f_\xi$，输出仍正交，故

$$
\|P^nf\|_2^2
=\sum_\xi\left\|
\left((W\mathsf S)|_{\mathcal H_J\cap\mathcal L_\xi}\right)^{n-1}Qf_\xi
\right\|_2^2.
\tag{20.13}
$$

这不认同不同扇区上的作用，也不允许只保留 $\xi=1$ 的扇区。
(19.5) 的非负密度比较与这里任意复向量的恒等式承担不同的量词。

还可用两个 $SU(2)$ 矩阵记录中心不变公式与完整公式的关系。
取 Pauli 矩阵

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\quad
r=\frac{I-i\sqrt3\sigma_y}{2},\quad
s=\frac{I+i\sqrt3\sigma_z}{2}.
\tag{20.14}
$$

用 $\sigma_j^2=I$ 及其反交换关系相乘，可得

$$
iA=rs,\quad r^3=s^3=-I,\quad JrJ=r^{-1},\quad Js=sJ,
\quad C=s^{-1}r^2s,\quad D=zs.
\tag{20.15}
$$

写 $V=T_s$、$\mathsf C_r=(T_r+T_{r^{-1}})/2$。
由 $JrJ=r^{-1}$，有 $QT_rQ=\mathsf C_rQ$，且 $V$ 与 $Q$ 交换。
另外 $r^2=(-I)r^{-1}$、$r^{-2}=(-I)r$，所以

$$
\mathsf S=T_z^2V^{-1}\mathsf C_rV,\qquad
\mathsf B=T_z^{-1}\mathsf C_rV\big|_{\mathcal H_J},\qquad
P^n=T_z^{-n}T_rV(\mathsf C_rV)^{n-1}Q.
\tag{20.16}
$$

最后一式也可从 $P=T_z^{-1}T_rVQ$ 和 $QT_rQ=\mathsf C_rQ$ 归纳得到。
只有在 $\xi=1$ 扇区，中心因子才全为一；一般扇区须保留 $\xi^{-n}$。
(20.16) 和 (20.6) 因而是同一实际算子的两种相位完整表达。

## 21. 每个紧开子群上的直接正双陪集障碍

母文 [Proposition 45.3](AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md#45-quaternion-coordinates-for-the-actual-chronological-word-language)
已经给出实际字律在树上的薄支撑，并区分实际律与完整球壳律。
这里考察更具体的接口：能否选一个紧开子群，使实际正测度经右平滑后成为
左不变测度。下面的逐字约化和指数比较适用于每个紧开子群，不以母文的
自由积或群分类作为前提。

### 21.1 同一实际字的有理四元数坐标

为避免与母文的四元数坐标以及物理空间 $H$ 混淆，本节把有理代数记为
$\mathbb B=(-1,-3)_{\mathbb Q}$，抽象生成元记为 $u,v$。
在 (20.14) 的复矩阵中取

$$
u=-\frac i2(\sigma_x+\sqrt3\sigma_y),\qquad
v=-i\sqrt3\sigma_z,\qquad a=\frac{I-v-2uv}{4}.
\tag{21.1}
$$

Pauli 乘法给出

$$
u^2=-I,\quad v^2=-3I,\quad uv=-vu,\qquad
a=iA,\qquad \frac v{\sqrt3}=iJ,
\quad \operatorname{Nrd}(a)=1,\quad\operatorname{Nrd}(v)=3.
\tag{21.2}
$$

这与母文 §45 的有理代数一致。具体地，把母文的坐标另写为
$u_s=i\sigma_x$、$v_s=i\sqrt3\sigma_z$，则

$$
v=-v_s,\qquad u=\frac{(v_s-I)u_s}{2},\qquad
u_s=\frac{(v-I)u}{2},\qquad
a=\frac{I+v_s+(3I+v_s)u_s}{4}.
\tag{21.3}
$$

后式就是母文 (45.1) 的 $a$；两边坐标可以有理地相互恢复。
对实际历史 $h$，令 $k(h)=\sum_{j=1}^nh_j$，并保持原次序定义

$$
q_h=(av^{h_n})\cdots(av^{h_1})\in\mathbb B^\times.
\tag{21.4}
$$

由 $A=-ia$、$J=-iv/\sqrt3$，逐个实际字母相乘得

$$
G_h=(-i)^{n+k(h)}3^{-k(h)/2}q_h,
\qquad\operatorname{Nrd}(q_h)=3^{k(h)}.
\tag{21.5}
$$

(21.5) 的复矩阵等式记录了每条历史自己的相位和尺度。
它允许将同一 $q_h$ 放入射影算术表示，不允许在原 Frobenius 配对事件中
逐字删去这些因子。尤其 $[G_h]=[q_h]$ 是复射影意义的等式；
以下的 $2$-进射影元素由有理 $q_h$ 经明确的分裂映射得到。

### 21.2 明确分裂与每条实际字的平移长度

在 $\mathbb Q_2$ 中取 $t^2=-7$、$t\equiv3\pmod8$。
其存在性可由 Hensel 引理直接得到：对 $f(X)=X^2+7$，
$v_2(f(3))=4>2v_2(f'(3))=2$，根满足 $v_2(t-3)\ge3$。
取分裂映射

$$
u\longmapsto\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
v\longmapsto\begin{pmatrix}t&2\\2&-t\end{pmatrix}.
\tag{21.6}
$$

平方和反交换子分别是 $-I,-3I,0$，因而给出
$\mathbb B\otimes\mathbb Q_2\to M_2(\mathbb Q_2)$ 的非零含幺同态。
四元数代数为中心单代数，该同态单射；两边维数均为四，故为同构。
在这个分裂中继续写 $a,v,q_h$ 表示其矩阵像。直接代入 (21.1)，

$$
a=\frac14\begin{pmatrix}-t-3&2t-2\\2t-2&t+5\end{pmatrix},
\qquad\det a=1,\quad\det v=3.
\tag{21.7}
$$

写 $t=3+8b$、$b\in\mathbb Z_2$，则

$$
2a=\begin{pmatrix}-3-4b&2+8b\\2+8b&4+4b\end{pmatrix},\qquad
\overline{2a}=e=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
\overline v=I.
\tag{21.8}
$$

横线表示模二约化。因此对每条长度 $n$ 的历史，

$$
2^nq_h=(2av^{h_n})\cdots(2av^{h_1})\in M_2(\mathbb Z_2),
\qquad\overline{2^nq_h}=e^n=e\quad(n\ge1).
\tag{21.9}
$$

这是全部历史的同一个归纳，不限于常字或选定子族。

树 $\mathcal T$ 的顶点为 $\mathbb Q_2^2$ 中满 $\mathbb Z_2$ 格的
位似类；若代表格之间的指数为二，则相邻。
每个格的三个相邻类对应 $\mathbb F_2^2$ 的三条直线，故树为三正则。
Smith 标准形说明两个格的相对初等因子为 $2^r,2^s$ 时，距离为 $|r-s|$：
位似消去较小指数后，逐次改变另一个指数给出长度 $|r-s|$ 的格链。
更具体地，相对 $L_0=\mathbb Z_2^2$，每个非根顶点唯一取代表
$L\subset L_0$、$L\not\subset2L_0$，其初等因子为 $(1,2^r)$、$r\ge1$。
相邻顶点中只有 $[L+2^{r-1}L_0]$ 的指数距离下降，其余两个上升。
这一描述由在相对基中列出三条模二直线直接得到，故每个顶点有唯一通往根的
下降路径；图连通且无环，确为树。记 $x_0=[L_0]$。

**定理 21.1（每条实际字的分裂平移长度）。** 对每个整数 $n\ge1$ 和
每条 $h\in\{0,1\}^n$，(21.6) 中的射影元素 $[q_h]$ 满足

$$
d_{\mathcal T}(x_0,[q_h]x_0)=2n,
\qquad\ell_{\mathcal T}([q_h])=2n.
\tag{21.10}
$$

第一式针对所显示的分裂和标准顶点；第二式是平移长度，与顶点无关。

证明。(21.9) 表明 $2^nq_h$ 有单位矩阵元；其行列式赋值为 $2n$。
Smith 初等因子的赋值遂为 $(0,2n)$，故 $q_h$ 的为 $(-n,n)$。
距离公式给出第一式。

还需证明平移长度，而非只证明一个顶点的位移。
(21.9) 的迹模二为一，所以 $T=\operatorname{tr}q_h$ 的赋值为 $-n$；
$d=\det q_h=3^{k(h)}$ 是单位。特征多项式的判别式为

$$
T^2-4d=T^2\left(1-\frac{4d}{T^2}\right),\qquad
1-\frac{4d}{T^2}\equiv1\pmod{16}.
\tag{21.11}
$$

最后一个单位有平方根 $s\equiv1\pmod4$：对其平方根方程从 $1$ 用
Hensel 引理，函数值赋值至少四而导数赋值为一。
于是一个特征值为 $T(1+s)/2$，其赋值为 $-n$；另一个因乘积为 $d$
而赋值为 $n$。两特征值不同，故 $q_h$ 在 $\mathbb Q_2$ 上可对角化。
对角元素在两特征直线确定的格链上平移 $2n$ 条边。
树中链外顶点到该链有唯一最近点；连接该顶点与其像的路径先到链、
沿链移动 $2n$ 步、再离开链，因此距离为链上平移量加两倍离链距离。
最小位移正是 $2n$，证明第二式。$\square$

### 21.3 任意紧开子群的指数与正测度障碍

令 $\mathcal G=\operatorname{PGL}_2(\mathbb Q_2)$。
对紧开子群 $U,V$ 写 $i(U,V)=[U:U\cap V]$，这些指数均有限。
三重交给出

$$
i(U,W)\le i(U,V)i(V,W).
\tag{21.12}
$$

确实，$[U:U\cap W]\le[U:U\cap V\cap W]$，而后者分解成
$[U:U\cap V][U\cap V:U\cap V\cap W]$；第二因子至多
$[V:V\cap W]$。这里不需要子群正规。

**定理 21.2（所有紧开子群的指数下界）。** 对每个 $n\ge1$、每条实际历史
$h\in\{0,1\}^n$ 以及每个紧开子群 $H\le\mathcal G$，

$$
[H:H\cap[q_h]H[q_h]^{-1}]\ge4^n.
\tag{21.13}
$$

证明。先对任意分裂双曲元素 $g\in\mathcal G$ 设其正平移长度为
$\ell$，并令 $D_H(m)=i(H,g^mHg^{-m})$。
沿共轭子群链反复应用 (21.12)，得到

$$
D_H(m)\le D_H(1)^m.
\tag{21.14}
$$

取任意顶点 $x$ 的完整稳定子 $M$。通过 $H$ 和 $g^mHg^{-m}$
再应用两次 (21.12)，并用共轭不变性，得到

$$
D_M(m)\le i(M,H)\,i(H,M)\,D_H(m).
\tag{21.15}
$$

两个前因子可依赖 $H$，但不依赖 $m$。
$M$ 在以 $x$ 为中心的每个球面上传递：在 $x=x_0$ 时这是 Smith
标准形的 $\operatorname{GL}_2(\mathbb Z_2)$ 左右消元，其他顶点由共轭得到。
半径 $r\ge1$ 的球面有 $3\cdot2^{r-1}$ 个顶点，因为第一步有三个选择，
之后每一步排除返回边而有两个选择。
$M\cap g^mMg^{-m}$ 正是 $M$ 中稳定 $g^mx$ 的子群，所以

$$
D_M(m)=3\cdot2^{d(x,g^mx)-1}\ge3\cdot2^{m\ell-1}.
\tag{21.16}
$$

最后的不等式来自双曲元素轴上的平移以及链外距离公式。
将 (21.14)–(21.16) 合并并取 $m$ 次根，令 $m\to\infty$，
所有固定有限前因子消失，得到 $D_H(1)\ge2^\ell$。
对 $g=[q_h]$ 应用定理 21.1 的 $\ell=2n$ 即得 (21.13)。$\square$

这个量词允许 $H$ 随 $n$ 改变。证明中先固定该 $n,h,H$，再令辅助
整数 $m\to\infty$；没有要求各个 $H$ 的前因子一致有界。

记 $m_H$ 为 $H$ 的 Haar 概率，定义原实际正律的右平滑

$$
\nu_{n,H}=2^{-n}\sum_{h\in\{0,1\}^n}\delta_{[q_h]}*m_H.
\tag{21.17}
$$

**推论 21.3（直接正双陪集识别的障碍）。** 对每个 $n\ge1$ 和每个紧开
$H\le\mathcal G$，$\nu_{n,H}$ 不是左 $H$ 不变测度。

证明。$\nu_{n,H}$ 支撑在至多 $2^n$ 个右陪集上，每个被支撑的陪集都有
严格正质量。$H$ 在 $[q_h]H$ 上的左作用轨道大小为

$$
|H[q_h]H/H|=[H:H\cap[q_h]H[q_h]^{-1}]\ge4^n.
\tag{21.18}
$$

若测度左 $H$ 不变，则一个有正质量的右陪集的整个轨道都必须具有
相同正质量，故其支撑至少有 $4^n$ 个右陪集。
这与 $4^n>2^n$ 矛盾。历史间的射影重合只会减少支撑，不影响论证。
$\square$

$n=0$ 时测度为 $m_H$，确实左 $H$ 不变；故正长度限制必要。
把若干原步骤组成一个块也不能避开推论，因为它对每个正总长度都成立。
这只排除在此明确射影实现中把原正律直接识别为稳定双陪集正律，或其
正线性组合的路线。它不排除压缩、较大或不同的表示、选定实际字的系数估计，
也不反驳 (19.28) 的临界目标。

## 22. 中间工具与仍需建立的估计

Peter–Weyl 完备性与紧群矩阵系数正交关系的原始文献为 F. Peter、
H. Weyl，*Die Vollständigkeit der primitiven Darstellungen einer geschlossenen
kontinuierlichen Gruppe*，Mathematische Annalen **97**，737–755，
[DOI: 10.1007/BF01447892](https://doi.org/10.1007/BF01447892)。
本节所需的具体权重和、维数、原球系数、Plancherel 权重和有限正核系数
已分别在 (19.2)–(19.11)、(19.19)–(19.27) 中写出。
平方特征标核与正交投影平均均为标准工具；这些工具并不供应实际矩阵幂的估计。
格树和群作用的背景文献为 J.-P. Serre，*Trees*，
[DOI: 10.1007/978-3-642-61856-7](https://doi.org/10.1007/978-3-642-61856-7)。
这里的模二约化、每字平移长度、任意紧开子群指数比较及正支撑矛盾
均由 (21.6)–(21.18) 的直接论证给出，不依赖群的最大有限子群、
完整有限群合并或算术格分类。

几何接口直接复用本卷 (15.3)、(15.7)，固定有限异常空间的充分接口复用
(16.1)，薄树背景复用母文 Proposition 45.3。
三个不同层次的要求分别是：有限和的必要且充分估计
$\log\mathcal S_n=o(n)$，原球向量在 (20.8) 中的范数估计，以及更强的
统一压缩幂估计 (20.9)。后两者的等式接口已经确定，所需衰减或增长上界
尚未得到。正双陪集障碍不提供这些解析上界。

由这些桥梁也没有得到任意时域的匹配记忆律、完整有限联合恢复律、因果相容性
或物理实现与资源结论；它们仍需各自的数学和实现条件。

## 追加锚（本行以下为增补区）

## 23. 实际有限自旋的奇异结构与酉因子恢复

本节及以下各节仍取 (1.1)、(20.1) 的同一个 $A,J,C,D$，
并取 (19.2) 的中心平凡自旋表示 $\rho_\ell$，作用空间记为
$V_\ell$，维数 $d_\ell=2\ell+1$。所有伴随均指相应 Hilbert
空间内积的伴随。置

$$
Q_\ell=\frac{I+\rho_\ell(J)}2,\qquad
H_\ell=\operatorname{ran}Q_\ell,\qquad
h_\ell=\dim H_\ell,\qquad
B_\ell=(Q_\ell\rho_\ell(A)Q_\ell)|_{H_\ell}.
\tag{23.1}
$$

$M_\ell=\rho_\ell(A)Q_\ell$ 仍是 (19.9) 的实际单步矩阵。
为说明后面群代数的确切来源，在 $K/Z(K)$ 中记
$c=[C]$、$d=[D]=[iD]$、$j=[J]$。母文 Proposition 45.3
的坐标与此处的对应为

$$
iA=\rho(a),\qquad iD=\rho(D_0),\qquad
C=\rho(D_0^{-1}R_0^{-1}D_0),\qquad
c=d^{-1}[R_0]^{-1}d,\qquad [R_0]=dc^{-1}d^{-1}.
\tag{23.2}
$$

这里无下标的 $\rho$ 仅指母文的四元数矩阵映射。
尤其 $c$ 不是 $[R_0]$。该母文已经证明自由积注入性及 $j$
在其外、固定 $[D_0]$ 并反演 $[R_0]$ 的性质。因此直接复用

$$
\Lambda=\langle c,d\rangle\simeq C_3*C_3,\qquad
\Gamma=\langle c,d,j\rangle=\Lambda\rtimes\langle j\rangle,
\qquad jdj=d,\quad jcj=c^{-1},\quad j\notin\Lambda.
\tag{23.3}
$$

更明确地，自由积的一个因子取逆并用另一个因子的元素共轭它，
仍给出自由积生成元；(23.2) 给出正反两向替换。
这也说明母文的 $j$ 作用在本坐标中正是 (23.3)。每个
$\Gamma$ 元素唯一写成 $gj^\epsilon$，$g\in\Lambda$、
$\epsilon\in\{0,1\}$。这些是已给出的群结构供应，不是新的群表示定理。
环境记忆卷 Theorems 10.1、12.2 的 $G(6,3)=C_6*_{C_2}S_3$
给出同一旋转群的另一组坐标：在本坐标中取 $x=dj$，则
$x^3=j$、$x^4=d$，与 $c$ 的轴垂直。

群代数的伴随约定为 $(\sum_ga_gg)^*=\sum_g\overline{a_g}g^{-1}$，
与每个酉表示的 Hilbert 空间伴随相容。约化音节长度是交替出现的
非恒等 $C_3$ 因子元素的个数；$c,c^{-1},d,d^{-1}$ 各算一个音节。
在 $\mathbb C[\Lambda]$ 中置

$$
s=\frac{c+c^{-1}}2,\qquad b=ds,\qquad
\mathcal W_k=\{dc^{\epsilon_1}\cdots dc^{\epsilon_k}:
\epsilon_i\in\{1,-1\}\},\qquad \mathcal W_0=\{e\}.
\tag{23.4}
$$

自由积的约化音节正规形给出 $|\mathcal W_k|=2^k$，每个非空字
的音节长度为 $2k$；显示的乘积顺序固定。$b$ 在 $j$ 共轭下不变。
在 $\mathbb C[\Gamma]$ 中令 $q=(1+j)/2$、$a=dc^{-1}$，则
$qaq=bq$，故 $(aq)^n=ab^{n-1}q$，$n\ge1$。
这只是中心平凡表示中的字典；原历史仍由 (1.2) 定义。

**定理 23.1（实际压缩的重数、行列式与时间迹）。** 对整数 $\ell\ge0$，
令 $\varepsilon_\ell=(-1)^\ell$，并令
$\eta_\ell=1,0,-1$ 按 $\ell\bmod3=0,1,2$ 周期取值。
$H_\ell$ 内的公共 $\langle c,j\rangle\simeq S_3$ 不变空间投影
记为 $E_\ell$，其秩记为 $e_\ell$。则

$$
h_\ell=\frac{d_\ell+\varepsilon_\ell}2,\qquad
e_\ell=\frac{d_\ell+2\eta_\ell+3\varepsilon_\ell}6,
\qquad h_\ell-e_\ell=\frac{d_\ell-\eta_\ell}3.
\tag{23.5}
$$

在 $H_\ell$ 上有

$$
\begin{aligned}
S_\ell&=\left.\frac{\rho_\ell(C)+\rho_\ell(C)^*}{2}\right|_{H_\ell}
       =\frac{3E_\ell-I_{H_\ell}}2,\\
U_\ell&=\rho_\ell(D)|_{H_\ell},\qquad B_\ell=U_\ell S_\ell,\\
B_\ell^*B_\ell&=S_\ell^2,\qquad
U_\ell=B_\ell(4B_\ell^*B_\ell-3I_{H_\ell}).
\end{aligned}
\tag{23.6}
$$

$U_\ell$ 酉。$B_\ell$ 可逆，奇异值为一（重数 $e_\ell$）及
$1/2$（重数 $h_\ell-e_\ell$），从而

$$
|\det B_\ell|=2^{-(d_\ell-\eta_\ell)/3}.
\tag{23.7}
$$

对每个整数 $n\ge1$，实际幂的精确等式为

$$
M_\ell^n=\rho_\ell(A)B_\ell^{n-1}Q_\ell,\qquad
\|M_\ell^n\|_{\rm HS}^2
=\operatorname{Tr}_{H_\ell}\bigl((B_\ell^*)^{n-1}B_\ell^{n-1}\bigr).
\tag{23.8}
$$

证明。由 (19.3)，半转 $j$ 的特征标为 $\varepsilon_\ell$，
三阶旋转 $c,c^{-1}$ 的特征标均为
$\sin((2\ell+1)\pi/3)/\sin(\pi/3)=\eta_\ell$。
$Q_\ell$ 的迹给出 $h_\ell$。在 $V_\ell$ 上令
$E_{C,\ell}=(I+\rho_\ell(C)+\rho_\ell(C)^2)/3$。
由 $C^3=I$，这是到 $C$ 不变空间的正交投影；
$JCJ=C^{-1}$ 使它与 $Q_\ell$ 交换。
所以它在 $H_\ell$ 上的限制就是 $E_\ell$。
$\langle c,j\rangle$ 的六个元素为 $e,c,c^{-1},j,cj,c^{-1}j$。
后三个均为非平凡半转，故群平均投影的迹为
$(d_\ell+2\eta_\ell+3\varepsilon_\ell)/6$。
相减给出 (23.5) 最后一式。

对称平均保持 $H_\ell$，并等于 $(3E_\ell-I)/2$；单独的 $C$
无需保持 $H_\ell$。由 (20.4) 的实际压缩，
$B_\ell=U_\ell S_\ell$。$D$ 与 $J$ 交换，故其在 $H_\ell$
上的限制酉，因而 $B_\ell^*B_\ell=S_\ell^2$。
$S_\ell$ 在 $E_\ell$ 的像和核上分别为 $1,-1/2$，所以

$$
S_\ell^{-1}=2S_\ell-I=4S_\ell^2-3I.
\tag{23.9}
$$

右乘此逆矩阵得到 (23.6) 的酉因子恢复公式；因子的左右次序不能交换。
同一正交分解给出奇异值及其重数，奇异值之积给出 (23.7)。

(23.8) 第一式是定理 20.1 在这个有限表示中的应用；亦可从
$M_\ell=\rho_\ell(A)Q_\ell$ 按原顺序归纳。
$\rho_\ell(A)$ 酉，$Q_\ell$ 是到 $H_\ell$ 的正交投影，
所以在 $V_\ell=H_\ell\oplus\ker Q_\ell$ 的正交基中取平方范数和，
恰得第二式，没有额外 $d_\ell$ 或 $h_\ell$ 因子。
$n=1$ 时其值是 $h_\ell$。$\square$

例如 $\ell=0,\ldots,6$ 时 $(h_\ell,e_\ell)$ 依次为
$(1,1),(1,0),(3,1),(3,1),(5,2),(5,1),(7,3)$。
常数自旋满足 $B_0=M_0=1$。
奇异值表描述一次作用，不给出非正规矩阵 $B_\ell$ 的幂衰减。
这里可用 $iD$ 代表 $D$，仅因 $\rho_\ell$ 对完整中心平凡。
在完整复空间中仍须使用 (20.10)–(20.13)：若 $T_z=\xi I$，则
$W=T_{iD}$、$\mathsf B=\xi^{-1}W\mathsf S$，并且
$P^n=\xi^{-(n-1)}T_A(W\mathsf S)^{n-1}Q$。
四个 $\xi\in\{1,i,-1,-i\}$ 扇区均保留；$D^3=iI$ 没有改成 $I$，
任何一条实际历史也没有重新选相位。

## 24. 原有序历史的有限加权迹与短时间窗

沿用 $\vartheta_\ell$ 的记号，把中心平凡表示的特征标作用于
$\Gamma$ 的射影元素。定义

$$
\begin{aligned}
T(n,L)&=\sum_{\ell=0}^L d_\ell\|M_\ell^n\|_{\rm HS}^2,
\qquad n\ge1,\ L\ge0,\\
\mathcal D_L(g)&=\sum_{\ell=0}^L(2\ell+1)\vartheta_\ell(g),\\
N_L&=\sum_{\ell=0}^L(2\ell+1)^2
=\frac{(L+1)(2L+1)(2L+3)}3.
\end{aligned}
\tag{24.1}
$$

这里 $\mathcal D_L$ 是有限特征标核，不是第 8 节的尾对计数 $D_m$。
$T(n,L_n)=\mathcal S_n$ 恰是 (19.12) 的原加权和。

**定理 24.1（实际短时间加权迹）。** 对所有整数 $n\ge1,L\ge0$，

$$
\left|T(n,L)-2^{-n}\bigl[N_L+(-1)^L(L+1)\bigr]\right|
\le(4L+1)256^{n-1}\bigl(1-2^{-(n-1)}\bigr).
\tag{24.2}
$$

更精确地，若 $k=n-1$，则

$$
\begin{aligned}
T(n,L)
&=\frac1{2\,4^k}\sum_{w,v\in\mathcal W_k}
 \bigl[\mathcal D_L(w^{-1}v)+\mathcal D_L(w^{-1}vj)\bigr]\\
&=4^{-n}\sum_{h,g\in\{0,1\}^n}\mathcal D_L(G_h^{-1}G_g).
\end{aligned}
\tag{24.3}
$$

特别地，对每个固定 $0<\epsilon<2/9$，当 $L\to\infty$ 时一致地有

$$
\frac{T(n,L)}{2^{-n}N_L}
=1+O\!\left(L^{-2}+\frac{512^n}{L^2}\right)
=1+O\!\left(L^{-2}+L^{-9\epsilon}\right),
\qquad 1\le n\le(2/9-\epsilon)\log_2L.
\tag{24.4}
$$

证明。先给出本模型所需的整数高度界。(20.1) 给出
$C=-I/2+i(\sqrt3/2)[(\sqrt3/2)\sigma_x+(1/2)\sigma_y]$。
取固定的 $R=\operatorname{diag}(e^{i\pi/12},e^{-i\pi/12})$，
用 $RCR^*$ 将这个水平轴移到 $x$ 轴；$D,J$ 不变。
取 $c,d$ 的 $SU(2)$ 提升及 $j$ 的提升为

$$
\widetilde c=\frac{-I+i\sqrt3\sigma_x}{2},\qquad
\widetilde d=iD=\frac{-I-i\sqrt3\sigma_z}{2},\qquad
\widetilde j=iJ=-i\sigma_z.
\tag{24.5}
$$

以 $X=i\sqrt3\sigma_x,Y=i\sigma_y,Z=i\sqrt3\sigma_z$ 为基，
$\mathscr O=\mathbb ZI+\mathbb ZX+\mathbb ZY+\mathbb ZZ$ 在乘法下封闭：
$X^2=Z^2=-3I,Y^2=-I$，$XY=-Z,YZ=-X,ZX=-3Y$，
反向乘积各改符号。四个字母 $\widetilde c^{\pm1},\widetilde d^{\pm1}$
均在 $\tfrac12\mathscr O$ 内。因此，音节长度至多 $m$ 的 $g\in\Lambda$
有提升

$$
\widetilde g=2^{-m}(a_0I+a_1X+a_2Y+a_3Z),\qquad
 a_i\in\mathbb Z,\qquad
 a_0^2+3a_1^2+a_2^2+3a_3^2=4^m.
\tag{24.6}
$$

长度小于 $m$ 时只将整数分子乘相应的二次幂，故仍用这个分母。
若提升的特征值为 $e^{\pm i\theta_g}$，则对非恒等的射影元素 $g$，

$$
\sin^2\theta_g=\frac{4^m-a_0^2}{4^m}\ge4^{-m}.
\tag{24.7}
$$

分子是严格正整数：若为零，提升为标量，射影元素即恒等。
$\widetilde g\widetilde j$ 的标量坐标为 $2^{-m}\sqrt3a_3$，所以

$$
\sin^2\theta_{gj}=\frac{4^m-3a_3^2}{4^m}\ge4^{-m}.
\tag{24.8}
$$

这里 $gj$ 对每个 $g\in\Lambda$ 都非恒等，理由是 (23.3) 中的
$j\notin\Lambda$；分子同样是严格正整数。
由 (19.3)，对 $g\ne e$ 立即有
$|\vartheta_\ell(g)|,|\vartheta_\ell(gj)|\le2^m$。
选择提升的正负号不改变整数自旋的特征标或上述正弦平方。

下面同时记录稍后将用于有限自旋多项式的归一化迹估计。
若 $f=\sum_ga_gg\in\mathbb C[\Lambda]$ 在 $j$ 共轭下不变，
且支撑音节长度至多 $m$，则 $\rho_\ell(f)$ 保持 $H_\ell$。
由 $Q_\ell=(I+\rho_\ell(j))/2$，

$$
\operatorname{Tr}_{H_\ell}\rho_\ell(f)|_{H_\ell}
=\frac12\sum_ga_g[\vartheta_\ell(g)+\vartheta_\ell(gj)].
\tag{24.9}
$$

$g=e$ 的括号为 $d_\ell+\varepsilon_\ell=2h_\ell$，
其余每个括号的绝对值至多 $2^{m+1}$。因此

$$
\left|\frac1{h_\ell}\operatorname{Tr}_{H_\ell}
 \rho_\ell(f)|_{H_\ell}-a_e\right|
\le\frac{2^m}{h_\ell}\sum_{g\ne e}|a_g|.
\tag{24.10}
$$

这是对本模型整数高度的应用，不需要 $f$ 的系数为实数或非负。

为处理维数权重，设 $g$ 非恒等，取其非标量提升角度 $\theta$。
几何级数给出
$|\sum_{\ell=0}^q e^{2i\ell\theta}|\le1/|\sin\theta|$。
对权重 $2\ell+1$ 作 Abel 求和：末端权重为 $2L+1$，
权重差的总和为 $2L$。乘上 $e^{i\theta}$ 并取虚部，再用
(19.3) 除以 $\sin\theta$，得到

$$
|\mathcal D_L(g)|\le\frac{4L+1}{\sin^2\theta_g}.
\tag{24.11}
$$

同样适用于 $gj$。另一方面，直接求和给出
$\mathcal D_L(e)=N_L$ 及
$\mathcal D_L(j)=\sum_{\ell=0}^L(2\ell+1)(-1)^\ell=(-1)^L(L+1)$；
后一式也可对 $L$ 归纳。

现在取 $k=n-1$。群代数中

$$
b^k=2^{-k}\sum_{w\in\mathcal W_k}w,\qquad
f_k=(b^*)^kb^k=4^{-k}\sum_{w,v\in\mathcal W_k}w^{-1}v.
\tag{24.12}
$$

$f_k$ 在 $j$ 共轭下不变，所有合并后的系数非负，总质量一，
恒等系数为 $2^{-k}$，支撑长度至多 $4k$。
恒等系数的值使用了 $|\mathcal W_k|=2^k$，而非整壳字数。
在 $H_\ell$ 上 $\rho_\ell(b)=B_\ell$。
故 (23.8)、(24.9) 以及有限求和交换给出 (24.3) 第一行。
第二行直接由 (19.10)、(19.25) 得到：
原来的每个有序历史对均以质量 $4^{-n}$ 进入；
$G_h=(AJ^{h_n})\cdots(AJ^{h_1})$ 的时间次序保持 (1.2) 不变。
两个式子是同一矩阵幂范数的精确展开，不是对原历史选择子族后重加权。

$w=v$ 的 $2^k$ 项贡献恰为
$2^{-n}[N_L+(-1)^L(L+1)]$。
其余有序对占 (24.12) 的质量 $1-2^{-k}$。
对每个这样的 $w^{-1}v\ne e$，使用 $m=4k$ 的
(24.7)–(24.8)、(24.11)，两项核各至多 $(4L+1)4^{4k}$。
外面的 $1/2$ 正好抵消两项之和的因子二。
这给出 (24.2)，包括 $k=0$ 时空的余和。

最后 $N_L\asymp L^3$，而 $(L+1)/N_L=O(L^{-2})$。
将 (24.2) 除以 $2^{-n}N_L$，即得 (24.4) 的第一个误差界。
所述时间范围内 $512^n=2^{9n}\le L^{2-9\epsilon}$，给出第二个界。
各常数可独立于这个范围内的 $n,L$ 选择。$\square$

$n=1$ 时 (24.2) 的误差严格为零，且
$T(1,L)=\sum_{\ell\le L}d_\ell h_\ell=[N_L+(-1)^L(L+1)]/2$。
$L=0$ 时 $T(n,0)=1$，对角项为 $2^{1-n}$；
$n=1$ 二者相等，$n\ge2$ 的差也满足 (24.2)。
作为 (24.10) 的另一直接读数，(24.12) 还给出

$$
\left|h_\ell^{-1}\|M_\ell^n\|_{\rm HS}^2-2^{-k}\right|
\le\frac{16^k}{h_\ell}(1-2^{-k}),\qquad k=n-1.
\tag{24.13}
$$

这些有限时间估计保留了全部自旋维数权重；它们没有估计临界时间窗。

## 25. 实际字支持上的系数普适正则转移成本

本节的 $\lambda_\Lambda$ 专指离散群 $\Lambda$ 在
$\ell^2(\Lambda)$ 上的左正则表示，与 (1.1) 的共同标量 $\lambda$
不同。对有限群代数元 $f=\sum_ga_gg$，记
$\|f\|_2=(\sum_g|a_g|^2)^{1/2}$，
$\tau(f)=a_e$，$\|f\|_1=\sum_g|a_g|$。
下面的系数可以是任意复数；实际字律仍是 (24.12) 中指定的等正系数。

**定理 25.1（实际支持的系数普适转移下界）。** 设 $\pi$ 是
$\Lambda$ 的任意非零 $d$ 维酉表示。对每个整数 $k\ge1$，

$$
\sup_{\substack{0\ne f\in\mathbb C[\Lambda]\\
\operatorname{supp}f\subseteq\mathcal W_k}}
\frac{\|\pi(f)\|}{\|\lambda_\Lambda(f)\|}
\ge\frac{2^{k/2}}{\sqrt{2d}\,(4k+1)}.
\tag{25.1}
$$

对原有限自旋 $\pi=\rho_\ell|_\Lambda$，在完整的 $V_\ell$ 上，
若 $n\ge3$、$k=n-1$、$0\le\ell\le L_n$，则右侧还至少为

$$
\frac{2^{n/3}}{8n}.
\tag{25.2}
$$

证明。先在同一个实际字支持上建立所需的正则模型比较。
取两个 $C^*$ 代数 $C^*(C_3)$，分别由 $d,c$ 生成，配以
规范迹 $\tau_i(u^a)=\mathbf1_{\{a=0\bmod3\}}$。
这些迹在有限维代数上忠实，故其 GNS 表示忠实。
其约化自由积作用正是 $C^*_r(\Lambda)$ 的左正则作用。
每个中心化因子的 $L^2$ 空间都有正交基 $u,u^2$；
约化音节字由这些基的交替张量构成正交基。

应用 Ricard–Xu, *Khintchine type inequalities for reduced free products
and applications*, [math/0505302v2](https://arxiv.org/pdf/math/0505302v2)，
Theorem 2.5 的 $(K_d)$。将该文的齐次次数改记为 $m$，
以免与表示维数 $d$ 混淆。它给出
$\|\lambda_\Lambda(f)\|\le(2m+1)\|\iota(f)\|$，
其中 $\iota$ 是该文 pp. 5–6 的辅助嵌入，不是直接的 $L^2$ 范数。
在这里还须检验其辅助范数。以下把这个检验在实际的两个三阶因子上写出。

固定音节次数 $m$ 的复标量系数元写成
$f=\sum_{|w|=m}a_ww$。
$\iota$ 的第一类分量把字在第 $p$ 个音节后切开，
以首段为行、倒序取逆的尾段为列，$0\le p\le m$。
对应矩阵的非零条目恰为 $a_w$；首段与尾段唯一恢复 $w$。
故该矩阵的 Hilbert–Schmidt 范数为 $\|f\|_2$，
算子范数至多这个值。行列的转置、逆序和共轭只改变正交基，
不改变此结论。

第二类分量保留第 $p+1$ 个音节在其因子代数内，
将前后两段分别变成行列，$0\le p<m$。
固定这个中间因子 $i$，把中间字母 $u,u^2$ 的系数矩阵分别记为
$F_{i,1},F_{i,2}$。唯一拼接性给出

$$
\|F_{i,1}\|_{\rm HS}^2+\|F_{i,2}\|_{\rm HS}^2
=\sum_{\substack{|w|=m\\w_{p+1}\text{ 属于因子 }i}}|a_w|^2
\le\|f\|_2^2.
\tag{25.3}
$$

该分量是 $F_{i,1}\otimes u+F_{i,2}\otimes u^2$。
$C^*(C_3)\simeq\mathbb C^3$，所以其空间张量范数由三个特征
$u\mapsto\zeta$、$\zeta^3=1$ 的算子范数的最大值给出。
逐个特征计算，

$$
\|\zeta F_{i,1}+\zeta^2F_{i,2}\|
\le\|F_{i,1}\|_{\rm HS}+\|F_{i,2}\|_{\rm HS}
\le\sqrt2\,\|f\|_2.
\tag{25.4}
$$

Ricard–Xu 嵌入的外层因子指标和各个切口都是 $\ell^\infty$ 直和，
取上确界，不再累加一个因子数。该文 p. 8 的保留中间因子实现
正是上述矩阵在 $C^*(C_3)$ 中的实现。
第一、第二类分量合并便有

$$
\|\iota(f)\|\le\sqrt2\,\|f\|_2,\qquad
\|\lambda_\Lambda(f)\|\le\sqrt2(2m+1)\|f\|_2.
\tag{25.5}
$$

此检验适用于任意复齐次标量系数，并非只适用于非负系数。
对 $\mathcal W_k$，音节次数是 $m=2k$，不是二元选择次数 $k$。
特别地，(24.12) 与正则表示作用于 $\delta_e$ 给出

$$
2^{-k/2}\le\|\lambda_\Lambda(b)^k\|
\le\sqrt2(4k+1)2^{-k/2},\qquad
r(\lambda_\Lambda(b))=2^{-1/2}.
\tag{25.6}
$$

下界使用 $\|b^k\|_2^2=2^k4^{-k}=2^{-k}$；
上下界取 $k$ 次根，并用有界算子的谱半径公式，给出最后一式。
(25.5)–(25.6) 是用于本定理的既有不等式之应用，
没有把正则范数结论转移给紧自旋。

现设 $N=2^k$，在 $\pi$ 的空间取正交基。
每个 $\pi(w)$ 酉，故

$$
\sum_{i,j=1}^d\sum_{w\in\mathcal W_k}|\pi(w)_{ij}|^2=Nd.
\tag{25.7}
$$

于是某个矩阵元满足
$A_{ij}:=\sum_{w\in\mathcal W_k}|\pi(w)_{ij}|^2\ge N/d>0$。
选择 $f=\sum_{w\in\mathcal W_k}\overline{\pi(w)_{ij}}\,w$。
此时 $\|f\|_2=\sqrt{A_{ij}}$，而
$\pi(f)_{ij}=A_{ij}$，所以 $\|\pi(f)\|\ge A_{ij}$。
由次数 $2k$ 的 (25.5)，

$$
\frac{\|\pi(f)\|}{\|\lambda_\Lambda(f)\|}
\ge\frac{\sqrt{A_{ij}}}{\sqrt2(4k+1)}
\ge\frac{2^{k/2}}{\sqrt{2d}(4k+1)}.
\tag{25.8}
$$

$f\ne0$；正则表示在有限群代数上忠实，因为其作用于 $\delta_e$
恢复全部系数，所以分母非零。这证明 (25.1)。

对原自旋，$n\ge3$ 时 $2^{n/3}\ge2$，因而
$d_\ell=2\ell+1\le2L_n+1\le2^{n/3}/2+1\le2^{n/3}$。
把 $k=n-1$ 代入 (25.1)，得到

$$
\frac{2^{(n-1)/2}}{\sqrt{2d_\ell}(4n-3)}
\ge\frac{2^{n/3-1}}{4n-3}
\ge\frac{2^{n/3}}{8n}.
\tag{25.9}
$$

这里必须使用整个 $V_\ell$：$H_\ell$ 不必受 $c$ 保持，
故不能把它当作 $\Lambda$ 的表示空间。$\square$

**推论 25.2（系数普适支配与精确等距压缩的边界）。** 任意非零有限维
$\pi$ 都不存在有限常数 $C_\pi$，使所有有限群代数元满足
$\|\pi(f)\|\le C_\pi\|\lambda_\Lambda(f)\|$。
因此 $\pi$ 不弱包含于 $\lambda_\Lambda$。
从紧正则表示移除有限个完整等型分量之后，其中心平凡部分仍不存在
这种对全部系数的正则范数支配，也不能通过到一个弱包含于
$\lambda_\Lambda$ 的表示的精确等距压缩来同时重现所有群酉算子。

证明。固定 $d$，(25.1) 的右侧随 $k$ 趋于无穷，给出第一项。
酉表示的弱包含范数判据要求对所有 $f\in\mathbb C[\Lambda]$
有 $\|\pi(f)\|\le\|\lambda_\Lambda(f)\|$，故亦被排除。
有限个完整紧等型分量的删除仍留下任意充分大的中心平凡自旋，
其中每个 $V_\ell$ 都作为有限维不变子表示出现。
若剩余直和有上述统一支配，每个子表示亦有，矛盾。

最后设 $V$ 是等距嵌入，$\sigma$ 是弱包含于正则表示的酉表示，
且对每个 $g\in\Lambda$ 都有 $V^*\sigma(g)V=\pi(g)$。
对任意向量 $v$，令 $P_V=VV^*$，则

$$
\|P_V\sigma(g)Vv\|=\|V\pi(g)v\|=\|v\|
=\|\sigma(g)Vv\|.
\tag{25.10}
$$

正交分解迫使 $(I-P_V)\sigma(g)Vv=0$，所以
$\sigma(g)V=V\pi(g)$；对 $g^{-1}$ 同样成立。
因此 $V$ 是交织算子，$\pi$ 是 $\sigma$ 的子表示，
便应弱包含于正则表示，与前面的结论矛盾。
剩余直和若有这样的等距压缩，限制到其中一个自旋子表示即得同一矛盾。
$\square$

(25.1) 的见证依赖 $\pi$，其系数未被要求非负、相等或在 $j$ 共轭下不变。
所以本节不反驳 $b^k$ 这一指定正等系数元的紧表示范数比较，
也不反驳加权平均迹的上界。
对压缩空间或仅对 $j$ 不变系数的比较另须论证，不能直接套用这个见证。
此外，令 $u=dc,v=dc^{-1}$，则
$u^{-1}v=c$、$(u^{-1}v)^3=e$。
它们的正半群单词虽互异，却不是自由群的一组自由生成元。
Kemp–Speicher [math/0512481v2](https://arxiv.org/pdf/math/0512481v2)
Theorem 1.3 要求 $*$-自由、同分布的 $R$-diagonal 族；
本模型没有建立这个条件。该文 Corollary 1.4 的自由群正生成元结果
也不能由正半群注入性移入这里。因此 (25.6) 没有使用更强的平方根型因子。

## 26. 实际压缩所必需的正交约化块增长

这里的正交约化分解指 Hilbert 空间的正交直和，每个块同时受算子及其
Hilbert 空间伴随保持。以下结论针对这种分解；不涉及非正交相似变换。

**定理 26.1（有限自旋的约化块下界）。** 设整数 $r\ge1$，置

$$
t=r^2+1,\qquad K=\frac{t(t+5)}2.
\tag{26.1}
$$

如果

$$
h_\ell\ge2\,t!\,2^{5K},
\tag{26.2}
$$

则 $B_\ell$ 和 $M_\ell$ 均不存在全部块维数至多 $r$ 的正交约化分解。
存在绝对常数 $c_*>0$，使充分大的 $\ell$ 的每种这种分解中，
最大块维数至少为 $c_*(\log(\ell+2))^{1/4}$。
从完整紧正则表示删除有限个完整等型分量之后，原 $P$ 及其
$J$ 不变空间上的压缩 $\mathsf B$ 也不存在维数一致有界的正交约化分解。

证明。在本模型的群代数中取

$$
x=b=ds,\qquad y=db=d^2s,\qquad s=(c+c^{-1})/2.
\tag{26.3}
$$

$x,y$ 在 $j$ 共轭下均不变。任意次数 $K$ 的 $x,y$ 单项式展开成
$2^K$ 个约化字，每字音节长度 $2K$，系数 $2^{-K}$。
确实，每个位置的 $d$ 音节是 $d$ 或 $d^2$，恢复该位置的 $x$ 或 $y$；
随后的 $c$ 音节是 $c$ 或 $c^{-1}$，恢复展开的符号选择。
相邻因子之间是 $c$ 音节接 $d$ 音节，没有约化抵消。
因此不同单项式的这些支持也互不相交。
这是实际 $c,d$ 的自由积正规形在此多项式上的应用。

令 $w_i=xy^ix$，$i=1,\ldots,t$，并取交替表达式

$$
F(x,y)=\sum_{\sigma\in S_t}\operatorname{sgn}(\sigma)
 w_{\sigma(1)}\cdots w_{\sigma(t)}.
\tag{26.4}
$$

每个单项式的次数都是 $\sum_{i=1}^t(i+2)=K$。
从 $xy^{\sigma(1)}xx y^{\sigma(2)}x\cdots x y^{\sigma(t)}x$
的 $y$ 连续段长度可以逐个恢复 $\sigma(1),\ldots,\sigma(t)$；
每个长度都至少一，故中间的两个 $x$ 是确定的分隔。
所以 (26.4) 有 $t!$ 个不同单项式。
再用上一段的互斥支持，展开后共有 $t!2^K$ 个不同群元素，
各系数为 $\pm2^{-K}$。由此精确得到

$$
\tau(F^*F)=\|F\|_2^2=t!2^{-K},\qquad
\|F\|_1=t!,\qquad \|F^*F\|_1\le(t!)^2.
\tag{26.5}
$$

最后一项使用群代数 $\ell^1$ 范数的次乘性，允许差字之间的重合。
$F^*F$ 在 $j$ 共轭下不变，支撑音节长度至多 $4K$。
因此 (24.10) 应用于这个实际群代数元，给出

$$
\left|\frac1{h_\ell}\operatorname{Tr}_{H_\ell}
 \rho_\ell(F^*F)|_{H_\ell}-t!2^{-K}\right|
\le\frac{2^{4K}(t!)^2}{h_\ell}.
\tag{26.6}
$$

$\rho_\ell(x)|_{H_\ell}=B_\ell$，
$\rho_\ell(y)|_{H_\ell}=U_\ell B_\ell$。
由于这些算子和伴随都保持 $H_\ell$，(26.6) 的迹正是
$\|F(B_\ell,U_\ell B_\ell)\|_{\rm HS}^2$。
(26.2) 使右侧至多 $\tfrac12t!2^{-K}$，所以

$$
\frac1{h_\ell}\|F(B_\ell,U_\ell B_\ell)\|_{\rm HS}^2
\ge\frac12t!2^{-K}>0.
\tag{26.7}
$$

若 $B_\ell$ 有全部维数至多 $r$ 的正交约化块，
每个块既受 $B_\ell$ 也受 $B_\ell^*$ 保持。
由 (23.6) 的有序多项式，$U_\ell$ 也保持每个块，
故 $B_\ell,U_\ell B_\ell$ 及全部 $w_i$ 均保持它。
在维数 $s_0\le r$ 的一个块上，$t=r^2+1>s_0^2$ 个矩阵 $w_i$
在 $s_0^2$ 维的复矩阵空间内线性相关。

为明确交替步骤，映射
$(Z_1,\ldots,Z_t)\mapsto\sum_{\sigma}\operatorname{sgn}(\sigma)
Z_{\sigma(1)}\cdots Z_{\sigma(t)}$
对每个输入线性；两个输入相等时，把排列按交换这两个输入配对，
两项符号相反而乘积相同，故为零。
线性相关时，将一个非零系数对应的输入表示为其余输入的线性组合，
再按该输入展开，每项都有重复输入，因而仍为零。
于是 (26.4) 在每个小块上为零，在整个正交直和上亦为零，
与 (26.7) 矛盾。这证明 $B_\ell$ 的结论。

若 $M_\ell$ 有这样的约化分解，则
$M_\ell^*M_\ell=Q_\ell$ 也保持每个块。
每个块因此按 $Q_\ell$ 的像和核正交分开；其与 $H_\ell$ 的交
组成 $H_\ell$ 的正交分解，每个交的维数至多 $r$。
压缩 $Q_\ell M_\ell Q_\ell|_{H_\ell}=B_\ell$ 及其伴随
保持这些交，给出已被排除的分解。

还须将阈值转成增长率。$h_\ell\ge\ell$，而 $r\ge1$ 时
$t\le2r^2$、$t+5\le7r^2$，从而 $K\le7r^4$。
又 $\log_2(t!)\le t\log_2t\le t^2\le4r^4$，故

$$
\log_2(2t!2^{5K})=1+\log_2(t!)+5K\le40r^4\le42r^4.
\tag{26.8}
$$

对充分大的 $\ell$ 取
$r=\lfloor(\log_2\ell/42)^{1/4}\rfloor\ge1$，
则 $h_\ell\ge\ell\ge2^{42r^4}$，满足 (26.2)。
所以每个分解的最大块维数大于 $r$。
利用 $\lfloor u\rfloor\ge u/2$（$u\ge2$）和
$\log\ell\ge\tfrac12\log(\ell+2)$（充分大的 $\ell$），
例如可取 $c_*=[2(84\log2)^{1/4}]^{-1}$。
这是充分下界，不宣称阈值尖锐。

最后处理完整等型直和，不能预设未知约化块与自旋对齐。
在 $\mathcal H_J$ 上，原完整压缩仍满足

$$
\mathsf B=T_D\mathsf S,\qquad
\mathsf B^*\mathsf B=\mathsf S^2,\qquad
T_D|_{\mathcal H_J}
=\mathsf B(4\mathsf B^*\mathsf B-3I).
\tag{26.9}
$$

这是 (20.3)–(20.5) 中两谱值及酉性的同一代数计算，
并未把 $T_D$ 换成 $T_{iD}$。
这些等式也限制到任意固定完整等型截断后的
$\mathcal H_{J,\Pi}$。如果该空间的 $\mathsf B$ 有维数至多 $r$
的正交约化块，(26.9) 以及刚才的矩阵空间维数和交替论证迫使
$F(\mathsf B,T_D\mathsf B)=0$。
但有限个完整等型分量的删除留下所有充分大的中心平凡自旋。
其任意一个 $H_\ell$ 副本上，这个表达式恰为
$F(B_\ell,U_\ell B_\ell)$，由 (26.7) 非零，矛盾。
这一限制只用于检出多项式非零，不要求原来的小块与自旋副本对齐。
若 $P|_{\ker\Pi}$ 有一致有界约化块，用 $P^*P=Q$ 和相同的
像核分解便得到 $\mathsf B$ 的一致有界块，亦矛盾。
$\square$

例如 $r=1$ 时 $t=2,K=7$，充分条件是 $h_\ell\ge2^{37}$；
$r=2$ 时 $t=5,K=25$，充分条件是 $h_\ell\ge240\,2^{125}$。
本证明使用实际字的互斥正规形和正交约化块的多项式恒等式，
没有从最小多项式次数推断块维数。
它允许随 $\ell$ 增长的约化块，也不排除任何非正交相似分块，
更不单独给出幂范数的增长或衰减界。

## 27. 临界实际有符号余和与文献对应

由 (24.3) 可把原目标所缺的量精确隔离，而不改变字律。
对 $n\ge1$、$k=n-1$、$L\ge0$ 定义

$$
\mathcal R(n,L)=\frac1{2\,4^k}
\sum_{\substack{w,v\in\mathcal W_k\\w\ne v}}
\bigl[\mathcal D_L(w^{-1}v)+\mathcal D_L(w^{-1}vj)\bigr].
\tag{27.1}
$$

这个实数和保留每个有序对；不同差字的相同值仍以原重数计入。
字的系数相等且为正，核的值则可以有正有负。
在原临界截断 $L_n=\lfloor2^{n/3}/4\rfloor$ 上，精确地

$$
\mathcal S_n=T(n,L_n)
=2^{-n}\bigl[N_{L_n}+(-1)^{L_n}(L_n+1)\bigr]
 +\mathcal R(n,L_n).
\tag{27.2}
$$

由于 $L_n/2^{n/3}\to1/4$，$N_L=(4/3)L^3+O(L^2)$，

$$
2^{-n}\bigl[N_{L_n}+(-1)^{L_n}(L_n+1)\bigr]\longrightarrow\frac1{48}.
\tag{27.3}
$$

而常数自旋给出 $\mathcal S_n\ge1$，因此

$$
\mathcal R(n,L_n)\ge\frac{47}{48}+o(1).
\tag{27.4}
$$

所以不能把目标换成“非对角余项趋于零”。
所需的是 (27.1) 这个实际等系数有符号和的次指数单侧上界：
存在 $u_n\ge1$、$\log u_n=o(n)$ 使
$\mathcal R(n,L_n)\le u_n$。
由于 (27.3) 有界且 $\mathcal S_n\ge1$，这个要求等价于
$\log\mathcal S_n=o(n)$：一个方向把有界对角项加回去，
另一个方向用对角项非负，故 $\mathcal R(n,L_n)\le\mathcal S_n$。
此上界仍未证明。

短时间结论 (24.4) 只适用于
$n\le(2/9-\epsilon)\log_2L$；原临界关系却是
$n=3\log_2L_n+6+o(1)$。
若把其中的主项渐近式直接延伸到临界关系，就会与
(27.3) 和 $\mathcal S_n\ge1$ 矛盾。
逐项绝对估计 (24.2) 在临界处亦不能供应所需的次指数上界：
其右侧含 $256^{n-1}(4L_n+1)$。
需要控制的是共同实现下整个有符号和的上方，而不是先把所有核值取绝对值。

与原配对问题的回接直接采用 (19.14)，不更换任何常数：
对 $n\ge18$，$a_0=1/(12\sqrt2\pi)$，

$$
\frac{Q_n}{128\pi^2}\le\mathcal S_n
\le\frac{18522\pi^2}{32a_0}Q_n.
\tag{27.5}
$$

因此 (19.28) 的必要充分接口、(15.3) 的全固定尺度族接口及
(15.7) 的原球向量接口原样适用。
这里不重复证明这些已给出的供应结果；
$128\pi^2$、$18522$、原球半径和每条历史的质量均保持原义。
第 21 节对每个紧开子群的直接正双陪集障碍仍成立，
(23.3) 的群结构复用没有消除它。

本增补的来源对应如下。

| 供应与精确位置 | 在实际模型中的用途和条件 |
| --- | --- |
| 母文 Proposition 45.3；环境记忆卷 Theorems 10.1、12.2 | 复用自由积、$j$ 的作用与外部性，以及旋转群识别；实际生成元的正反替换是 (23.2)，并非 $c=[R_0]$ |
| Radin–Sadun, *Subgroups of SO(3) Associated with Tilings*, [math/9601202v1](https://arxiv.org/pdf/math/9601202v1), Theorem 1(i),(ii), Corollary 2，PDF p. 3；Journal of Algebra **202**, 611–633，DOI [10.1006/jabr.1997.7320](https://doi.org/10.1006/jabr.1997.7320) | 垂直轴旋转：奇数阶 $(3,3)$ 的自由积，以及偶数阶/奇数阶 $(6,3)$ 的合并积。它们是已用群供应的文献依据，不给紧表示范数转移 |
| Radin–Sadun, *On 2-generator subgroups of SO(3)*, [math/9706203v2](https://arxiv.org/pdf/math/9706203v2), Theorem 2 cases 1,2，式 (15),(16)，PDF p. 6 | 相同垂直轴条件下的两种表示式。以 $x=dj,c$ 为六阶/三阶旋转，一次共同空间旋转对应文中的两条轴；其结论不供应配对能量界 |
| Ricard–Xu, [math/0505302v2](https://arxiv.org/pdf/math/0505302v2), §1 的忠实 GNS 条件，Lemmas 2.1–2.3、Corollary 2.4、pp. 5–6 的 $\iota$ 与 Theorem 2.5 $(K_d)$，p. 8 的中间因子实现 | 两个带规范忠实迹的 $C^*(C_3)$、齐次约化音节次数 $m=2k$；(25.3)–(25.5) 另行检验标量辅助范数，才得到 (25.6) 及系数任意的 (25.8) |
| Kemp–Speicher, *Strong Haagerup inequalities for free R-diagonal elements*, [math/0512481v2](https://arxiv.org/pdf/math/0512481v2), Definition 1.2、Theorem 1.3、Corollary 1.4，PDF pp. 2–4 | $*$-自由同分布 $R$-diagonal 族或自由群正生成元的条件没有在这里建立；该不等式不作为本增补的供应 |
| 本卷 (19.2)–(19.3)、(19.9)–(19.14)、(19.25)–(19.28)、(20.1)–(20.13) | 复用中心平凡自旋、维数权重、原时间幂、临界等价与完整相位压缩；本增补在这些对象内推导重数、整数高度加权迹及两种具体路线的障碍 |

(23.5)–(23.9) 是实际 $S_3$ 压缩的有限表示计算；
(24.2)–(24.13) 是实际生成元整数高度、维数加权核和原历史恒等式的推导；
(25.1)–(25.10) 把既有正则不等式用于实际支持上的系数普适比较；
(26.2)–(26.9) 用实际 $d,d^2$ 音节和有限自旋迹排除一致小约化块。
一般自由积不等式与一般交替多项式事实仅是这些应用中的中间工具。
这些普通数学推导不声称全局原创性、优先权或形式内核认证。

原临界估计 $\log\mathcal S_n=o(n)$ 仍未解决。
第 16 节及 (20.9) 对固定有限完整等型截断的完整复空间统一幂条件，
也没有被上述有限自旋结构、任意复系数见证或约化块增长证明或反驳。
所有四个中心扇区仍属于这个较强条件的量词。
任意时域的匹配记忆律、完整有限联合恢复律以及物理实现均仍需原有的
独立数学与实现条件；短时间窗不将这些目标结算。

## 追加锚（本行以下为增补区）
