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
\(\mathbb Q(\sqrt3,i)\) 中的精确有限代数；第 14–15 节给出独立的度量和
计数证明；第 16 节明确标为尚未证明的充分供应条件。它们都不是 Lean
核验、全局认证或对前文状态的重写。所有实际历史、相位、重数、闭事件和
两个行列式分量继续按第 1 节保留。

## 13. 完整 \(S^3\) 上的有限表示见证与 \(\gamma_{22}\) 的方向

仍取第 2 节的同一个 \(A=A_g\)、\(J\)、\(J_j=A^{-j}JA^j\) 以及
\(C_1=J_0J_1\)、\(C_2=J_1J_2\)。直接相乘得到

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

这两个矩阵属于 \(SU(2)\)，且 \(C_j^{-1}=C_j^\dagger\)。令

$$
X=\frac18\begin{pmatrix}6&-5\sqrt3+9i\\-5\sqrt3-9i&-6\end{pmatrix}.
\tag{13.2}
$$

则 \(X=X^\dagger\)、\(\operatorname{tr}X=0\)、\(X^2=3I_2\)，并且逐项有限
相乘给出

$$
\frac14\left(C_1XC_1^\dagger+C_1^\dagger XC_1\,+C_2XC_2^\dagger+C_2^\dagger XC_2\right)=\frac58X.
\tag{13.3}
$$

为说明 (13.3) 的有限代数内容，可用 Pauli 基底
\(\sigma_x,\sigma_y,\sigma_z\) 写共轭作用的实三维矩阵。四项对称平均为

$$
M=\frac1{256}
\begin{pmatrix}
25&63\sqrt3&-18\sqrt3\\
63\sqrt3&-5&-90\\
-18\sqrt3&-90&-20
\end{pmatrix},
$$

而 \(q=(-5\sqrt3,-9,6)^{\mathsf T}\) 满足 \(Mq=\frac58q\)。这与
(13.2) 的坐标完全相同，故 (13.3) 是精确等式而非浮点特征值判断。

在完整单位球面 \(S^3\subset\mathbb C^2\) 上，对任意矩阵记
\(v_X(z)=z^\dagger Xz\)，并取

$$
v(z)=z^\dagger Xz
=\frac34(|z_1|^2-|z_2|^2)
+\frac14\operatorname{Re}\!\left[(-5\sqrt3+9i)\overline z_1z_2\right].
\tag{13.4}
$$

对 \(z_1=\sqrt t\,e^{i\alpha}\)、\(z_2=\sqrt{1-t}\,e^{i\beta}\)，归一化球面
测度为 \(dt\,d\alpha\,d\beta/(2\pi)^2\)。相位积分消去交叉项，故

$$
\int_{S^3}v\,dm=\frac34\int_0^1(2t-1)\,dt=0.
$$

同样计算平方，令 \(B=-5\sqrt3+9i\)，则 \(|B|^2=156\)，从而

$$
\begin{aligned}
\|v\|_2^2
&=\frac{36}{64}\int_0^1(2t-1)^2dt
+\frac{2\cdot156}{64}\int_0^1t(1-t)dt\\
&=\frac{36}{64}\cdot\frac13+\frac{312}{64}\cdot\frac16=1.
\end{aligned}
\tag{13.5}
$$

函数 \(v\) 是完整 \(S^3\) 上的非零、均值零、范数一的复 \(L^2\) 函数。对
\(\mathsf U_gv(z)=v(g^{-1}z)\)，有
\(\mathsf U_gv_X=v_{gXg^\dagger}\)。因此 (13.3) 在原来的完整球面作用中给出

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

中的上界方向；正性沿用前文已明确标出的供应前提。没有证明 \(\gamma_{22}=3/8\)，
没有证明它是全空间最小商，也没有得到独立的正下界。特别地，不能把
\(3/8\) 当作 P1–P4 所需的谱隙下界。

若只在继承的 \(0<\gamma=\gamma_{22}\le1\) 和前文条件包络下工作，
\(\kappa=1-\gamma/2\)、\(\widehat\xi=-\ln\kappa\) 满足

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

对任意 \(\widehat a<a<h_*\)，同一条件包络的线性支满足

$$
3a>a+\widehat\xi(1-a/h_*),
\qquad
h_*>a+\widehat\xi(1-a/h_*),
$$

所以该包络在这一区间严格低于目标 \(\min\{3a,h_*\}\)。尤其
\(a_*<a<h_*\) 对所有与 (13.7) 相容的正 \(\gamma\) 都未被这个包络匹配。
这只是供应包络的未消除区间；它不是原目标的反例。原始的每个固定
\(a,c>0\) 的全尺度目标和完整有限联合恢复目标仍为 **OPEN**。相应地，
若沿用前文的率变量 \(\widehat\beta=2\widehat a\)，则
\(\widehat\beta\le2a_*\)，其条件操作率的未匹配区间仍为
\(\widehat\beta<\beta<2h_*\)。

## 14. 任意概率律的三维紧群几何不等式

下面的引理对 \(K=SU(2)\sqcup SU(2)J\) 上任意概率律 \(\nu\) 成立，因而不把
有限实际字律替换成 Haar 律。取常数 \(a_0,b_0>0\)，使得由第 5 节的
体积公式，在 \(0<s\le1/2\) 时

$$
a_0s^3\le V(s)\le b_0s^3.
\tag{14.1}
$$

**引理 G。** 存在绝对常数 \(C_G\)，使得对所有充分小的
\(0<\delta\le1/8\)、所有 \(0\le r\le1/8\) 以及 \(K\) 上任意概率律 \(\nu\)，

$$
E_\nu(r):=(\nu\times\nu)\{(x,y):d(x,y)\le r\}
\le C_G(1+r/\delta)^3E_\nu(\delta).
\tag{14.2}
$$

证明如下。取一个极大的 \(\delta/2\)-分离有限网
\(\{x_i\}_{i\in I}\)。紧性保证有限性，极大性保证每个点在某个
\(B_{\delta/2}(x_i)\) 内。按最小指标打破平局，得到可测分割
\(K=\bigsqcup_iA_i\)，且 \(A_i\subseteq B_{\delta/2}(x_i)\)，故
\(\operatorname{diam}A_i\le\delta\)。置 \(p_i=\nu(A_i)\)。闭事件的边界
不被删除，因为同一 cell 中的每一对点都满足 \(d(x,y)\le\delta\)，所以

$$
\sum_i p_i^2\le E_\nu(\delta).
\tag{14.3}
$$

若 \(x\in A_i\)、\(y\in A_j\) 且 \(d(x,y)\le r\)，则
\(d(x_i,x_j)\le r+\delta\)。对固定 \(i\) 令
\(N_i=\{j:d(x_i,x_j)\le r+\delta\}\)。网点间的关系是对称的。由于
\(r+\delta<2\)，相反行列式分量的网点不可能同时出现在 \(N_i\) 中；因此
所有这些小球留在同一个三维分量内。网点的开球
\(B_{\delta/4}(x_j)\) 两两不交，并包含于
\(B_{r+5\delta/4}(x_i)\)。当 \(\delta\) 足够小时，(14.1) 给出

$$
|N_i|\,a_0(\delta/4)^3
\le b_0(r+5\delta/4)^3
\le C_0(1+r/\delta)^3\delta^3,
\tag{14.4}
$$

其中 \(C_0\) 与 \(\nu,r,\delta\) 无关。于是最大对称邻居度满足
\(\max_i|N_i|\le C_0(1+r/\delta)^3\)。再由
\(p_ip_j\le(p_i^2+p_j^2)/2\)，并按有序邻居求和，得到

$$
\begin{aligned}
E_\nu(r)
&\le\sum_i\sum_{j\in N_i}p_ip_j\\
&\le\sum_i|N_i|p_i^2
\le C_0(1+r/\delta)^3\sum_i p_i^2.
\end{aligned}
$$

结合 (14.3) 即得 (14.2)。当 \(r=0\) 时直接由单元对角项和
\(E_\nu(0)\le E_\nu(\delta)\) 得到结论；因此 (14.2) 包括闭边界和
\(0\le r\) 的端点。

对实际长度 \(n\) 的律 \(\nu_n=\mu^{*n}\)，置

$$
\delta_n=2^{-n/3},\qquad Q_n=2^nE_n(\delta_n).
\tag{14.5}
$$

当 \(n\) 足够大使 \(\delta_n\) 落入引理 G 的范围时，
\(\delta_n^3=2^{-n}\) 和
\((1+x)^3\le4(1+x^3)\) 给出统一的几何界

$$
E_n(r)\le C\,Q_n(2^{-n}+r^3)
\qquad(0\le r\le1/8),
\tag{14.6}
$$

其中 \(C\) 为绝对常数。这个界只使用实际律的 cell 质量，保留了所有
历史重数。

## 15. 临界尺度、平滑二范数与精确尾字计数

先证明临界尺度与原全尺度陈述的等价性。若
\(Q_n\le e^{o(n)}\)，把 \(r=ce^{-an}\) 代入 (14.6)，固定的 \(a,c>0\)
给出

$$
E_n(ce^{-an})\le e^{o(n)}\bigl(e^{-3an}+2^{-n}\bigr).
\tag{15.1}
$$

反过来，在原目标中取 \(a=h_*/3\)、\(c=1\)，便有
\(ce^{-an}=\delta_n\)，所以

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

这里的 \(o(n)\) 可依赖所固定的 \(a,c\)；(14.6) 中的常数 \(C\) 是统一的。
这只是等价改写，不是临界假设的证明。

令 \(f_{n,s}=P^nb_s\)。由实际前向卷积和闭球交叠的逐项展开，

$$
\|f_{n,s}\|_2^2
=4^{-n}\sum_{h,g}
\frac{m_K(B_s(G_h)\cap B_s(G_g))}{V(s)^2}.
\tag{15.4}
$$

若中心距离不超过 \(r\)，则 \(B_r(G_h)\) 落在两个
\(B_{2r}\) 球的交中；反之，交叠非空时中心距离不超过 \(2s\)。取
\(s=2\delta_n\)，并用 (14.1)，得到充分大 \(n\) 时的两侧关系

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

第一式直接来自 (15.4)：若 \(d(G_h,G_g)\le r\)，则
\(B_r(G_h)\subseteq B_{2r}(G_h)\cap B_{2r}(G_g)\)，故

$$
E_n(r)\le\frac{V(2r)^2}{V(r)}\|P^nb_{2r}\|_2^2.
$$

在 \(r=\delta_n\) 时，由 \(2^n\delta_n^3=1\) 及 (14.1)，
\(2^nV(2\delta_n)^2/V(\delta_n)\le64b_0^2/a_0\)，即得 (15.5)。
第二式来自 (15.4) 中交叠质量至多 \(V(2\delta_n)\)，再把 (14.6)
用于 \(4\delta_n\)。故

$$
Q_n\le e^{o(n)}
\quad\Longleftrightarrow\quad
\|P^nb_{2\delta_n}\|_2^2\le e^{o(n)}.
\tag{15.7}
$$

现在给出不带取整的尾字等式。对 \(m\ge0\) 保持第 8 节实际尾字集合
\(\mathcal T_m\) 和有序计数

$$
D_m(R)=\#\{(W,V)\in\mathcal T_m^2:N(W-V)\le R\}.
$$

第 8 节的实际时间字典把长度 \(n=m+1\) 的每个奇偶类逐一对应于
\(\mathcal T_m\)，并保留每条历史的质量 \(2^{-(m+1)}\)。同一奇偶类的
距离平方为 \(2\,4^{-m}N(W-V)\)，两类之间的距离恰为 \(2\)。因为
\(\delta_{m+1}<2\)，异奇偶项不进入临界闭球，故精确地

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

所以，不作 floor 或半径舍入，保留 \(m=n-1\)，有

$$
\boxed{
Q_{m+1}=2^{-m}D_m\!\left(2^{(4m-5)/3}\right)
}\qquad(m\ge0).
\tag{15.9}
$$

端点 \(m=0\) 也在此式中成立：约定 \(D_0(R)=1\)（\(R\ge0\)），则
\(Q_1=1\)。式 (15.9) 是实际有序尾对、对角项、原时间顺序和奇偶
分量的精确字典，不是整壳均匀律。

同样，若 \(k+\ell=n\)，把实际历史按时间写成 \(XY\)，其中
\(X\sim\mu^{*\ell}\) 是最后 \(\ell\) 个字母的乘积，
\(Y\sim\mu^{*k}\) 是最初 \(k\) 个字母的乘积。对两份独立历史
\(X'Y'\)，双不变性给出严格的时间顺序恒等式

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

下面的条件是一个保留原非对称算子 \(P=UQ_0\) 的充分供应者，当前不声称
它对这些生成元成立。令 \(\Pi\) 是 \(L^2(K;\mathbb C)\) 中有限个完整
Peter–Weyl 左正则等型分量的正交投影，包含常数分量和 \(\chi\) 分量；记
其有限秩为 \(d_\Pi\)。假定存在 \(s_n\ge1\)，\(\log s_n=o(n)\)，使

$$
\|P^n(I-\Pi)\|_{2\to2}^2\le s_n\,2^{-n}
\qquad(n\ge1).
\tag{16.1}
$$

这是未证明的充分条件，涉及原来的非正规前向算子及固定有限异常空间，
不是谱半径结论、对称化行走结论或 Shannon 熵结论。

为说明它确实足以供应临界二范数，取任一完整等型分量的标准正交基，
有限和的 reproducing kernel 对角线恒为 \(d_\Pi\)：左不变性使其为常数，
积分后常数正是秩。因此对任意非负概率密度 \(f\)，

$$
\|\Pi f\|_2
=\left\|\int_K f(x)(\phi_a(x))_a\,dm_K(x)\right\|_2
\le\int_K f(x)\left(\sum_a|\phi_a(x)|^2\right)^{1/2}dm_K(x)
\le\sqrt{d_\Pi}.
\tag{16.2}
$$

投影 \(\Pi\) 与每个左平移、因而与原来的 \(P\) 交换。对
\(f=b_{2\delta_n}\)，由 (14.1) 有
\(\|f\|_2^2=V(2\delta_n)^{-1}\le C_3\,2^n\)。于是 (16.1)–(16.2)
以及 \((a+b)^2\le2a^2+2b^2\) 给出

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
\(Q_n\le e^{o(n)}\)，进而蕴含原全尺度目标。条件 (16.1) 本身仍是
**UNPROVED sufficient supplier**；它没有被当作实际算子的已证性质，也没有
改变主目标仍为临界配对能量这一事实。

## 17. \(\gamma\) 见证与实际局部恢复误差的有限对应

这里仅复用固定有限二元 CPTP 定理 59.2 及其在编码 qutrit 上的已发表
应用。为固定生成元与该应用的时间对应，仍取 \(A=A_g\)、
\(g_0=A,g_1=AJ\)。同长度的共同相位消去后，约定相对矩阵为
\(F_h^{-1}F_k=G_h^{-1}G_k\)。由 \(J_j=A^{-j}JA^j\)、\(J_j^2=I\)
以及 (1.2) 的实际时间顺序，有

$$
\begin{aligned}
G_{00}^{-1}G_{11}
&=A^{-2}(AJ)(AJ)=A^{-1}JAJ=J_1J_0=C_1^{-1},\\
G_{000}^{-1}G_{101}
&=A^{-3}(AJ)A(AJ)=A^{-2}JA^2J=J_2J_0=(C_1C_2)^{-1}.
\end{aligned}
$$

这里 \(C_1C_2=J_0J_1^2J_2=J_0J_2\)。由 (13.1) 的精确矩阵及
\(SU(2)\) 中逆矩阵与原矩阵的迹相同，

$$
\frac12\operatorname{tr}(J_2J_0)
=\frac12\operatorname{tr}(C_1C_2)=\frac58.
$$

因此实际同一组 \(A,J\) 的等奇偶历史 \(000,101\) 在编码 qutrit 的
相对矩阵中满足 \(\cos\theta=5/8\)。对固定且输入无关的公平权重
\(p=q=1/2\)，定理 59.2 的数值域距离为 \(\nu=\cos\theta=5/8\)，故

$$
\delta_{1/2}(U)
=1-\sqrt{1-4(1/2)(1/2)(1-\nu^2)}
=1-\nu=\frac38.
\tag{17.1}
$$

这是实际 \(000/101\) 这一固定记录、固定公平权重、编码 qutrit 范围内的
**条件 recovery error**。它与 (13.6) 的测试 Rayleigh 商同为
\(1-5/8=3/8\)。因此在这个具体有限代数实例中可以写成

$$
\gamma_{22}\ \le\ \underbrace{\frac38}_{\text{测试商}}
=\underbrace{\frac38}_{\text{实际 }000/101\text{ 的条件局部误差}}.
\tag{17.2}
$$

等号右侧的局部解释依赖定理 59.2 的固定输入无关公平权重和编码 qutrit
嵌入；它不涉及全局控制器、历史相关的最优记录、全体记忆宽度或终端
CPTP 家族的全局最优。也不允许把公平权重改为输入依赖 Born 权重，或把
这个角度推广为任意角度的谱隙—恢复等式。式 (17.2) 的唯一谱隙结论仍是
变分定义给出的上界 \(\gamma_{22}\le3/8\)，而非一般的谱隙与恢复误差
相等定理。

## 18. 工具、来源相对性与未解决目标

本补充使用的工具是标准的矩阵系数与 Rayleigh 商计算、紧群上的
Peter–Weyl 分解、最大分离网与 Cauchy–Schwarz 邻居计数、Haar 小球体积
比较，以及第 59.2 节的有限二元 CPTP 定理。它们在这里按实际
\(A,J\)、实际时间顺序和实际公平字律应用；没有用 Haar 字律替换有限历史，
也没有把与本字母表不相符的 entropy 或 golden-gate 方案作为定理前提。
这些陈述是来源相对的普通数学草稿，不作全局原创性或文献穷尽声明。

目前保留的主问题仍是：对同一实际独立公平历史、相位、重数、闭有序配对
事件，证明每个固定 \(a,c>0\) 的 (9.1)，以及在其基础上的完整有限
\((n,\varepsilon)\) 联合恢复律。有限表示见证排除了同一条件包络中
\(\gamma_{22}=1\) 的分支，却没有证明或否定临界能量估计。有限异常
Peter–Weyl 条件 (16.1) 是可检验的额外路线，尚未在实际算子上得到。

## 追加锚（本行以下为增补区）

