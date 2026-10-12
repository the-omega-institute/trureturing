# Auric FIB-ATOM：带符号阶乘核、黄金阈值与共同 Gram 相容性

## 1. 原始阶乘来源与累计供应

**定义 1.1（同一阶乘余项与完整高段响应）。** 全文使用自然对数，令 $\ell=\log2$，并对 $y\ge1$ 定义

$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad
C(Y)=\int_1^Y\frac{\eta(y)}{y^2}\,dy\quad(Y\ge1).
$$

对 $r>0$，定义

$$
h(r)=\int_1^\infty\frac{\eta(y)}{y^2}
\left[\frac1{r+\log y}+\frac1{(r+\log y)^2}\right]dy.
\tag{1.1}
$$

这里保留完整的有符号 $\eta$、整个积分域及两个核项。这些定义对应 [ActualFactorialRobinHighDerivative 的 `eta_factorial`、`highKernel_formula` 与 `highRemainder`](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative.lean)。下文所有平移和差分都作用于式 (1.1) 的这个函数。

**约定 1.2（所用累计估计）。** 采用上述来源的 `eta_high` 以及 [ActualFactorialCumulativePositivity 的 `result`](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/D5/S3/Arith/Robin/ActualFactorialCumulativePositivity.lean) 给出的同对象估计：

$$
|\eta(y)|\le1+\log y\quad(y\ge1),
\tag{1.2}
$$

$$
\frac{\log Y}{Y}\le C(Y)
\le2-\frac{\log Y+2}{Y}<2\quad(Y\ge1),
\tag{1.3}
$$

$$
C(1)=0,\qquad C(2)=\log2-\frac{(\log2)^2}{2}.
$$

置

$$
c_{\mathrm{fac}}=\frac{\log2(1-\log2)}2>0.
$$

当 $Y\ge2$ 时，还有

$$
C(Y)\ge c_{\mathrm{fac}}+\frac{\log Y}{Y}.
\tag{1.4}
$$

同一供应中的积分表示及严格界为

$$
h(r)=\int_0^\infty C(e^u)
\left[\frac1{(r+u)^2}+\frac2{(r+u)^3}\right]du,
\tag{1.5}
$$

$$
c_{\mathrm{fac}}\left[\frac1{r+\ell}+\frac1{(r+\ell)^2}\right]
<h(r)<2\left(\frac1r+\frac1{r^2}\right).
\tag{1.6}
$$

这些累计供应作为后续谱表示的前提使用；它们没有要求 $\eta$ 逐点非负。

## 2. 有限阶乘公式与正累计的局部边界

**命题 2.1（有限阶乘累计公式）。** 对 $Y\ge1$，令 $n=\lfloor Y\rfloor$，空和取零，则

$$
C(Y)=\sum_{j=2}^{n}\frac{\log j}{j}
-\frac{\log(n!)}Y-\frac12(\log Y)^2+\log Y.
\tag{2.1}
$$

特别地，$7!=5040$ 给出

$$
C(7)=\sum_{j=2}^{7}\frac{\log j}{j}
-\frac{\log5040}{7}-\frac12(\log7)^2+\log7.
\tag{2.2}
$$

证明。有限阶乘恒等式

$$
\log(\lfloor y\rfloor!)=\sum_{j=2}^{n}\log j\,\mathbf1_{[j,Y]}(y)
\quad(1\le y\le Y)
$$

允许有限求和与积分交换，因而

$$
\int_1^Y\frac{\log(\lfloor y\rfloor!)}{y^2}\,dy
=\sum_{j=2}^{n}\log j\left(\frac1j-\frac1Y\right).
$$

另外，$\int_1^Y(1-\log y)y^{-1}dy=\log Y-(\log Y)^2/2$，相加即得。$\square$

**命题 2.2（正累计不要求局部正密度）。** 存在 $\delta\in(0,1)$，使得 $\eta(y)<0$ 对全部 $8-\delta<y<8$ 成立，而 $\eta(8)>0$。因此 $C$ 在该左邻域严格递减，同时仍满足 $C(Y)>0$ 对全部 $Y>1$ 成立。

证明。在 $(7,8)$ 上，$\eta(y)=\log5040-y\log y+y$，其左极限为

$$
L=\log5040-8\log8+8.
$$

由指数级数，$e=\sum_{k=0}^\infty1/k!\le5/2+(1/6)\sum_{j=0}^\infty4^{-j}=49/18<11/4$；而整数恒等式

$$
8^8\,4^8-5040\,11^8=19142867536>0
$$

给 $5040e^8<8^8$，故 $L<0$。连续性给所需左邻域。另一方面，$\log x$ 严格递增，所以

$$
\log(8!)=\sum_{j=2}^{8}\log j
>\int_1^8\log x\,dx=8\log8-7,
$$

从而 $\eta(8)>1$。在上述左邻域，$C'(y)=\eta(y)/y^2<0$；全域正性则由式 (1.3) 给出。于是 $C$ 为正不等于 $dC$ 为正测度。$\square$

## 3. 同源正谱密度与全部阶数的符号

**定义 3.1（累计的 Laplace 密度）。** 令 $A(u)=C(e^u)$，$u\ge0$，并对 $t>0$ 定义

$$
\omega(t)=t(1+t)\int_0^\infty A(u)e^{-tu}\,du.
\tag{3.1}
$$

由式 (1.3)，$A(0)=0$ 且 $0<A(u)<2$ 对 $u>0$ 成立。称 $f:(0,\infty)\to\mathbb R$ 完全单调，是指 $f\in C^\infty$ 且 $(-1)^nf^{(n)}(r)\ge0$ 对全部整数 $n\ge0$ 和 $r>0$ 成立；若每项严格为正，则称严格完全单调。

**定理 3.2（原始有符号高段的正谱表示）。** $\omega$ 在 $(0,\infty)$ 连续，并满足

$$
0<\omega(t)<2(1+t),
\qquad
\omega(t)=1-\frac1{t^2}-\zeta'(1+t).
\tag{3.2}
$$

式 (1.1) 的同一高段函数具有绝对收敛表示

$$
h(r)=\int_0^\infty e^{-rt}\omega(t)\,dt,
\tag{3.3}
$$

而且对每个 $n\ge0$，

$$
(-1)^nh^{(n)}(r)=\int_0^\infty t^ne^{-rt}\omega(t)\,dt>0.
\tag{3.4}
$$

证明。首先，式 (1.2) 给出

$$
\int_1^\infty\frac{|\eta(y)|}{y^2}\,dy
\le\int_1^\infty\frac{1+\log y}{y^2}\,dy=2.
\tag{3.5}
$$

这同时保证式 (1.1) 绝对收敛、$C$ 局部绝对连续和 $|C|\le2$。为明确与原来源的等式，置

$$
B_r(y)=\frac1{r+\log y}+\frac1{(r+\log y)^2}.
$$

在 $[1,R]$ 上分部积分；$C(1)=0$ 且 $C(R)B_r(R)\to0$。由于

$$
-B_r'(y)=\frac1y\left[\frac1{(r+\log y)^2}
+\frac2{(r+\log y)^3}\right]
$$

绝对可积，令 $R\to\infty$ 并代入 $y=e^u$，即恢复式 (1.5)。这里没有把 $\eta$ 换成正函数。

对式 (1.5) 使用经典 Gamma 积分的 $\nu=2,3$ 情形（[NIST DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1)，$\mu=1$）：

$$
\frac1{(r+u)^2}=\int_0^\infty te^{-(r+u)t}\,dt,
\qquad
\frac2{(r+u)^3}=\int_0^\infty t^2e^{-(r+u)t}\,dt.
$$

全部被积项非负，Tonelli 定理给式 (3.3)。式 (3.1) 的严格正性及上界来自 $0<A(u)<2$。在任意 $t\ge\varepsilon>0$ 的紧区间上，$2e^{-\varepsilon u}$ 是共同可积控制，故 $\omega$ 连续。

又因 $A$ 局部绝对连续，几乎处处有 $A'(u)=\eta(e^u)e^{-u}$。式 (1.2) 给

$$
\int_0^\infty |A'(u)|e^{-tu}\,du
\le\int_0^\infty(1+u)e^{-(1+t)u}\,du<\infty.
$$

利用 $A(0)=0$、$A(u)e^{-tu}\to0$ 分部积分，得到

$$
\omega(t)=(1+t)\int_1^\infty\eta(y)y^{-t-2}\,dy.
\tag{3.6}
$$

对固定 $t>0$，阶乘部分非负，Tonelli 定理给

$$
\int_1^\infty\log(\lfloor y\rfloor!)y^{-t-2}\,dy
=\frac1{t+1}\sum_{j=2}^\infty\frac{\log j}{j^{1+t}}<\infty.
$$

其余连续部分也绝对可积，且

$$
\int_1^\infty(1-\log y)y^{-t-1}\,dy=\frac1t-\frac1{t^2}.
$$

在 $\Re s>1$ 内，[DLMF 25.2.1](https://dlmf.nist.gov/25.2.E1) 的 Dirichlet 级数可逐项求导：任意 $\Re s\ge1+\varepsilon$ 上，导数项由可求和的 $(\log j)j^{-1-\varepsilon}$ 控制。因此

$$
-\zeta'(1+t)=\sum_{j=2}^\infty\frac{\log j}{j^{1+t}},
$$

代入式 (3.6) 即得式 (3.2)。所有拆分在 $t>0$ 内绝对收敛；没有在 $t=0$ 直接拆开两个发散项。

最后，对任意 $r_0>0$，在 $r\ge r_0/2$ 的邻域内，各阶导数被积函数由 $2t^n(1+t)e^{-r_0t/2}$ 控制，其积分有限。逐阶支配微分给式 (3.4)，严格正性来自 $\omega(t)>0$。这只是在本阶乘密度上使用 Laplace 积分的经典微分法则。$\square$

**命题 3.3（零频极限与原响应远端主项）。** 存在有限常数

$$
C_\infty=\int_1^\infty\frac{\eta(y)}{y^2}\,dy
=\lim_{Y\to\infty}C(Y),
\qquad c_{\mathrm{fac}}\le C_\infty\le2,
$$

并且

$$
\lim_{t\downarrow0}\omega(t)=C_\infty,
\qquad
\lim_{r\to\infty}rh(r)=C_\infty>0.
\tag{3.7}
$$

证明。绝对收敛由式 (3.5) 保证，界由式 (1.3)、(1.4) 取极限得到。在式 (3.1) 中令 $v=tu$，则

$$
\omega(t)=(1+t)\int_0^\infty e^{-v}A(v/t)\,dv.
$$

对 $v>0$，$A(v/t)\to C_\infty$；当 $0<t\le1$ 时以 $4e^{-v}$ 控制，支配收敛给第一个极限。在式 (3.3) 中令 $v=rt$，得到

$$
rh(r)=\int_0^\infty e^{-v}\omega(v/r)\,dv.
$$

当 $r\ge1$ 时以 $2e^{-v}(1+v)$ 控制，再用支配收敛即得。$\square$

## 4. 完整二进差分与有限素数差分

**定义 4.1（同源平移与二进响应）。** 对 $a\ge0$，令 $T_af(r)=f(r+a)$，并定义

$$
q(r)=\left(I-\frac12T_\ell\right)h(r)
=h(r)-\frac12h(r+\ell).
$$

此 $q$ 采用 [累计供应的同对象差分](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/Blueprint/D5/S3/Arith/Robin/ActualFactorialCumulativePositivity.scribe.cs) 中的字面 $h$。它只是完整高段的差分；[ActualFactorialRobinDyadicDerivative 的 `result`](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/D5/S3/Arith/Robin/ActualFactorialRobinDyadicDerivative.lean) 中总积分的低段仍是另一个加项。

**定理 4.2（二进差分的全阶正性与带尾重建）。** 对 $r>0$、$n\ge0$，

$$
(-1)^nq^{(n)}(r)
=\int_0^\infty t^ne^{-rt}(1-2^{-1-t})\omega(t)\,dt>0,
\tag{4.1}
$$

且 $h(r)/2<q(r)<h(r)$。对每个整数 $M\ge1$，

$$
h(r)=\sum_{j=0}^{M-1}2^{-j}q(r+j\ell)+2^{-M}h(r+M\ell),
\tag{4.2}
$$

$$
0<2^{-M}h(r+M\ell)
<2^{1-M}\left[\frac1{r+M\ell}+\frac1{(r+M\ell)^2}\right].
\tag{4.3}
$$

因此式 (4.2) 的有限和收敛到 $h(r)$。

证明。平移 $T_a$ 在式 (3.3) 中乘以 $e^{-at}$，而 $1/2<1-2^{-1-t}<1$ 对 $t>0$ 成立。定理 3.2 的同一指数控制允许求各阶导数，并给全部严格界，特别是 $-q'(r)>0$。反复代入 $h=q+T_\ell h/2$ 得式 (4.2)；式 (1.6) 给式 (4.3)，其右端趋于零。$\square$

**定义 4.3（有限素数支撑的容斥）。** 对有限素数集 $S$，包括空集，定义

$$
\mathcal Q_S(r)=\prod_{p\in S}\left(I-\frac1pT_{\log p}\right)h(r),
\qquad P_S=\prod_{p\in S}p.
$$

空乘积为恒等算子或数值 $1$。$\mu$ 表示 Möbius 函数。

**命题 4.4（有限素数差分保留此高段的严格完全单调性）。** 对每个有限 $S$、$r>0$ 和 $n\ge0$，

$$
\mathcal Q_S(r)=\sum_{d\mid P_S}\frac{\mu(d)}d h(r+\log d),
$$

$$
(-1)^n\mathcal Q_S^{(n)}(r)
=\int_0^\infty t^ne^{-rt}
\prod_{p\in S}(1-p^{-1-t})\omega(t)\,dt>0.
\tag{4.4}
$$

证明。各平移可交换，有限展开与积分交换不涉及极限。每个谱因子介于零与一之间，故式 (3.4) 的控制仍适用，并给严格正性。对每个子集 $U\subseteq S$，展开项的分母是 $d=\prod_{p\in U}p$，符号是 $(-1)^{|U|}=\mu(d)$，给约数表达式。

特别地，$S=\{2,3,5,7\}$ 时，$P_S=210$，有限展开有 $2^4=16$ 项。另一方面，

$$
5040=2^4\,3^2\,5\,7,
\qquad \operatorname{rad}(5040)=210,
\qquad \#\{d:d\mid5040\}=(4+1)(2+1)(1+1)^2=60.
$$

因此式 (2.2) 的阶乘指数信息与这里的平方自由素数支撑是不同读数；式 (4.4) 的量词只涵盖有限 $S$。$\square$

## 5. 五模式带符号响应的黄金阈值

**定义 5.1（五模式的同源尺度响应）。** 使用 [对称 seam 与 Fibonacci 层级卷中合法窗口的定义及五模式](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/docs/develop/theory/AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md)：

$$
\Sigma_3=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\},
\qquad Z_3(z)=\sum_{I\in\Sigma_3}z^{|I|}=1+3z+z^2.
$$

对 $\tau\ge0$，每个选中位置贡献系数 $-\tau$ 并增加同一个尺度 $\ell$，定义

$$
\begin{aligned}
\mathcal F_\tau(r)
&=\sum_{I\in\Sigma_3}(-\tau)^{|I|}h(r+|I|\ell)\\
&=h(r)-3\tau h(r+\ell)+\tau^2h(r+2\ell).
\end{aligned}
\tag{5.1}
$$

这是指定的解析响应；系数不是概率，相同单选响应也不将三个模式标签识别成一个模式。置

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad \tau_* =\varphi^{-2}=\frac{3-\sqrt5}{2}.
$$

**定理 5.2（五模式全域正性与严格全阶正性的共同阈值）。** 在 $0\le\tau\le1$ 内，以下三条件等价：

$$
\begin{aligned}
&\mathcal F_\tau(r)>0\quad\text{对全部 }r>0;\\
&(-1)^n\mathcal F_\tau^{(n)}(r)>0
\quad\text{对全部 }r>0\text{ 和整数 }n\ge0;\\
&\tau\le\tau_*.
\end{aligned}
\tag{5.2}
$$

临界值 $\tau=\tau_*$ 也保留全部严格不等式。

证明。定理 3.2 及有限线性组合给

$$
\mathcal F_\tau(r)=\int_0^\infty e^{-rt}
P(\tau e^{-\ell t})\omega(t)\,dt,
\qquad P(z)=1-3z+z^2.
\tag{5.3}
$$

对固定 $\tau$，$|P(\tau e^{-\ell t})|\le1+3\tau+\tau^2$；因此各阶导数仍可在积分内计算。因式分解

$$
P(z)=(1-\varphi^2z)(1-\varphi^{-2}z)
$$

表明，若 $0\le\tau\le\tau_*$，则 $P(\tau e^{-\ell t})>0$ 对每个 $t>0$ 成立。在临界处只在端点 $t=0$ 消失，故积分及其全部交替导数仍严格为正。

反过来，式 (5.3) 中令 $v=rt$，命题 3.3 及共同控制

$$
2(1+3\tau+\tau^2)e^{-v}(1+v)\quad(r\ge1)
$$

给出

$$
\lim_{r\to\infty}r\mathcal F_\tau(r)
=C_\infty(1-3\tau+\tau^2).
\tag{5.4}
$$

当 $\tau_*<\tau\le1$ 时，该极限严格为负，所以存在 $R>0$，使全部 $r>R$ 都有 $\mathcal F_\tau(r)<0$。这排除了全域正性；而严格完全单调显然蕴含零阶正性，故三者等价。$\square$

## 6. 四份记录的共同 Gram 与同一个多项式

**定义 6.1（单位记录的完整关系合同）。** 对 $\tau\ge0$，令 $a=\sqrt\tau$，规定四份单位记录的候选 Gram 为

$$
G_\tau=
\begin{pmatrix}
1&a&0&0\\
a&1&a&0\\
0&a&1&a\\
0&0&a&1
\end{pmatrix}.
\tag{6.1}
$$

共同实现是同一实或复内积空间中四个单位向量，其全部内积恰为式 (6.1)；非相邻内积为零是合同的一部分。最小载体维数指这种向量实现的最小维数。所用 Gram 分解与最小秩判据沿用 [二阶关系完成卷，定义 109.1 与定理 109.2](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)。由于此矩阵为实对称，那里记录相关矩阵的转置约定不改变本矩阵。

此合同只规定共同向量。带转移概率和内部运输的完整等距约束是 [最小记录 dilation 卷，定义 1.1–1.3](https://github.com/the-omega-institute/trureturing/blob/c1b1f24da3ffc4aff376259b96685604d55525ea/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md) 中的另一合同；本定义未供应那些转移、运输或取得操作。

**定理 6.2（五模式响应与四记录相容性的同一边界）。** 对全部 $\tau\ge0$，

$$
\det G_\tau=1-3\tau+\tau^2,
\qquad
G_\tau\succeq0\iff0\le\tau\le\tau_*.
\tag{6.2}
$$

在可实现范围内，最小载体维数为

$$
\operatorname{rank}G_\tau=
\begin{cases}
4,&0\le\tau<\tau_*,\\
3,&\tau=\tau_*.
\end{cases}
\tag{6.3}
$$

因此，在 $0\le\tau\le1$ 内，式 (5.2) 还等价于四份记录的共同实现；只有临界点可在三维载体实现。

证明。行列式的非零置换由路径上的不相邻换位组成。空选择贡献 $1$，三个单换位各贡献 $-a^2$，第一与第三条边的共同换位贡献 $a^4$。故行列式恰为同一个五模式多项式 $P(a^2)$。

谱计算使用三对角 Toeplitz 矩阵的经典特征值公式（[Nicholas J. Higham, *What Is a Tridiagonal Matrix?*, 式 (6)](https://nhigham.com/2022/01/10/what-is-a-tridiagonal-matrix/)）。对式 (6.1)，其四个特征值为

$$
1+a\varphi,\quad1+a\varphi^{-1},\quad
1-a\varphi^{-1},\quad1-a\varphi.
$$

最小值为 $1-a\varphi$，故给正半定阈值。阈值以下全部特征值严格为正；在阈值处只有最后一个为零，给式 (6.3)。经典 Gram 分解在此提供存在性及最小维数，定理 5.2 给同源解析等价。

临界时令 $a=\varphi^{-1}$，满足 $a+a^2=1$。显式向量

$$
\begin{aligned}
e_1&=(1,0,0),& e_2&=(a,\sqrt a,0),\\
e_3&=(0,\sqrt a,a),& e_4&=(0,0,1)
\end{aligned}
$$

均为单位向量，相邻内积为 $a$，非相邻内积为零，且张成三维，因而达到最小值。这里的维数始终是所定义共同记录的载体维数。$\square$

**命题 6.3（全部三记录可实现仍不足以共同实现四记录）。** 对 $\tau=2/5$，式 (6.1) 的每个三记录主矩阵均正定，但完整四记录矩阵不是正半定；同参数的 $\mathcal F_{2/5}$ 对充分大的 $r$ 为负。

证明。三阶主行列式在连续三点时为 $1-2\tau=1/5$，在另外两种三点选择时为 $1-\tau=3/5$。二阶主行列式为 $1-\tau=3/5$ 或 $1$，一阶为 $1$，故每个三阶主矩阵正定。另一方面，

$$
\det G_{2/5}=1-\frac65+\frac4{25}=-\frac1{25}<0,
$$

所以不存在四记录共同 Gram 实现。式 (5.4) 给 $r\mathcal F_{2/5}(r)\to-C_\infty/25<0$，得到解析结论。$\square$

## 7. 一般有限窗口的完全单调分类

**定义 7.1（有限窗口与零窗口约定）。** 对整数 $N\ge0$，沿用定义 5.1 所引 Fibonacci 层级卷的合法集合

$$
\Sigma_N=\{I\subseteq\{1,\ldots,N\}:I\text{ 不含相邻位置}\},
\qquad Z_N(z)=\sum_{I\in\Sigma_N}z^{|I|}.
$$

采用该合法集合的选择递推作为中间工具：

$$
Z_0(z)=1,\quad Z_1(z)=1+z,\quad
Z_N(z)=Z_{N-1}(z)+zZ_{N-2}(z)\quad(N\ge2).
\tag{7.1}
$$

它由末位置未选或已选两种互斥情形得到。对 $\tau\ge0$ 定义

$$
\mathcal F_{N,\tau}(r)
=\sum_{I\in\Sigma_N}(-\tau)^{|I|}h(r+|I|\ell),
\qquad
G_{N,\tau}=I_{N+1}+\sqrt\tau\,A_{N+1},
$$

其中 $A_{N+1}$ 是 $N+1$ 个顶点的路径邻接矩阵。特别地，$\mathcal F_{3,\tau}=\mathcal F_\tau$。零窗口单独规定为 $\mathcal F_{0,\tau}=h$、$G_{0,\tau}=(1)$，对所有 $\tau\ge0$ 都适用；其阈值可记为 $\tau_0=+\infty$，不使用下述余弦分母公式。

**定理 7.2（同一阶乘响应的窗口分类）。** 对整数 $N\ge1$ 和 $\tau\ge0$，置

$$
\tau_N=\frac1{4\cos^2(\pi/(N+2))}.
$$

以下条件等价：$\mathcal F_{N,\tau}$ 完全单调；$\mathcal F_{N,\tau}$ 严格完全单调；$\tau\le\tau_N$；$G_{N,\tau}\succeq0$。在该范围内，$G_{N,\tau}$ 的秩在 $\tau<\tau_N$ 时为 $N+1$，在 $\tau=\tau_N$ 时为 $N$。

证明。有限展开给

$$
\mathcal F_{N,\tau}(r)=\int_0^\infty e^{-rt}
Z_N(-\tau e^{-\ell t})\omega(t)\,dt.
\tag{7.2}
$$

对固定 $N,\tau$，多项式因子在 $t\ge0$ 上有界，定理 3.2 的控制因此适用于全部导数。

路径行列式的换位展开与 $\Sigma_N$ 的选择一一对应；等价地，其行列式递推与式 (7.1) 相同，且初值相同。因此

$$
\det(I_{N+1}+\sqrt z\,A_{N+1})=Z_N(-z)\quad(z\ge0).
$$

引用定理 6.2 所用的经典路径谱公式，特征值为 $2\cos(j\pi/(N+2))$，$1\le j\le N+1$。将相反的特征值配对，若有零特征值则其因子为一，得到

$$
Z_N(-z)=\prod_{j=1}^{\lceil N/2\rceil}
\left(1-4z\cos^2\frac{j\pi}{N+2}\right).
\tag{7.3}
$$

右侧各正根互异，最小根为 $\tau_N$。若 $\tau\le\tau_N$，则对每个 $t>0$ 有 $Z_N(-\tau e^{-\ell t})>0$，故式 (7.2) 给严格完全单调性。

为了证明必要性，设 $\tau>\tau_N$。在最小根右侧且下一根左侧的开区间内，$Z_N(-z)<0$；若只有一个根，取它右侧的充分小邻域。选择该区间中的 $z_0<\tau$，令

$$
t_0=\ell^{-1}\log(\tau/z_0)>0,
\qquad b(t)=Z_N(-\tau e^{-\ell t})\omega(t).
$$

则 $b$ 连续，$b(t_0)<0$，且存在有限 $K$ 使 $|b(t)|\le K(1+t)$ 对全部 $t>0$ 成立。

若 $\mathcal F_{N,\tau}$ 完全单调，对每个整数 $n\ge1$ 就有

$$
\int_0^\infty t^ne^{-(n/t_0)t}b(t)\,dt\ge0.
\tag{7.4}
$$

以下将 Gamma 集中的经典近似作用于这个具体 $b$，并保留其增长控制。令 $X_n$ 的密度为

$$
p_n(t)=\frac{(n/t_0)^{n+1}}{\Gamma(n+1)}t^ne^{-nt/t_0},\qquad t>0.
$$

归一化及矩由 [DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1) 的 Gamma 积分给出：

$$
\mathbb E X_n=t_0\frac{n+1}{n},\qquad
\operatorname{Var}(X_n)=t_0^2\frac{n+1}{n^2},\qquad
\mathbb E X_n^2=t_0^2\frac{(n+1)(n+2)}{n^2}.
$$

于是 $\mathbb E(X_n-t_0)^2=t_0^2(n+2)/n^2\to0$，且 $\sup_n\mathbb E(1+X_n)^2<\infty$。给定 $\varepsilon>0$，连续性允许选 $\delta>0$ 使 $|b(t)-b(t_0)|<\varepsilon$ 当 $|t-t_0|<\delta$。在补集上，Cauchy–Schwarz 与二阶矩界给

$$
\begin{aligned}
&\mathbb E\bigl[|b(X_n)-b(t_0)|\,
\mathbf1_{\{|X_n-t_0|\ge\delta\}}\bigr]\\
&\quad\le
K\bigl(\mathbb E(1+X_n)^2\bigr)^{1/2}
\mathbb P(|X_n-t_0|\ge\delta)^{1/2}
+|b(t_0)|\mathbb P(|X_n-t_0|\ge\delta)\longrightarrow0.
\end{aligned}
$$

概率趋零由二阶矩的 Markov 界保证。因此 $\mathbb E b(X_n)\to b(t_0)<0$。但式 (7.4) 乘以正的归一化因子即为 $\mathbb E b(X_n)\ge0$，矛盾。增长界和一致二阶矩保证了整个尾部的控制，单有依概率集中并不足以替代这一步。

最后，$G_{N,\tau}$ 的最小特征值为

$$
1-2\sqrt\tau\cos\frac\pi{N+2}.
$$

它非负恰在 $\tau\le\tau_N$；阈值以下全部正，阈值处只有最小特征值为零。故正半定等价和秩结论成立。$\square$

**推论 7.3（有限窗口数值与极限的精确范围）。** 对 $N=1,2,3,4$，合法模式数分别为 $2,3,5,8$，阈值分别为

$$
1,\quad\frac12,\quad\varphi^{-2},\quad\frac13,
$$

临界记录秩分别为 $1,2,3,4$。序列 $\tau_N$ 严格递减到 $1/4$，故固定 $\tau\ge0$ 时，所有有限窗口的响应都完全单调，当且仅当 $\tau\le1/4$。此外，对任意固定 $N\ge0$、$\tau\ge0$，

$$
\lim_{r\to\infty}r\mathcal F_{N,\tau}(r)
=C_\infty Z_N(-\tau).
\tag{7.5}
$$

证明。模式数由式 (7.1) 在 $z=1$ 的递推得到，阈值由余弦值直接代入。随着 $N$ 增大，$\pi/(N+2)$ 严格减小到零，余弦严格增大到一，给阈值极限和全有限窗口结论。式 (7.5) 用式 (7.2) 的有界多项式因子重复命题 3.3 的支配收敛即可。

定理 7.2 分类的是全部交替导数。式 (7.5) 在 $Z_N(-\tau)<0$ 时还给最终负性；当该多项式非负时，仅凭此极限不能判定全部 $r>0$ 的正性。五模式的零阶正性等价采用定理 5.2 的 $0\le\tau\le1$ 范围。$\square$

## 8. 黄金临界的主项消去与正剩余

**定理 8.1（同源黄金响应的远端衰减）。** 对 $0\le\tau<\tau_*$，

$$
r\mathcal F_\tau(r)\longrightarrow
C_\infty(1-3\tau+\tau^2)>0.
\tag{8.1}
$$

临界响应具有算子分解

$$
\mathcal F_{\tau_*}=(I-T_\ell)(I-\varphi^{-4}T_\ell)h,
\tag{8.2}
$$

并满足

$$
r^2\mathcal F_{\tau_*}(r)\longrightarrow
C_\infty\ell(1-\varphi^{-4})>0.
\tag{8.3}
$$

证明。式 (8.1) 是式 (5.4) 在所列范围的直接使用。恒等式 $3\varphi^{-2}=1+\varphi^{-4}$ 给

$$
1-3\tau_*z+\tau_*^2z^2=(1-z)(1-\varphi^{-4}z),
$$

故得式 (8.2)。临界谱乘子为

$$
(1-e^{-\ell t})(1-\varphi^{-4}e^{-\ell t})
=\ell(1-\varphi^{-4})t+O(t^2)\quad(t\downarrow0).
$$

在谱积分中令 $v=rt$，则 $r^2\mathcal F_{\tau_*}(r)$ 的被积函数为

$$
e^{-v}r(1-e^{-\ell v/r})
(1-\varphi^{-4}e^{-\ell v/r})\omega(v/r).
$$

对 $r\ge1$，由 $r(1-e^{-\ell v/r})\le\ell v$，其绝对值不超过 $2\ell v(1+v)e^{-v}$，可积。点态极限为 $C_\infty\ell(1-\varphi^{-4})ve^{-v}$，而 $\int_0^\infty ve^{-v}dv=1$，故支配收敛给式 (8.3)。这消去的是 $1/r$ 主项；定理 5.2 保证临界响应自身及全部交替导数仍严格为正。$\square$

## 9. 尺度角点差分与二进响应的严格对数凸性

**定义 9.1（尺度参数的混合差分）。** 对 $a>0$，令 $\Delta_a=I-T_a$。对整数 $m\ge1$ 和 $a_1,\ldots,a_m>0$，$\Delta_{a_1}\cdots\Delta_{a_m}h$ 是尺度长方体角点的交替和，所有角点仍由同一个 $h$ 取值。这里的长方体是参数域 $\prod_{j=1}^m[0,a_j]$。

**命题 9.2（阶乘高段的正内部积分与二进谱方差）。** 对定义 9.1 的参数及 $r>0$，

$$
\begin{aligned}
\Delta_{a_1}\cdots\Delta_{a_m}h(r)
&=\int_0^{a_1}\cdots\int_0^{a_m}
(-1)^m h^{(m)}(r+s_1+\cdots+s_m)\,ds_m\cdots ds_1\\
&=\int_0^\infty e^{-rt}
\prod_{j=1}^m(1-e^{-a_jt})\omega(t)\,dt>0.
\end{aligned}
\tag{9.1}
$$

对二进响应 $q$，定义概率测度

$$
d\nu_r(t)=\frac{e^{-rt}(1-2^{-1-t})\omega(t)}{q(r)}\,dt
\quad(t>0).
$$

则

$$
(\log q)''(r)=\operatorname{Var}_{\nu_r}(t)>0,
\qquad q(r)q''(r)-q'(r)^2>0.
\tag{9.2}
$$

证明。逐次使用微积分基本定理于 $h(r)-h(r+a)=\int_0^a-h'(r+s)ds$，得到式 (9.1) 的第一行；定理 3.2 保证全部所需连续导数。有限差分的每个平移在谱侧给 $e^{-a_jt}$，得到第二行。谱乘积介于零与一之间，故积分收敛，并因每个 $a_j>0$ 而严格为正。

这也可由第一行代入式 (3.4) 并用非负 Tonelli 交换积分得到。对 $m=2$，其角点表达式正是

$$
h(r)-h(r+a_1)-h(r+a_2)+h(r+a_1+a_2)>0;
$$

对 $m=3$ 则是八个角点的交替和。该混合差分使用定义 5.1 所引对称 seam 卷中的同一代数差分规则；内部积分的严格正性由本卷的阶乘密度供应。

由式 (4.1)，$\nu_r$ 总质量为一，并有全部有限矩。直接计算

$$
\mathbb E_{\nu_r}t=-\frac{q'(r)}{q(r)},\qquad
\mathbb E_{\nu_r}t^2=\frac{q''(r)}{q(r)},
$$

从而得到式 (9.2) 的方差恒等式。其密度在整个 $(0,\infty)$ 上严格为正，故不能集中于一点，方差严格大于零。这里使用的是正 Laplace 权重下的经典矩计算；严格性来自已经证明的同源密度正性。$\square$

## 追加锚（本行以下为增补区）
