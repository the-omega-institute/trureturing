# 实际奇 Möbius 调和率与固定尺度 Robin 尾合同

本卷续接 [原曲率逼近卷](FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_CURVATURE_APPROXIMATION.md) §471，保留连续的条目编号。

§453 的原核、可积性、求导与 DP.13–DP.15 取自 [素数前缀卷](FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_PRIME_PREFIX.md) §453。§464 的 RLB.7、§466 的 HG.2–HG.10 与命题 466.1–466.2，以及 §§468–469 的有限运输均取自 [原曲率逼近卷](FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_CURVATURE_APPROXIMATION.md) 的对应章节。

实际未加权有限配对的形式化来源见 [ActualOddMobiusFinitePairing.lean](../../../D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.lean)；其完整 dyadic 与 clipped 身份不提供奇调和衰减。

## 472. 实际奇调和前缀的全部后继衰减与固定尺度尾输入

本节在 §466 的同一实际算术对象上消费 §464 的 RLB.7 与命题 466.1 的 HG.2。有限运输中的小整数商、零商与末项均保留；所得衰减用于命题 466.2 的原核合同。

**定理 472.1（实际完整调和率向奇调和率的有限运输）。** 令 $\mu$ 为标准算术 Möbius 函数，保持

$$
H(N)=\sum_{1\le m\le N}\frac{\mu(m)}m,
\qquad
H_{\mathrm o}(N)=\sum_{\substack{1\le m\le N\\m\text{ 奇}}}\frac{\mu(m)}m,
\qquad H(0)=H_{\mathrm o}(0)=0.
$$

完整调和率的来源是 dbsanfte/RiemannGaussian 不可变修订 [`24444671cee3bf643ff1307909b961a329372a9e`](https://github.com/dbsanfte/RiemannGaussian/tree/24444671cee3bf643ff1307909b961a329372a9e) 中 [`MoebiusHarmonicCancellation.lean`](https://github.com/dbsanfte/RiemannGaussian/blob/24444671cee3bf643ff1307909b961a329372a9e/RiemannGaussian/MoebiusHarmonicCancellation.lean) 的 `exists_moebiusHarmonicPrefix_cubic_rate`，即 RLB.7。取该来源给出的任一实数见证 $h_0\ge22$，并取其固定常数 $C_{\rm harmonic}=6+4C_{\rm finite}>0$；准确供应为

$$
\forall h\in\mathbb R\ (h\ge h_0),\quad
\forall q\in\mathbb N:\quad
\exp(2\cdot10^{15}h^3)\le q
\ \Longrightarrow
|H(q)|\le C_{\rm harmonic}e^{-h/8}.
\tag{OH.1}
$$

在此来源合同及同一实际前缀的 HG.2 下，定义

$$
A=2\cdot10^{15},\qquad
c_{\mathrm o}=\frac1{8(4A)^{1/3}},\qquad
C_{\mathrm o}=2C_{\rm harmonic}+16,\qquad
D_0=\left\lceil\exp\!\bigl(\max\{8,4Ah_0^3\}\bigr)\right\rceil.
\tag{OH.2}
$$

则 $D_0$ 是自然数，$C_{\mathrm o}>0$、$c_{\mathrm o}>0$，且同一对常数对全部自然数后继成立：

$$
\boxed{\quad
\forall n\in\mathbb N\ (n\ge D_0):\qquad
|H_{\mathrm o}(n)|\le
C_{\mathrm o}\exp\!\left(-c_{\mathrm o}(\log n)^{1/3}\right).
\quad}
\tag{OH.3}
$$

$h_0$ 是来源的存在见证，OH.2 保留这一依赖，不指定其数值或阈值的计算可行性。该结论是上述来源命题与 HG.2 之上的普通数学推导，不表示该上游证明闭包或本节在本库取得新的 kernel、公理闭包或冻结验收。

**证明。** 固定任意自然数 $n\ge D_0$，记

$$
t=\log n,\qquad L=\log2,\qquad
h=\left(\frac{t}{4A}\right)^{1/3},\qquad
J=\left\lfloor\frac{t}{2L}\right\rfloor,\qquad
K=n+1,\qquad q_a=\left\lfloor\frac{n}{2^a}\right\rfloor.
$$

由自然数上取整的定义，$n\ge\exp(\max\{8,4Ah_0^3\})$，所以 $t\ge8$、$t\ge4Ah_0^3$、$h\ge h_0$。所有立方根取非负实立方根。特别地 $n\ge e^8>16$，且 $J\ge1$。由 $\log n\le n-1$ 与 $2\log2>1$ 得 $J<K$，故下面的两个有限区间覆盖 $0\le a<K$，没有漏层。

应用 HG.2 于这个 $n,K$，保留原末项，得

$$
H_{\mathrm o}(n)
=\sum_{a=0}^{J-1}2^{-a}H(q_a)
 +\sum_{a=J}^{K-1}2^{-a}H(q_a)
 +2^{-K}H_{\mathrm o}(q_K).
\tag{OH.4}
$$

§466 已给 $2^{n+1}\ge n+2>n$，因此 $q_K=0$，OH.4 的末项恰为 $2^{-K}H_{\mathrm o}(0)=0$。这一步使用准确整数截止，没有以极限删除余项。

先处理 $0\le a<J$。因为 $a<J\le t/(2L)$，有

$$
\frac{n}{2^a}\ge e^{t/2}\ge2.
$$

对任意实数 $u\ge2$，$\lfloor u\rfloor\ge u-1\ge u/2$。于是每个这样的原整数商满足

$$
q_a\ge\frac12e^{t/2}\ge e^{t/4}
=\exp(Ah^3),
\tag{OH.5}
$$

其中第二个不等式由 $t\ge8>4\log2$ 支付。故 $q_a$ 是 OH.1 允许的自然数截止；已经支付的 $h\ge h_0$ 给

$$
|H(q_a)|\le C_{\rm harmonic}e^{-h/8}
=C_{\rm harmonic}e^{-c_{\mathrm o}t^{1/3}}.
$$

这些未归一化的几何系数总量准确为 $2(1-2^{-J})$，从而

$$
\left|\sum_{a=0}^{J-1}2^{-a}H(q_a)\right|
\le 2C_{\rm harmonic}e^{-c_{\mathrm o}t^{1/3}}.
\tag{OH.6}
$$

再处理整个 $J\le a<K$，不要求这些整数商满足 OH.1。标准 Möbius 函数满足 $|\mu(m)|\le1$。因此，对任何 $1\le q\le n$，有限三角不等式与递减函数 $u\mapsto1/u$ 的积分比较给

$$
|H(q)|\le\sum_{m=1}^{q}\frac1m
\le1+\int_1^q\frac{du}{u}
=1+\log q\le1+t.
\tag{OH.7}
$$

$q=1$ 时积分为零，准确包括单位源 $\mu(1)/1=1$；$q=0$ 时使用 $H(0)=0$，同一上界仍成立。所有 $q_a$ 都在 $0,\ldots,n$ 内，故 OH.7 或零值逐项支付整个后段。这里仅对实际有符号前缀作上界估计，没有以绝对 Möbius 前缀替换 OH.1 或 OH.4 的对象。

后段有限系数总量及 floor 损失分别为

$$
\sum_{a=J}^{K-1}2^{-a}
=2^{1-J}\bigl(1-2^{-(K-J)}\bigr)\le2^{1-J},
\qquad
2^{-J}\le2e^{-t/2},
\tag{OH.8}
$$

后一个不等式来自 $J\le t/(2L)<J+1$。因而

$$
\left|\sum_{a=J}^{K-1}2^{-a}H(q_a)\right|
\le4(1+t)e^{-t/2}.
\tag{OH.9}
$$

这包括全部未达到来源阈值的小商；若 $2^a>n$，其 $q_a=0$ 项准确为零，没有为零商取对数。此估计也允许后段中仍有大商，故没有遗漏任何过渡层。

最后，把 OH.9 吸收到同一个立方对数率。由 $e^{t/4}\ge1+t/4$，得到 $1+t\le4e^{t/4}$。又由 $A>0$ 及其准确数值，有 $0<c_{\mathrm o}\le1$；$t\ge8$ 给 $t^{1/3}\le t/4$。因此

$$
4(1+t)e^{-t/2}
\le16e^{-t/4}
\le16e^{-c_{\mathrm o}t^{1/3}}.
\tag{OH.10}
$$

将 OH.6、OH.9–OH.10 与 OH.4 的准确零末项合并，得到

$$
|H_{\mathrm o}(n)|
\le(2C_{\rm harmonic}+16)e^{-c_{\mathrm o}t^{1/3}},
$$

即 OH.3。整个论证对任意 $n\ge D_0$ 成立；$h,J,K$ 可随 $n$ 选取，但 $C_{\mathrm o},c_{\mathrm o},D_0$ 先由同一个来源合同确定，不随 $n$ 改变。所有和始终有限。证毕。

**推论 472.2（对每个固定原核的 HG.9 实例）。** 在定理 472.1 的同一来源合同下，固定任意实数 $x\ge e$，取任意自然数 $D\ge D_0$ 且 $D>x$。严格保持 HG.3 的原对象

$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad w(t)=\frac{1+\log t}{t^2\log^2t},
$$

$$
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)\,dt,
\qquad\mathscr D_x(s)=P_x^\eta(s)-P_x^\eta(2s),
\qquad b_x(s)=s\mathscr D_x(s).
$$

消费 §§453、466 对这些完整积分的可积性、求导与 HG.6 增长及变差合同，$V_x$ 取 HG.6 的同一固定 $x$ 常数。令 $c=c_{\mathrm o}$、$z_0=(\log(D+1))^{1/3}$，$J_j(c,z_0)$ 严格取 HG.8 的完整积分。则同一实际奇来源的自然截止尾存在，并满足 HG.9 的准确实例

$$
\begin{aligned}
\mathscr T_{D,\infty}(x)
&:=\lim_{M\to\infty}
  \sum_{\substack{D<n\le M\\n\text{ 奇}}}\mu(n)\mathscr D_x(n)\\
&=-b_x(D+1)H_{\mathrm o}(D)
 -\sum_{n=D+1}^{\infty}[b_x(n+1)-b_x(n)]H_{\mathrm o}(n),\\
|\mathscr T_{D,\infty}(x)|
&\le |b_x(D+1)|\,|H_{\mathrm o}(D)|
 +3C_{\mathrm o}V_xe^c
  [J_2(c,z_0)+2J_5(c,z_0)+J_8(c,z_0)].
\end{aligned}
\tag{OH.11}
$$

**证明。** 每个自然数 $n\ge D$ 都满足 $n\ge D_0$，故定理 472.1 以同一 $C_{\mathrm o},c_{\mathrm o}$ 提供命题 466.2 的全部 HG.7 输入。$D>x$ 与同核 HG.6 保持其余假设。直接应用命题 466.2 即得 OH.11；其有限式 HG.10 的末项 $b_x(M)H_{\mathrm o}(M)$ 保留到自然截止极限，并由 HG.6 与 OH.3 趋零，锚 $-b_x(D+1)H_{\mathrm o}(D)$ 保留。证毕。

OH.11 只支付这一固定 $x$ 的尾合同。回接 §453 的原累计 Mertens 配对时，DP.13 的 $P_x^\eta(\min\{2m,N+1\})$ 截止，以及 DP.14 的完整差项

$$
E_N(x)=\sum_{\substack{N/2<m\le N\\m\text{ 奇}}}
\mu(m)[P_x^\eta(2m)-P_x^\eta(N+1)]
$$

仍按 DP.14–DP.15 的同核、同截止合同处理；不能因 OH.3 或 OH.11 将其有限值设为零，也不能据此进行独立的无限素数—合数拆分。

#### 472.3 来源成熟度与结论范围

定理 472.1 是复用 RLB.7 与 HG.2 的来源运输推导；推论 472.2 是既有命题 466.2 的应用。上游正的 $C_{\rm harmonic}$ 与存在见证 $h_0$ 按 OH.1 原样承重；衰减供应、有限身份与此处普通证明的成熟度不混作本库新的形式化验收。RiemannGaussian 来源使用 Apache-2.0；这里不复制或重证其调和消去证明。$|\mu|\le1$ 复用钉版 Mathlib 的 [`ArithmeticFunction.abs_moebius_le_one`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean)。实际未加权有限配对的仓内来源为 `D5/S3/Arith/Robin/ActualOddMobiusFinitePairing.lean`，它的完整 dyadic 与 clipped 身份不是奇调和衰减定理。

定理 472.1 明确给出命题 466.2 所需的 HG.7 算术输入。§§468–469 的有限逆、加权 floor 与幂次类运输不承担 OH.1；`WeightedInghamRate` 的对象是 Fibonacci 商的余数和，而不是实际 $\mu(n)/n$。本节的常数只用于支付完整运输，不主张最优常数、加强率、成本改进或文献优先权。

固定 $x$ 时 $V_x$ 等原核常数允许依赖 $x$；OH.11 没有给出 $x,D$ 联合增长时的 $\sqrt{x}\log x$ 临界共同精度，也没有支付整个有限头部的实际符号。原 signed Robin 完整目标与 RH、native observer 对应，以及物理熵或控制成本的桥仍未由本节建立。Abel 变差级数的绝对收敛与实际原子尾的自然截止存在也不等于原子级数绝对收敛。

## 追加锚（本行以下为增补区）
