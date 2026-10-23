# Robin 自价格来源的联合标量松弛

## 1. 同一整数上的合同与实际算术范围

**定义 1.1（自价格与完整有符号尾项）。** 对 $x>1$ 置

$$
f(x)=\log\log x,\qquad
g(x)=f'(x)=\frac1{x\log x},\qquad
k(x)=-g'(x)=\frac{1+\log x}{x^2\log^2x},\qquad
T(x)=\sqrt x\log x.
\tag{1.1}
$$

对普通整数 $N>e$，实际响应是 $Z(N)=\sigma(N)/N$，
$G(N)=Z(N)/\log\log N$，自价格为 $g(\log N)$。
本文使用的实际来源条件是：$N$ 在这个价格上全局 CA 最优，
$G(m)\le G(N)$ 对全部整数 $m\ge N$ 成立，且
$G(N/p)\le G(N)$、$N/p>e$ 对全部素因子 $p\mid N$ 成立。
这些条件中的 $N$ 必须是同一个整数。

[Caveney–Nicolas–Sondow 的同源选取应用](../../../Library/Arith/caveney2012sacaga.md#the-same-power-excess-family-also-supplies-proper-ga1-sources)
给出所用来源族；
[Mantovanelli 存档原稿 §4 的 `thm:direct-bridge`](../../../Library/Analytic/mantovanelli2026primeworkload.md#the-existing-prime-local-bridge)
直接提供该族的 regular 身份。
这两项既有结果不在本文重新证明。
实际尾项是

$$
I_\psi(A)=\int_A^\infty(\psi(t)-t)k(t)\,dt,
\qquad A=\log N,
\tag{1.2}
$$

其中 $\psi$ 是普通素数幂的 Chebyshev 函数。
[既有端点应用](../../../Library/ArithSums/nicolas2025comparison.md#the-endpoint-condition-at-actual-self-tangent-sources)
提供 $A-\vartheta(A)=\sqrt{2A}(1+o(1))$，不提供式（1.2）的下界。

**定义 1.2（标量松弛合同）。** 将实际 $Z$ 换成正整数上的正函数
$\widetilde Z$，令 $\widetilde G(n)=\widetilde Z(n)/\log\log n$
仅在 $n>e$ 上定义。另取最终正且严格递增的连续函数
$Q,\widetilde\psi,\widetilde\vartheta$，以及可微势 $\widetilde H$。
在来源 $n$、尺度 $a=\log n$ 上要求

$$
\begin{aligned}
\widetilde Z(m)m^{-g(a)}
&\le\widetilde Z(n)n^{-g(a)} &&(m\in\mathbb N_{\ge1}),\\
\widetilde G(m)&\le\widetilde G(n) &&(m\ge n),\\
\widetilde G(n/p)&\le\widetilde G(n),\quad n/p>e &&(p\mid n),\\
Q(a)&=a,\qquad
\widetilde H(a)=\log\widetilde G(n),
\end{aligned}
\tag{1.3}
$$

以及完整的势、核心和尾积分关系

$$
\begin{aligned}
\widetilde H'(t)&=k(t)(Q(t)-t),&
\lim_{t\to\infty}\widetilde H(t)&=\gamma,\\
\widetilde K(a)&=\int_a^\infty(Q(t)-\widetilde\psi(t))k(t)\,dt,&
\widetilde I(a)&=\int_a^\infty(\widetilde\psi(t)-t)k(t)\,dt,\\
\gamma-\log\widetilde G(n)&=\widetilde I(a)+\widetilde K(a).
\end{aligned}
\tag{1.4}
$$

这里 $Q$ 是正单调累积量；$t-Q(t)$ 是有符号量，不要求逐点非负。
合同没有要求 $\widetilde Z=\sigma/n$，没有规定事件为普通素数幂，
也没有要求 $\widetilde\psi(t)=\sum_{r\ge1}\widetilde\vartheta(t^{1/r})$。

## 2. 联合实现的构造

**定义 2.1（递减峰高与整数尺度）。** 固定
$0<\eta<1/2$、$b>0$、$c_0=\sqrt2-1$、$\delta=1/10$，置

$$
n_j=2^{2^j},\qquad a_j=\log n_j=2^j\log2,
\qquad
\chi(v)=
\begin{cases}
(1-v^2)^3,& |v|\le1,\\
0,& |v|>1.
\end{cases}
\tag{2.1}
$$

取整数 $j_0$ 使 $(1-\delta)a_{j_0}>e$，对 $x>1$ 定义

$$
h(x)=b\sum_{j\ge j_0}a_j^{-\eta}
\chi\!\left(\frac{x-a_j}{\delta a_j}\right),
\qquad U(x)=\gamma+f(x)+h(x).
\tag{2.2}
$$

这一构造复用光滑峰函数与凹函数支撑线的方法。
[主卷 §§261–262](FIBONACCI_ATOMIC_RELATION_GENERATION.md#261-精确-fibonacci-采样的相位盲区与单调脉冲模型)
已有人工单调源、强 PNT 相容误差与尾项失控的构造；
这里的承重命题是整数全局自价格优化、右尾优化、删除比较、端点与正核心
在同一个来源族上的联合实现，记为 `repo-derived`。

**定理 2.2（同源双优化不提供完整尾项的有限下界）。**
对定义 2.1 的每个 $\eta,b$，存在共同常数 $x_0>e$、$t_0>1$ 和整数
$J\ge j_0$，使以下构造全部定义良好。置

$$
\widetilde Z(m)=
\begin{cases}
\exp U(\log m),& \log m\ge x_0,\\
1,& \log m<x_0,
\end{cases}
\qquad
Q(t)=(U')^{-1}(g(t))\quad(t\ge t_0),
\tag{2.3}
$$

其中 $U'$ 的逆取自 $[x_0,\infty)$，且
$g(t_0)\le U'(x_0)$。再置

$$
\begin{aligned}
\widetilde\psi(t)&=Q(t)-c_0\sqrt t,\\
\widetilde\vartheta(t)&=Q(t)-\sqrt{2t},\\
\widetilde H(t)&=U(Q(t))+g(t)(t-Q(t))-f(t).
\end{aligned}
\tag{2.4}
$$

则 $Q,\widetilde\psi,\widetilde\vartheta$ 在 $[t_0,\infty)$ 正且严格递增，
且对全部 $j\ge J$，同一个 $n_j$ 满足式（1.3）—（1.4），以及
$\widetilde G(n_jp)\le\widetilde G(n_j)$ 对全部普通素数 $p$ 成立。
此外，全部 $X\ge a_j$ 满足

$$
\widetilde H(X)\le\widetilde H(a_j),\qquad
\int_{a_j}^X(Q(t)-t)k(t)\,dt\le0.
\tag{2.5}
$$

同源端点关系、渐近误差和正核心为

$$
\begin{aligned}
\widetilde\psi(a_j)-a_j&=-c_0\sqrt{a_j},\\
a_j-\widetilde\vartheta(a_j)&=\sqrt{2a_j},\\
Q(t)&=t+O(t^{1-\eta}\log t),\qquad Q'(t)\to1,\\
\widetilde\psi(t)&=t+O(t^{1-\eta}\log t),\\
\widetilde K(a)&=c_0\int_a^\infty\sqrt t\,k(t)\,dt,\qquad
T(a)\widetilde K(a)\to2c_0>1/2.
\end{aligned}
\tag{2.6}
$$

然而完整的归一尾项满足

$$
\boxed{
T(a_j)\widetilde I(a_j)
=-b a_j^{1/2-\eta}\log a_j-2c_0+o(1)\longrightarrow-\infty.
}
\tag{2.7}
$$

因而上述联合标量合同没有蕴含最终统一有限下界。

**证明：共同定义域与支撑线。** 峰支撑是
$[(1-\delta)a_j,(1+\delta)a_j]$，因 $a_{j+1}=2a_j$ 而两两不交。
$\chi$ 及其前两阶导数在接缝处连续，所以 $h$ 为 $C^2$，并且

$$
h(a_j)=ba_j^{-\eta},\qquad h'(a_j)=0,\qquad
h(x)\le h(a_j)\ (x\ge a_j),
\tag{2.8}
$$

$$
h'(x)=O(x^{-1-\eta}),\qquad
h''(x)=O(x^{-2-\eta}).
\tag{2.9}
$$

这是对每个支撑区间使用 $x\asymp a_j$ 的一致界；支撑之外两阶导数为零。
由于 $g(x)\asymp1/(x\log x)$、$k(x)\asymp1/(x^2\log x)$，
$|h'|/g$ 与 $|h''|/k$ 都趋零。可取共同 $x_0$ 使
$U'>0$、$U''<0$，且 $U'\downarrow0$ 于 $[x_0,\infty)$。
因此其逆在 $(0,U'(x_0)]$ 定义良好。

在每个 $a_j\ge x_0$，$U'(a_j)=g(a_j)$。
凹函数支撑线直接给

$$
U(x)-g(a_j)x\le U(a_j)-g(a_j)a_j\qquad(x\ge x_0).
\tag{2.10}
$$

低于 $x_0$ 的有限整数补丁，其目标值为 $m^{-g(a_j)}\le1$；
来源目标值是

$$
\exp(U(a_j)-g(a_j)a_j)
=e^\gamma\log a_j\,
\exp\!\left(ba_j^{-\eta}-\frac1{\log a_j}\right)\longrightarrow\infty.
$$

所以一个共同 $J$ 后，式（2.10）覆盖全部整数 $m\ge1$ 的目标比较。
大整数范围内 $\widetilde G(m)=e^{\gamma+h(\log m)}$，
式（2.8）给全部 $m\ge n_j$ 的右尾比较及所有素数插入比较。
唯一素因子为 $2$；共同 $J$ 可再保证
$a_j-\log2\ge x_0$ 且 $\log2<\delta a_j$。
此时该点在第 $j$ 个峰支撑内，$0\le\chi\le1$ 给
$h(a_j-\log2)\le h(a_j)$，得到删除比较，且 $n_j/2>e$。

**证明：单调累积量与前向比较。** 因 $g$ 与 $U'$ 都严格递减，
$Q=(U')^{-1}\circ g$ 严格递增，且 $Q(a_j)=a_j$。
由 $U'(x)/g(x)\to1$ 得 $g(Q(t))/g(t)\to1$，故 $Q(t)/t\to1$。
具体地，若对某固定 $\varepsilon>0$ 有 $Q(t)\ge(1+\varepsilon)t$，
则 $g(Q(t))/g(t)\le g((1+\varepsilon)t)/g(t)\to(1+\varepsilon)^{-1}<1$；
另一侧用 $(1-\varepsilon)t$ 同理排除。

等式 $g(Q(t))-g(t)=-h'(Q(t))$ 与均值定理、式（2.9）给
$Q(t)-t=O(t^{1-\eta}\log t)$。隐函数求导又给

$$
Q'(t)=\frac{g'(t)}{U''(Q(t))}
=\frac{k(t)}{k(Q(t))-h''(Q(t))}\longrightarrow1.
\tag{2.11}
$$

因此增大共同 $t_0$ 后，式（2.4）的三项全部正且严格递增，
仍有 $g(t_0)\le U'(x_0)$。同时增大 $J$ 使 $a_J\ge t_0$。
直接求导并使用 $U'(Q(t))=g(t)$，得到

$$
\widetilde H'(t)=k(t)(Q(t)-t),\qquad
\widetilde H(a_j)=\gamma+ba_j^{-\eta}.
\tag{2.12}
$$

这里导数公式保留全部 $Q(t)-t$，没有丢弃负部。
凹函数 $f$ 的支撑线给

$$
\widetilde H(t)=\gamma+h(Q(t))
+[f(Q(t))-f(t)-g(t)(Q(t)-t)]
\le\gamma+h(Q(t)).
\tag{2.13}
$$

对 $t\ge a_j$，单调性给 $Q(t)\ge a_j$，
式（2.8）遂给 $\widetilde H(t)\le\widetilde H(a_j)$。
结合式（2.12）积分即得式（2.5）。

**证明：完整尾积分与正核心。** 由 $Q(t)/t\to1$ 及二阶余项，
式（2.13）的方括号为 $O(t^{-2\eta}\log t)\to0$，
且 $h(Q(t))\to0$，所以 $\widetilde H(t)\to\gamma$。
绝对积分有界性由

$$
|(Q(t)-t)k(t)|=O(t^{-1-\eta}),\qquad
\sqrt t\,k(t)=O(t^{-3/2}/\log t)
\tag{2.14}
$$

承担；$\widetilde I$ 和 $\widetilde K$ 也因此绝对收敛。
在 $[a_j,\infty)$ 积分式（2.12）给

$$
\int_{a_j}^\infty(Q(t)-t)k(t)\,dt=-ba_j^{-\eta}.
\tag{2.15}
$$

式（2.4）给 $Q-\widetilde\psi=c_0\sqrt t$，
故 $\widetilde I(a_j)=-ba_j^{-\eta}-\widetilde K(a_j)$。
这也证明式（1.4）的完整账本与端点关系。

令 $R=\log a$，代换 $t=ae^v$，得到

$$
T(a)\int_a^\infty\sqrt t\,k(t)\,dt
=\int_0^\infty e^{-v/2}
\frac{R(1+R+v)}{(R+v)^2}\,dv\longrightarrow2.
\tag{2.16}
$$

当 $R\ge1$ 时分式至多 $2$，对每个固定 $v$ 趋于 $1$；
支配收敛直接给所写极限。
因此 $T(a)\widetilde K(a)\to2c_0$。
$2c_0=2\sqrt2-2>1/2$，结合式（2.15）得到式（2.7）。
$0<\eta<1/2$ 使负项的量级趋于无穷。
所有用到的阈值只有有限项，取其共同最大值即可同时满足全部量词。$\square$

## 3. 真实算术没有被合同恢复

**定理 3.1（普通约数响应的明确不实现）。**
定理 2.2 的 $\widetilde Z$ 不等于普通约数响应 $\sigma(n)/n$。
$\widetilde\psi$ 也不等于普通素数幂的 Chebyshev 函数。

**证明。** 在同一个整数 $n_j=2^{2^j}$ 上，有限几何和给

$$
\frac{\sigma(n_j)}{n_j}=2-2^{-2^j}<2,
\qquad
\widetilde Z(n_j)=e^\gamma\log a_j\,e^{ba_j^{-\eta}}\longrightarrow\infty.
\tag{3.1}
$$

因此两者在全部充分大的来源上不相等。
式（2.11）保证 $\widetilde\psi$ 最终连续可微；
普通 $\psi$ 在每个普通素数处有正跳跃 $\log p$，
素数无穷性保证这些跳跃超出任何有限阈值，所以二者不能相等。

定理 2.2 保留的是式（1.3）—（1.4）的联合标量关系，
没有把式（3.1）中的两项识别成同一个算术函数。
尤其 $\widetilde\vartheta=\widetilde\psi-\sqrt t$ 重现端点数值，
并未提供普通素数幂共同关系
$\psi(t)=\sum_{r\ge1}\vartheta(t^{1/r})$ 或 Riemann $\zeta$ 的显式公式。
因此式（2.7）否定的是只依赖这些松弛合同的统一下界推论；
它没有给出实际来源类中的反例，也没有证明或反驳 RH。$\square$

## 追加锚（本行以下为增补区）
