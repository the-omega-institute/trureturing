<!-- editorial:front-matter:begin -->

# Robin 裕量的三项非负预算、递归酉实现与 Mellin 判据

> **编者说明（来源与证明边界）。** 下文完整保留所供原稿的论述、七节、七个定理、原公式编号和链接；只转换 Markdown 数学分隔符并添加显式锚。原稿的第一人称、“上一轮”“项目已经证明”及“本轮已经完成”等表述均是原稿自述，其证明归属按各处编者注限定；这里的纸面推导不表示本次 Lean 核验、原生控制取得或 RH 证明。原稿 SHA-256 为 `d57d021335a946a0070a1dfb4581162f0606e1741a99e5776b60e80a95b4743a`。编者注与原稿分开，保留未定位的匹配终点前提，并补明积分、谱群和证书取得的适用条件。

正文导航：[一](#section-1) · [二](#section-2) · [三](#section-3) · [四](#section-4) · [五](#section-5) · [六](#section-6) · [七](#section-7)。

定理：[1](#theorem-1) · [2](#theorem-2) · [3](#theorem-3) · [4](#theorem-4) · [5](#theorem-5) · [6](#theorem-6) · [7](#theorem-7)。

原编号公式：[1](#eq-1) · [2](#eq-2) · [3](#eq-3) · [4](#eq-4) · [5](#eq-5) · [6](#eq-6) · [7](#eq-7) · [8](#eq-8) · [9](#eq-9) · [10](#eq-10) · [11](#eq-11) · [12](#eq-12) · [13](#eq-13) · [14](#eq-14) · [15](#eq-15) · [16](#eq-16) · [17](#eq-17) · [18](#eq-18) · [19](#eq-19) · [20](#eq-20) · [21](#eq-21) · [22](#eq-22) · [23](#eq-23) · [24](#eq-24) · [25](#eq-25) · [26](#eq-26) · [27](#eq-27)。

<!-- editorial:front-matter:end -->

这次可以把前面的思路推进成一条更完整的定理链：

<a id="source-display-001"></a>

$$
\boxed{
\text{原整数的 Robin 裕量}
=
\text{一个有符号的素数振荡项}
+
\text{三个明确的非负算术量}.
}
$$

而且，这三个非负量中的未读余量，确实能做到：

<a id="source-display-002"></a>

$$
\boxed{
\text{每继续读取三层，余量至多减半；相应三轴读出有真正的酉实现。}
}
$$

这两点可以证明。接下来还可以证明：**如果把“稳定”进一步落实为素数振荡项在所有充分大尺度上的统一下界，就足以推出 RH。** 目前尚未证明这个统一下界，因此下面是一组已完成的中间定理，以及一个明确的最终证明目标。

我沿用项目中的[实际优化器与两价格缺口](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/Blueprint/D5/S3/Arith/Robin/ActualTwoPriceDefect.md)、[素数幂层的根尺度修正](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/Blueprint/D5/S3/Arith/Robin/EulerLayerRootCorrection.md)，以及 [AURIC 三轴误差与酉相容性 V35](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/docs/develop/theory/AURIC_THREE_AXIS_ERROR_GEOMETRY_UNITARY_COMPATIBILITY_AND_ENDOGENOUS_STABILITY_V35.md)。以下新增部分是纸面推导，不将它们标为已经完成的 Lean 核验，也不主张文献首创。

---

<a id="section-1"></a>

# 一、先证明：每个素数的有限指数，都带有严格正的差额

以下所有对数均为自然对数。

对素数 $p$，定义

<a id="source-display-003"></a>

$$
S_p(a)=1+\frac1p+\cdots+\frac1{p^a},
\qquad a\ge0.
$$

它是素数幂 $p^a$ 对 $\sigma(n)/n$ 的实际贡献。

定义两种层增量：

<a id="source-display-004"></a>

$$
\lambda_{p,j}
=
\log\frac{S_p(j)}{S_p(j-1)}
=
\log\left(1+\frac1{p+\cdots+p^j}\right),
$$

<a id="source-display-005"></a>

$$
\nu_{p,j}=\frac1{jp^j},
\qquad j\ge1.
$$

其中 $\lambda_{p,j}$ 是项目使用的实际乘法层收益；$\nu_{p,j}$ 来自 Euler 对数展开。

<a id="theorem-1"></a>

## 定理 1：两列总量相同，但有限前缀有严格的大小关系

对每个素数 $p$：

<a id="source-display-006"></a>

$$
\lambda_{p,1}<\nu_{p,1},
$$

<a id="source-display-007"></a>

$$
\lambda_{p,j}>\nu_{p,j}\qquad(j\ge2),
$$

而

<a id="source-display-008"></a>

$$
\sum_{j\ge1}\lambda_{p,j}
=
\sum_{j\ge1}\nu_{p,j}
=
-\log(1-1/p).
$$

因此，定义

<a id="source-display-009"></a>

$$
e_p(a)
=
\sum_{j=1}^{a}\frac1{jp^j}-\log S_p(a),
$$

便有

<a id="source-display-010"></a>

<a id="eq-1"></a>

$$
\boxed{
e_p(0)=0,\qquad e_p(a)>0\quad(a\ge1).
}
\tag{1}
$$

### 证明

第一层直接由 $\log(1+x)<x$ 得到：

<a id="source-display-011"></a>

$$
\lambda_{p,1}=\log(1+1/p)<1/p.
$$

对 $j\ge2$，利用 $\log(1+x)>x/(1+x)$：

<a id="source-display-012"></a>

$$
\lambda_{p,j}
>
\frac1{1+p+\cdots+p^j}.
$$

又因为 $p\ge2$，

<a id="source-display-013"></a>

$$
1+p+\cdots+p^j<2p^j\le jp^j,
$$

所以

<a id="source-display-014"></a>

$$
\lambda_{p,j}>\frac1{jp^j}=\nu_{p,j}.
$$

另一方面，实际层收益望远镜相消：

<a id="source-display-015"></a>

$$
\sum_{j\ge1}\lambda_{p,j}
=
\log\left(\lim_{a\to\infty}S_p(a)\right)
=
-\log(1-1/p).
$$

而对数级数给出同一个总量：

<a id="source-display-016"></a>

$$
\sum_{j\ge1}\nu_{p,j}
=
\sum_{j\ge1}\frac{p^{-j}}j
=
-\log(1-1/p).
$$

故对 $a\ge1$，

<a id="source-display-017"></a>

$$
\begin{aligned}
e_p(a)
&=\sum_{j\le a}(\nu_{p,j}-\lambda_{p,j})\\
&=\sum_{j>a}(\lambda_{p,j}-\nu_{p,j})\\
&>0.
\end{aligned}
$$

证毕。

这个结论与“总量守恒”直接对应：

> 第一层的差额，恰好等于全部后续层差额的总和；截取任何有限指数后，仍保留一个严格正的未展开部分。

尤其有精确递归：

<a id="source-display-018"></a>

<a id="eq-2"></a>

$$
\boxed{
e_p(a)
=
\bigl(\lambda_{p,a+1}-\nu_{p,a+1}\bigr)
+
e_p(a+1).
}
\tag{2}
$$

右侧两项均为正。

<!-- editorial:recursion-domain:begin -->

**编者注（式 (2) 的正性范围）。** 这里的指数均为非负整数，层号为正整数；式 (2) 作为恒等式对 $a\ge0$ 成立，但“两项均为正”只适用于 $a\ge1$。在 $a=0$ 时，第一项是 $\lambda_{p,1}-\nu_{p,1}<0$，由它与 $e_p(1)>0$ 相消得到 $e_p(0)=0$。两列均由几何级数或对数级数绝对收敛，故前缀与尾和的相减合法；后文只对 $p\mid n$ 的 $a_p\ge1$ 使用正递归。

<!-- editorial:recursion-domain:end -->

---

<a id="section-2"></a>

# 二、把原整数的 Robin 裕量，精确分到三个非负轴上

现在固定**实际整数**

<a id="source-display-019"></a>

$$
n>5040,
\qquad
T=\log n,
\qquad
a_p=v_p(n).
$$

定义

<a id="source-display-020"></a>

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n}.
$$

Robin 不等式就是 $R(n)<1$，等价于

<a id="source-display-021"></a>

$$
-\log R(n)>0.
$$

Robin 判据说明，所有 $n>5040$ 都满足这一严格不等式，当且仅当 RH 成立。[arxiv.org](https://arxiv.org/pdf/2110.13478?utm_source=chatgpt.com)

取价格

<a id="source-display-022"></a>

$$
q=\frac1{T\log T},
\qquad
z_p=q\log p,
$$

并定义基准指数

<a id="source-display-023"></a>

$$
b_p=\left\lfloor\frac{\log T}{\log p}\right\rfloor.
$$

也就是：

<a id="source-display-024"></a>

$$
p^j\le T\iff j\le b_p.
$$

由于 $x\log x$ 在 $x>1$ 上递增，

<a id="source-display-025"></a>

$$
j\le b_p
\Longrightarrow
\nu_{p,j}\ge z_p,
$$

<a id="source-display-026"></a>

$$
j>b_p
\Longrightarrow
\nu_{p,j}<z_p.
$$

于是可以定义三个有限的非负量。

| 量 | 定义 | 算术含义 |
|---|---|---|
| $E(n)$ | $\displaystyle\sum_{p\mid n}e_p(a_p)$ | 有限指数的严格正差额 |
| $M(n)$ | $\displaystyle\sum_p\sum_{a_p<j\le b_p}(\nu_{p,j}-z_p)$ | 缺少基准层的代价 |
| $U(n)$ | $\displaystyle\sum_p\sum_{b_p<j\le a_p}(z_p-\nu_{p,j})$ | 超过基准层的代价 |

所有空和均取零。虽然记号中写了 $\sum_p$，这些和都是有限的：只有 $p\mid n$ 或 $p\le T$ 可能贡献。

<!-- editorial:cutoff-domains:begin -->

**编者注（实际整数、等号与有限性）。** 全文 $n$ 是正整数，$\sigma(n)=\sum_{d\mid n}d$，$\gamma$ 是 Euler–Mascheroni 常数，$v_p(n)$ 是原整数的素数赋值；$n>5040$ 保证 $T=\log n>1$。对正层号 $j$，$\nu_{p,j}\ge z_p$ 等价于 $p^j\log(p^j)\le T\log T$，从而等价于 $p^j\le T$；等号恰在 $p^j=T$。$p>T$ 时 $b_p=0$。每个基准前缀有限，实际支持也有限；$n>1$ 至少有一个 $a_p\ge1$，故 $E>0$，而 $M,U$ 可以为零。这里和后文的 Euler 因子始终属于同一个实际 $n$。

<!-- editorial:cutoff-domains:end -->

特别地，

<a id="source-display-027"></a>

<a id="eq-3"></a>

$$
\boxed{
E(n)>0,\qquad M(n)\ge0,\qquad U(n)\ge0.
}
\tag{3}
$$

<a id="theorem-2"></a>

## 定理 2：实际整数的三项非负分解

定义

<a id="source-display-028"></a>

$$
\psi(t)=\sum_{p^j\le t}\log p,
$$

<a id="source-display-029"></a>

$$
\kappa(t)=\frac{\log t+1}{t^2(\log t)^2},
$$

以及有符号的尾积分

<a id="source-display-030"></a>

$$
I_\psi(T)
=
\int_T^\infty \kappa(t)\bigl(\psi(t)-t\bigr)\,dt.
$$

则有精确恒等式

<a id="source-display-031"></a>

<a id="eq-4"></a>

$$
\boxed{
-\log R(n)
=
I_\psi(T)+E(n)+M(n)+U(n).
}
\tag{4}
$$

这里的 $a_p$ 始终是原整数 $n$ 的指数。

### 证明第一步：把三个非负量合起来

记

<a id="source-display-032"></a>

$$
S(T)=\sum_{p^j\le T}\frac1{jp^j}.
$$

对每个素数，直接比较实际前缀 $1,\ldots,a_p$ 与基准前缀 $1,\ldots,b_p$，得到

<a id="source-display-033"></a>

$$
\begin{aligned}
&e_p(a_p)
+\sum_{a_p<j\le b_p}(\nu_{p,j}-z_p)
+\sum_{b_p<j\le a_p}(z_p-\nu_{p,j})\\
&\qquad=
\sum_{j\le b_p}\nu_{p,j}
-\log S_p(a_p)
+(a_p-b_p)z_p.
\end{aligned}
$$

对所有素数求和，使用

<a id="source-display-034"></a>

$$
\sum_p a_p\log p=T,
\qquad
\sum_p b_p\log p=\psi(T),
$$

以及

<a id="source-display-035"></a>

$$
\log\frac{\sigma(n)}n=\sum_p\log S_p(a_p),
$$

得

<a id="source-display-036"></a>

<a id="eq-5"></a>

$$
\boxed{
E+M+U
=
S(T)-\log\frac{\sigma(n)}n
+\frac{T-\psi(T)}{T\log T}.
}
\tag{5}
$$

### 证明第二步：尾积分也有有限表达

Abel 分部求和给出

<a id="source-display-037"></a>

<a id="eq-6"></a>

$$
\boxed{
I_\psi(T)
=
\frac{\psi(T)-T}{T\log T}
+\gamma+\log\log T-S(T).
}
\tag{6}
$$

说明一下无穷端点。Mertens 乘积定理给出

<a id="source-display-038"></a>

$$
\log\prod_{p\le X}(1-1/p)^{-1}
-\log\log X\longrightarrow\gamma.
$$

左侧乘积的对数与 $S(X)$ 的差，只是那些满足 $p\le X<p^j$ 的跨界幂尾；这个尾趋于零。再由 $\psi(X)=O(X)$，端点项

<a id="source-display-039"></a>

$$
\frac{\psi(X)-X}{X\log X}
$$

也趋于零，因而得到式 (6)。这里不需要 RH。Mertens 乘积公式及其在这条研究路线中的作用，也是经典 Ramanujan—Robin 方法的基础。[arxiv.org](https://arxiv.org/pdf/1211.6944?utm_source=chatgpt.com)

<!-- editorial:abel-endpoints:begin -->

**编者注（式 (6) 的端点与收敛）。** 本文 $\psi$ 是包含端点所有素数幂、每幂权为 $\log p$ 的右连续函数。令 $f(t)=1/(t\log t)$。在有限区间使用 $(T,X]$ 的 Stieltjes 积分，$d\psi$ 给出 $S(X)-S(T)$，而 $f'=-\kappa$，故

$$
\int_T^X\kappa(t)(\psi(t)-t)\,dt
=f(T)(\psi(T)-T)-f(X)(\psi(X)-X)
+S(X)-S(T)-\log\log X+\log\log T.
$$

跨界幂尾可直接界定：对 $p\le\sqrt X$，令 $k$ 为最小满足 $p^k>X$ 的层号，则其尾至多 $2/X$；这部分总量至多 $2/\sqrt X$。对 $\sqrt X<p\le X$，尾从第二层开始，至多 $2/p^2$，求和不超过 $2\sum_{m>\sqrt X}m^{-2}=O(X^{-1/2})$。因此 $S(X)-\log\log X\to\gamma$，配合 $\psi(X)=O(X)$ 即得式 (6) 的不定上限极限。第六节所引无条件 PNT 误差还保证 $I_\psi$ 绝对收敛。Kedlaya 的显式公式采用素数幂处的半跳值 $\psi_0$；它与这里的右连续 $\psi$ 在普通积分中相同，但不能在式 (6) 的有限端点项中不作调整就替换。

<!-- editorial:abel-endpoints:end -->

将式 (5)、(6) 相加：

<a id="source-display-040"></a>

$$
I_\psi(T)+E+M+U
=
\gamma+\log\log T-\log\frac{\sigma(n)}n
=
-\log R(n).
$$

证毕。

**现在，三轴确实有了具体的算术内容。** 令

<a id="source-display-041"></a>

$$
\mathcal C(n)=E(n)+M(n)+U(n)>0,
$$

则

<a id="source-display-042"></a>

$$
\left(
\frac{E(n)}{\mathcal C(n)},
\frac{M(n)}{\mathcal C(n)},
\frac{U(n)}{\mathcal C(n)}
\right)
$$

是非负、总和为 $1$ 的三轴读出。另行保留总量 $\mathcal C(n)$，便没有丢掉 Robin 裕量所需的尺度。

同时，式 (4) 已经证明一个有效分类：

<a id="source-display-043"></a>

<a id="eq-7"></a>

$$
\boxed{
I_\psi(\log n)\ge0
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{7}
$$

所有可能的反例，都必须位于 $I_\psi(\log n)<0$ 的尺度上，并且其负值必须足以抵消三个正量。

<!-- editorial:three-axes:begin -->

**编者注（非负轴与严格性）。** “三个正量”应依式 (3) 理解为 $E>0$、$M,U\ge0$，不要求三者都严格正。式 (7) 的严格性来自 $E>0$。三个归一化数和独立保留的 $\mathcal C$ 给出这些聚合算术量；这种表示本身不供应原生物理制备、控制或读出。

<!-- editorial:three-axes:end -->

---

<a id="section-3"></a>

# 三、上一轮的无穷层修正，其实是有限的非负素数和

上一轮有

<a id="source-display-044"></a>

$$
-\log R(n)=\mathcal D(n)+I_\psi(T)+K(T),
$$

其中 $\mathcal D(n)\ge0$ 是实际整数相对于价格最优整数的缺口，

<a id="source-display-045"></a>

$$
K(T)=\int_T^\infty\kappa(t)\bigl(A(t)-\psi(t)\bigr)\,dt,
$$

而 $A(t)$ 是项目的严格价格优化器之对数。

<!-- editorial:actual-optimizer:begin -->

**编者注（固定源码中的实际优化器与缺口）。** 本节使用开头所引固定提交的 `ActualTwoPriceDefect`，不是另选比较整数：`integerAt(t)=strictInteger(price(t))`，`price(t)=1/(t log t)`，`clock(t)=log(integerAt(t))`，故 $A(t)=\mathrm{clock}(t)$。`strict_layer_iff` 给出第 $j$ 层被取当且仅当 $q(t)\log p<\lambda_{p,j}$，等价价格层不取；`strictInteger_counts` 给出全部素数的完整前缀。`W(n)` 是 $\log(\sigma(n)/n)$，`pressure(q)` 是所有正整数的 $W(m)-q\log m$ 的上确界，`pressure_eq_of_optimal` 与 `pressure_maximal_spec` 给出正价格下的实际取到。因此本文 $\mathcal D(n)$ 精确对应 `defect(T,n)`：

$$
\mathcal D(n)=P(q(T))-W(n)+q(T)\log n\ge0,
\qquad P(q)=\mathrm{pressure}(q).
$$

$q(t)\log p\le\nu_{p,j}$ 则是 $p^j\le t$ 的参考层阈值。两种阈值的等号集合对 $t$ 为零测集，不影响积分。这里是固定源码的定义和定理选读，不是本次 Lean 重编译认证。

<!-- editorial:actual-optimizer:end -->

现在可以进一步证明：

<a id="theorem-3"></a>

## 定理 3：有限正修正定理

对 $T>1$，定义

<a id="source-display-046"></a>

$$
K_p(T)
=
\sum_{j\ge1}
\left[
\min(z_p,\lambda_{p,j})
-
\min(z_p,\nu_{p,j})
\right].
$$

则

<a id="source-display-047"></a>

<a id="eq-8"></a>

$$
\boxed{
K(T)=\sum_{p\le T}K_p(T),
}
\tag{8}
$$

并且

<a id="source-display-048"></a>

<a id="eq-9"></a>

$$
\boxed{
0\le K_p(T)\le
\frac1p-\log(1+1/p)<\frac1{2p^2}.
}
\tag{9}
$$

进一步，

<a id="source-display-049"></a>

<a id="eq-10"></a>

$$
\boxed{
T>2\Longrightarrow K(T)>0.
}
\tag{10}
$$

### 为什么无穷远的素数会精确抵消？

若 $p\ge T$，则

<a id="source-display-050"></a>

$$
z_p=\frac{\log p}{T\log T}\ge\frac1p.
$$

两列的每一项都不超过 $1/p$，所以所有 $\min$ 都直接取其第二个参数。于是

<a id="source-display-051"></a>

$$
K_p(T)
=
\sum_j\lambda_{p,j}-\sum_j\nu_{p,j}
=0.
$$

这使用的是逐素数的精确总量相等。

### 为什么剩下的每一项非负？

分三种情况即可。

若 $z_p\ge\nu_{p,1}$，已经知道 $K_p=0$。

若

<a id="source-display-052"></a>

$$
\lambda_{p,1}\le z_p<\nu_{p,1},
$$

则第一层加上全部高层后，恰有

<a id="source-display-053"></a>

$$
K_p=\nu_{p,1}-z_p>0.
$$

若 $z_p<\lambda_{p,1}$，第一层两个最小值相等；而所有 $j\ge2$ 都满足

<a id="source-display-054"></a>

$$
\min(z_p,\lambda_{p,j})
\ge
\min(z_p,\nu_{p,j}),
$$

充分高的层还严格大于。因此 $K_p>0$。

同一分情况证明也给出上界 (9)。当 $T>2$ 时，取 $p=2<T$，便得到 $K(T)>0$。

<!-- editorial:clipped-cases:begin -->

**编者注（三种情形的缺省细节）。** $\lambda_{p,j}$、$\nu_{p,j}$ 都严格递减且趋零，且 $j\ge2$ 时 $\nu_{p,j}<\lambda_{p,j}<\lambda_{p,1}$。所以中间情形的所有高层均未被截断，利用总量相等得到 $K_p=\nu_{p,1}-z_p$。最后情形中，每个高层的最小值差介于零和 $\lambda_{p,j}-\nu_{p,j}$ 之间；充分高的层两者都小于 $z_p>0$，差严格正。故该情形的总量至多 $\sum_{j\ge2}(\lambda_{p,j}-\nu_{p,j})=\delta_p$，其中 $\delta_p=1/p-\log(1+1/p)=\int_0^{1/p}u/(1+u)\,du<1/(2p^2)$。$p<T$ 时 $z_p<\nu_{p,1}$，因而严格正；$p=T$ 时精确为零。“有限和”指外层素数支持有限，内层仍是收敛级数；取有限 $J\ge1$ 使其后两列均小于 $z_p$，可写成前 $J$ 个截断差加上已知尾 $e_p(J)$，不等于声称超越常数已有机器精确计算。

<!-- editorial:clipped-cases:end -->

### 求和与积分为什么可以交换？

逐层积分恰好给出上述两个 $\min$ 的差。并且

<a id="source-display-055"></a>

$$
\sum_p\sum_{j\ge1}
|\lambda_{p,j}-\nu_{p,j}|
=
2\sum_p
\left[\frac1p-\log(1+1/p)\right]
<
\sum_p\frac1{p^2}
<\infty.
$$

因此差值具有绝对可积的总控制，交换求和与积分是合法的。

<!-- editorial:fubini-and-defect:begin -->

**编者注（逐层积分与同整数的式 (11)）。** 置 $y=q(t)\log p$，则 $dy=-\kappa(t)\log p\,dt$，$y$ 从 $z_p$ 降到零。两层指标函数之差的加权积分等于 $\min(z_p,\lambda_{p,j})-\min(z_p,\nu_{p,j})$；其绝对值积分恰为该最小值差的绝对值，且不超过 $|\lambda_{p,j}-\nu_{p,j}|$。原文的可和控制因此是真正的绝对 Fubini 控制，不是分别对两个发散总量作交换。另令

$$
Q_\nu(T)=\sum_{p,j}(\nu_{p,j}-z_p)_+
=S(T)-q(T)\psi(T).
$$

实际完整层优化给 $P(q(T))=\sum_{p,j}(\lambda_{p,j}-z_p)_+$。逐素数总量相等和上述绝对控制给 $K=Q_\nu-P$。式 (5) 遂给 $E+M+U=Q_\nu-W(n)+q(T)T=\mathcal D(n)+K$。这里的 $\mathcal D$、$T=\log n$ 和全部赋值都是同一个 $n$，并由式 (4) 得回本节开头的分解。

<!-- editorial:fubini-and-defect:end -->

这一结果把上一轮的渐近正修正，推进成了**任意有限尺度上的严格非负分解**。

与第二节的三轴相接，得到

<a id="source-display-056"></a>

<a id="eq-11"></a>

$$
\boxed{
E(n)+M(n)+U(n)=\mathcal D(n)+K(T).
}
\tag{11}
$$

在先前证明的匹配价格贪心终点 $N$ 上，

<a id="source-display-057"></a>

$$
\mathcal D(N)=0,\qquad M(N)=0,
$$

<!-- editorial:matched-terminal:begin -->

**编者注（式 (12) 的匹配终点前提：ASSUMED-UNVERIFIED）。** 原稿“先前证明的匹配价格贪心终点”是原稿对既有工作的自述。在所引固定优化器、根修正源码及其相邻 Robin 源码的限定核对范围内，没有定位到同时供应该终点及这两个结论的声明；这里不依赖待交付文稿，也不补造供应定理。两个零值须分开：若同一个 $N$ 确实在 $q(\log N)$ 取得 $P$，则由实际缺口定义立即有 $\mathcal D(N)=0$；在此条件下，所有 $j\ge2$ 且 $p^j\le T$ 的层因 $\lambda_{p,j}>\nu_{p,j}\ge z_p$ 都必被取，但第一层满足相反的 $\lambda_{p,1}<\nu_{p,1}$，不能沿用该推理。$M(N)=0$ 还需要每个 $p<T$ 的基准第一层都在同一 $N$ 中；$p=T$ 的第一层缺失项权为零。仅有任意价格的优化性甚至不保证 $\mathcal D(N)=0$，仅有自身匹配价格的优化性也没有给出所需的全部第一层条件。因此下列式 (12) 在这两个明示前提下成立，原稿对该实际终点已有证明的归属仍未验证。式 (4)、(8)–(11) 与后文固定任意 $n$ 的论证不使用此未定位前提。

<!-- editorial:matched-terminal:end -->

所以进一步简化为

<a id="source-display-058"></a>

<a id="eq-12"></a>

$$
\boxed{
-\log R(N)
=
I_\psi(T)+E(N)+U(N),
\qquad T=\log N.
}
\tag{12}
$$

---

<a id="section-4"></a>

# 四、递归误差确实收敛，而且可以证明酉收敛

这一节直接落实你提出的“结果、误差、总量守恒，继续递归分析”。

<a id="theorem-4"></a>

## 定理 4：每读取三层，未读余量至多减半

对所有素数 $p\ge2$、整数 $a\ge1$，有

<a id="source-display-059"></a>

<a id="eq-13"></a>

$$
\boxed{
\frac13p^{-a-1}
\le e_p(a)
\le\frac43p^{-a-1}.
}
\tag{13}
$$

因此

<a id="source-display-060"></a>

<a id="eq-14"></a>

$$
\boxed{
e_p(a+3)\le\frac12e_p(a).
}
\tag{14}
$$

### 证明

令 $x=p^{-a-1}\le1/4$。由精确尾表达，

<a id="source-display-061"></a>

$$
e_p(a)
=
-\log(1-x)
-
\sum_{j>a}\frac1{jp^j}.
$$

上界直接得到

<a id="source-display-062"></a>

$$
e_p(a)
\le-\log(1-x)
\le\frac{x}{1-x}
\le\frac43x.
$$

当 $a\ge2$ 时，

<a id="source-display-063"></a>

$$
\sum_{j>a}\frac1{jp^j}
\le
\frac{x}{(a+1)(1-1/p)}
\le\frac23x,
$$

而 $-\log(1-x)\ge x$，故 $e_p(a)\ge x/3$。

当 $a=1$ 时，

<a id="source-display-064"></a>

$$
e_p(1)
=
\frac1p-\log(1+1/p)
=
\int_0^{1/p}\frac{u}{1+u}\,du
\ge\frac1{3p^2}.
$$

因此式 (13) 对全部情形成立。进而

<a id="source-display-065"></a>

$$
\frac{e_p(a+3)}{e_p(a)}
\le\frac4{p^3}
\le\frac12.
$$

证毕。

现在固定原整数 $n$，定义

<a id="source-display-066"></a>

$$
E_h=\sum_{p\mid n}e_p(a_p+3h).
$$

这里 $a_p+3h$ 表示向后读取余量的深度，原整数仍然是同一个 $n$。

于是

<a id="source-display-067"></a>

<a id="eq-15"></a>

$$
\boxed{
0<E_h\le2^{-h}E_0.
}
\tag{15}
$$

已读出的正量则是有限和

<a id="source-display-068"></a>

$$
E_0-E_h
=
\sum_{p\mid n}
\sum_{j=a_p+1}^{a_p+3h}
(\lambda_{p,j}-\nu_{p,j}).
$$

令

<a id="source-display-069"></a>

$$
F=M(n)+U(n),\qquad
\mathcal C=E_0+F.
$$

定义递归三轴：

<a id="source-display-070"></a>

<a id="eq-16"></a>

$$
\boxed{
X_h=\frac{E_0-E_h}{\mathcal C},
\qquad
Y_h=\frac{E_h}{\mathcal C},
\qquad
Z_h=\frac F{\mathcal C}.
}
\tag{16}
$$

那么

<a id="source-display-071"></a>

$$
X_h,Y_h,Z_h\ge0,
\qquad
X_h+Y_h+Z_h=1,
$$

且

<a id="source-display-072"></a>

$$
Y_h\le2^{-h}\frac{E_0}{\mathcal C}.
$$

这就有了你要求的精确形式：

- 第一轴记录已读出的正量；
- 第二轴记录尚未读出的余量；
- 第三轴记录已经确定的其余代价；
- 每次递归保持总量，并将第二轴中的质量转入第一轴。

<a id="theorem-5"></a>

## 定理 5：上述三轴递归有真正的酉实现

定义

<a id="source-display-073"></a>

$$
\theta_h=\arccos\sqrt{\frac{E_h}{E_0}},
$$

以及单位向量

<a id="source-display-074"></a>

$$
v_h=
\begin{pmatrix}
\sqrt{E_0/\mathcal C}\sin\theta_h\\
\sqrt{E_0/\mathcal C}\cos\theta_h\\
\sqrt{F/\mathcal C}
\end{pmatrix}.
$$

其三个坐标的模平方，正是式 (16) 的三个读出。

令

<a id="source-display-075"></a>

$$
\mathsf R(\theta)=
\begin{pmatrix}
\cos\theta&\sin\theta&0\\
-\sin\theta&\cos\theta&0\\
0&0&1
\end{pmatrix}.
$$

这是实正交矩阵，因而也是酉矩阵。直接验证：

<a id="source-display-076"></a>

$$
v_h=\mathsf R(\theta_h)v_0,
$$

<a id="source-display-077"></a>

$$
v_{h+1}
=
\mathsf R(\theta_{h+1}-\theta_h)v_h.
$$

由 $E_h\to0$，有

<a id="source-display-078"></a>

$$
\theta_h\longrightarrow\frac\pi2.
$$

因此累计酉变换收敛：

<a id="source-display-079"></a>

$$
\boxed{
\mathsf R(\theta_h)
\longrightarrow
\mathsf R(\pi/2)
}
$$

而且具有明确的算子范数误差界：

<a id="source-display-080"></a>

<a id="eq-17"></a>

$$
\boxed{
\left\|
\mathsf R(\theta_h)-\mathsf R(\pi/2)
\right\|
\le
\sqrt2\,2^{-h/2}.
}
\tag{17}
$$

所以这里同时证明了：

<a id="source-display-081"></a>

$$
\boxed{
\text{非负性、归一化、余量收缩、酉性、累计演化收敛}.
}
$$

按照项目原有五模式次序 $(N,2,3,5,25)$，可以把上述三个振幅放在模式 $2,5,3$ 上，另外两模式取零；其占据读出就是原 AURIC 的 $(X,Y,Z)$。这是明确选定的三维编码子空间。三个聚合读出及其总量得到保留，详细的逐层历史若也要保留，则需要相应的记录空间。

### 贪心读取也有收敛率

若 $r=\omega(n)$ 是不同素因子个数，每次选择当前未读余量最大的素数，再读取三层。

最大余量至少为总余量的 $1/r$，而此次读取至少消去它的一半，因此

<a id="source-display-082"></a>

<a id="eq-18"></a>

$$
\boxed{
E^{(k+1)}
\le
\left(1-\frac1{2r}\right)E^{(k)}.
}
\tag{18}
$$

这给出了同一原整数内部的贪心收敛定理。

<!-- editorial:recursion-unitary:begin -->

**编者注（递归、退化边与范数速率）。** $h,k$ 为非负整数，允许 $h=0$；$r=\omega(n)\ge1$。式 (13) 在 $a\ge2$ 时使用 $(a+1)(1-1/p)\ge3/2$；在 $a=1$ 时，$u\le1/p\le1/2$ 使 $u/(1+u)\ge2u/3$，积分即得 $1/(3p^2)$。原有尾表达由 $S_p(a)=(1-p^{-a-1})/(1-p^{-1})$ 得到。式 (15) 是有限支持上的逐项三层估计；读取后的 $a_p+3h$ 不是把原整数改成新整数。$E_0>0$ 保证 $\mathcal C>0$，即使 $F=0$，所有振幅和角度仍定义良好。$\theta_0=0$，$v_0=(0,\sqrt{E_0/\mathcal C},\sqrt{F/\mathcal C})^{\mathsf T}$，所列旋转符号确给 $v_h$。令 $d_h=\pi/2-\theta_h\in[0,\pi/2]$，旋转弦长公式给

$$
\|\mathsf R(\theta_h)-\mathsf R(\pi/2)\|_{\mathrm{op}}
=2\sin(d_h/2)
\le\sqrt2\sin d_h
=\sqrt{2E_h/E_0}\le\sqrt2\,2^{-h/2}.
$$

此处双竖线的含义为算子范数。固定提交 V35 的模式算子为 $N_1=\operatorname{diag}(0,1,0,0,1)$、$N_3=\operatorname{diag}(0,0,0,1,1)$、$N_2=\operatorname{diag}(0,0,1,0,0)$，读出次序是 $(N_1,N_3,N_2)$；把三振幅置于 $(2,5,3)$ 并令模式 $N,25$ 为零，正好保持 $(X_h,Y_h,Z_h)$。这是聚合质量的编码；完整逐素数逐层历史仍须另有记录空间。贪心每步只用有限 $r$ 个余量的最大者至少为总量的 $1/r$，故保留原式 (18) 的同整数速率；不由此取得自然零点谱的酉性。

<!-- editorial:recursion-unitary:end -->

---

<a id="section-5"></a>

# 五、与 Zeckendorf 遍历结合：得到逐整数完备的有限证明过程

定义有限层下界

<a id="source-display-083"></a>

$$
\begin{aligned}
L_h(n)
={}&I_\psi(\log n)+M(n)+U(n)\\
&+
\sum_{p\mid n}
\sum_{j=a_p+1}^{a_p+3h}
(\lambda_{p,j}-\nu_{p,j}).
\end{aligned}
$$

由前面的精确恒等式，

<a id="source-display-084"></a>

<a id="eq-19"></a>

$$
\boxed{
-\log R(n)-L_h(n)=E_h>0.
}
\tag{19}
$$

所以：

<a id="source-display-085"></a>

<a id="eq-20"></a>

$$
\boxed{
L_h(n)>0\Longrightarrow R(n)<1.
}
\tag{20}
$$

更进一步：

<a id="theorem-6"></a>

## 定理 6：有限递归证书的逐点完备性

对每个固定 $n>5040$，

<a id="source-display-086"></a>

<a id="eq-21"></a>

$$
\boxed{
R(n)<1
\iff
\exists h<\infty,\ L_h(n)>0.
}
\tag{21}
$$

### 证明

充分性已经由式 (19) 得到。

反过来，若

<a id="source-display-087"></a>

$$
\varepsilon=-\log R(n)>0,
$$

由于 $E_h\le2^{-h}E_0$，可以选有限 $h$ 使 $E_h<\varepsilon$。于是

<a id="source-display-088"></a>

$$
L_h(n)=\varepsilon-E_h>0.
$$

证毕。

项目的 [ZeckendorfGreedyPermutation](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md) 已证明 A370630 是正整数排列。因此，可以把它用作外层遍历次序，并对每个遇到的整数公平地继续上述递归：

<a id="source-display-089"></a>

$$
\text{Zeckendorf 遍历}
\longrightarrow
\text{实际素数幂分类}
\longrightarrow
\text{正量贪心读取}
\longrightarrow
\text{有限严格证书}.
$$

这样，**每一个实际上满足 Robin 不等式的整数，最终都会得到一个有限证书。**

要把这一步提升为 RH，还需要证明：对每个 $n>5040$，这个证书都会出现。式 (21) 保留了这一全称命题，没有在“遍历完整”或“余量趋零”中预先假定它。

<!-- editorial:pointwise-effective:begin -->

**编者注（逐点完备性与实际取得）。** 式 (19) 对同一 $n$ 给出严格正余隙，因而式 (21) 只对本来满足 $-\log R(n)>0$ 的点保证有限 $h$；等于零或小于零时，没有正的 $L_h$。固定的 Zeckendorf 源码 `result` 针对实际从 $1$ 开始、每步在全部未用正整数中选择与当前项恰共享一个标准 Zeckendorf 项的最小者的序列，包含正指标的单射和满射。公平交错的含义是每个已遇到的点继续获得任意多有限步骤，不能在第一个未决点一直阻塞外层遍历。这里的“有限证书”首先是有限 $h$ 对真实数表达式的严格不等式；要成为有效可执行的证书取得过程，仍须供应可认证的积分/常数区间与严格符号判定办法。对已有正间隙，收敛的认证区间才可最终识别其正性。排列定理、余量收敛与存在一个有限实数证书，各自都不供应这个取得接口，也不证明所有整数的证书均会出现。

<!-- editorial:pointwise-effective:end -->

---

<a id="section-6"></a>

# 六、再推进一步：什么样的“误差稳定”足以证明 RH？

现在正项递归的稳定性已经证明。剩下的对象是

<a id="source-display-090"></a>

$$
I_\psi(T).
$$

你的“不能发散”可以在这里写成一个很具体的数学要求：

<a id="source-display-091"></a>

$$
\sqrt T\log T\,I_\psi(T)
$$

不能沿充分大尺度向负无穷逃逸。

这实际上有一个严格的等价定理。

<a id="theorem-7"></a>

## 定理 7：归一化负尾有统一下界，当且仅当 RH 成立

下列两项等价：

1. RH 成立。
2. 存在常数 $C>0,T_0>1$，使所有实数 $T\ge T_0$ 满足

<a id="source-display-092"></a>

<a id="eq-22"></a>

$$
\boxed{
I_\psi(T)\ge-\frac{C}{\sqrt T\log T}.
}
\tag{22}
$$

注意量词是**所有充分大的实尺度**，而且 $C$ 与 $T$ 无关。

下面给出证明的关键步骤。

<a id="subsection-6-1"></a>

## 6.1 把尾积分换成适合 Mellin 分析的形式

定义

<a id="source-display-093"></a>

$$
J(x)=\int_x^\infty\frac{\psi(u)-u}{u^2}\,du,
$$

<a id="source-display-094"></a>

$$
B(x)=\frac{(\log x)^2}{\log x+1}.
$$

经典无条件素数定理误差界

<a id="source-display-095"></a>

$$
\psi(x)-x=O\!\left(xe^{-c\sqrt{\log x}}\right)
$$

保证这里的积分和下面的边界处理合法；此处仍然没有使用 RH。[kskedlaya.org](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com)

由分部积分，

<a id="source-display-096"></a>

<a id="eq-23"></a>

$$
\boxed{
J(x)
=
B(x)I_\psi(x)
+
\int_x^\infty B'(u)I_\psi(u)\,du,
}
\tag{23}
$$

其中

<a id="source-display-097"></a>

$$
B'(u)
=
\frac{\log u(\log u+2)}
{u(\log u+1)^2}>0.
$$

因此这是一个保持下界的正核转换。

<!-- editorial:positive-kernel:begin -->

**编者注（式 (23)–(24) 的边界）。** 用 $J'=-(\psi-x)/x^2$ 与 $I_\psi'=-\kappa(\psi-x)$ 的几乎处处导数，在有限区间先分部积分，再令上限趋无穷；第六节所引无条件 PNT 误差保证定义 $J$ 与 $I_\psi$ 的被积函数在各自尾区间上绝对可积。更具体地，$L=\log u$ 足够大时，$J(u)=O((\sqrt L+1)e^{-c\sqrt L})$、$I_\psi(u)=O(e^{-c\sqrt L}/\sqrt L)$，故 $B(u)I_\psi(u)\to0$。这给式 (23) 的正号。取 $x\ge\max(T_0,e)$，原式 (22) 的同一常数 $C$ 给

$$
\frac{B(x)}{\sqrt x\log x}\le x^{-1/2},
\qquad
\frac{B'(u)}{\sqrt u\log u}
=\frac{\log u+2}{u^{3/2}(\log u+1)^2}
\le u^{-3/2}.
$$

积分最后一项得 $2/\sqrt x$，所以确有式 (24)。这里及式 (22)、(26) 的量词都是全部充分大实数尺度、与尺度无关的同一常数，不是仅对 $\log n$ 的取样。

<!-- editorial:positive-kernel:end -->

若式 (22) 成立，则对充分大的 $x$，

<a id="source-display-098"></a>

$$
B(x)I_\psi(x)\ge-\frac C{\sqrt x},
$$

而积分项也不小于 $-2C/\sqrt x$。故

<a id="source-display-099"></a>

<a id="eq-24"></a>

$$
\boxed{
J(x)\ge-\frac{3C}{\sqrt x}.
}
\tag{24}
$$

<a id="subsection-6-2"></a>

## 6.2 一侧下界排除临界线右侧零点

对 $\Re s>0$，定义

<a id="source-display-100"></a>

$$
F(s)=\int_1^\infty J(x)x^{-s-1}\,dx.
$$

由 von Mangoldt 级数与积分交换，

<a id="source-display-101"></a>

<a id="eq-25"></a>

$$
\boxed{
F(s)
=
\frac{J(1)}s
+
\frac{\zeta'(s+1)}
{s(s+1)\zeta(s+1)}
+
\frac1{s^2}.
}
\tag{25}
$$

这里 $J(1)=-1-\gamma$，所以 $s=0$ 的表观极点相消。

<!-- editorial:mellin-cancellation:begin -->

**编者注（初始绝对交换及 Laurent 消去）。** 写 $\Lambda(m)=\log p$（$m=p^j$）而在其余正整数为零，令 $\sigma=\Re s>0$。无条件 PNT 误差给 $\int_1^\infty|\psi(u)-u|u^{-2}\,du<\infty$，故

$$
\int_1^\infty\int_x^\infty
\frac{|\psi(u)-u|}{u^2}x^{-\sigma-1}\,du\,dx
\le\frac1\sigma\int_1^\infty\frac{|\psi(u)-u|}{u^2}\,du<\infty.
$$

Euler 乘积在 $\Re(s+1)>1$ 的绝对收敛对数导数给

$$
H(s):=\int_1^\infty(\psi(u)-u)u^{-s-2}\,du
=-\frac{\zeta'(s+1)}{(s+1)\zeta(s+1)}-\frac1s.
$$

绝对 Fubini 或一次分部积分给 $F(s)=(J(1)-H(s))/s$，即式 (25)。沿实 $s\downarrow0$，支配收敛给 $H(s)\to J(1)$。DLMF 原链接式 25.2.4 的 Laurent 展开给 $\zeta'(1+s)/\zeta(1+s)=-1/s+\gamma+O(s)$，从而 $J(1)=-1-\gamma$，且

$$
\frac{\zeta'(1+s)}{s(s+1)\zeta(1+s)}
=-\frac1{s^2}+\frac{1+\gamma}{s}+O(1).
$$

所以二阶与一阶极点分别精确相消。初始积分仅在 $\Re s>0$ 定义全纯函数；其右式提供向左的亚纯延拓，不把延拓值冒作原积分已收敛。

<!-- editorial:mellin-cancellation:end -->

若 $\rho$ 是非平凡零点，则式 (25) 在

<a id="source-display-102"></a>

$$
s=\rho-1
$$

具有真正的极点。另一方面，它在实轴 $s>-1/2$ 上没有奇点：$\zeta$ 在 $0<s<1$ 没有实零点，而 $s=0$ 已作消去。所用的 Euler 乘积、Laurent 展开和解析延拓都是标准的 $\zeta$ 函数性质。[dlmf.nist.gov](https://dlmf.nist.gov/25.2?utm_source=chatgpt.com)

<!-- editorial:real-axis-poles:begin -->

**编者注（真实极点与实轴正则性）。** 对重数 $m_\rho$ 的非平凡零点，式 (25) 在 $s_\rho=\rho-1$ 的留数是 $m_\rho/[\rho(\rho-1)]\ne0$，其他显式项在那里全纯，故确为真极点。对实 $s>-1/2$，置 $r=s+1>1/2$；$r>1$ 的无零性来自 Euler 乘积，$0<r<1$ 时交错级数

$$
\eta(r)=\sum_{k\ge1}\bigl((2k-1)^{-r}-(2k)^{-r}\bigr)>0,
\qquad \zeta(r)=\frac{\eta(r)}{1-2^{1-r}}<0
$$

排除实零点，$s=0$ 已如上消去。此处使用的是 $r=s+1$ 的实零点事实；原文那句 $0<s<1$ 中的字母只是 zeta 的自变量。由复解析性与每个实点的非零性，取得的是这些实点邻域的全纯性，足够应用 Landau 引理，并未假定整个半平面无零点。

<!-- editorial:real-axis-poles:end -->

现在由式 (24)，对充分大的 $x$，

<a id="source-display-103"></a>

$$
g(x)=J(x)+3Cx^{-1/2}\ge0.
$$

它的 Mellin 变换等于式 (25)，加上一个只在 $s=-1/2$ 有极点的项，再减去一个有限区间积分。因此在实轴 $s>-1/2$ 上仍无奇点。

使用 **Landau 正性引理**：

> 非负函数的 Mellin 变换，如果具有有限收敛横坐标，那么该横坐标对应的实点必为奇点。

这个引理的原因很直接：假如该实点还能解析延拓，就可以在其右侧作 Taylor 展开；各阶导数对应的积分具有交替的确定符号。向左代入 Taylor 级数后，非负性允许交换求和与积分，于是得到超出原收敛横坐标的收敛，产生矛盾。

如果存在 $\Re\rho>1/2$，那么 $g$ 的 Mellin 变换在

<a id="source-display-104"></a>

$$
\Re(\rho-1)>-1/2
$$

处有极点，其收敛横坐标也必须大于 $-1/2$。Landau 引理便要求这个区间内的实轴出现奇点，与刚才的解析性矛盾。

因此不存在 $\Re\rho>1/2$ 的零点。再由函数方程的对称性，所有非平凡零点均在临界线上，RH 成立。

<!-- editorial:landau-tail:begin -->

**编者注（Landau 正性引理在这里的完整前提）。** 选固定 $X>1$ 使 $g(x)=J(x)+3Cx^{-1/2}\ge0$ 对 $x\ge X$ 成立，只考虑这条局部可积非负尾的变换 $G_X(s)$。初始 $\Re s>0$ 上有

$$
G_X(s)=F(s)-\int_1^X J(x)x^{-s-1}\,dx
+\frac{3C X^{-s-1/2}}{s+1/2}.
$$

有限区间项整函数，新增项只在 $-1/2$ 有极点，所以每个非实 $s_\rho$ 的真极点都保留。非负尾的收敛横坐标 $\sigma_c\le0$；若存在 $\Re\rho>1/2$，该极点使 $\sigma_c\ge\Re(\rho-1)>-1/2$，否则积分全纯性和解析延拓唯一性会排除它。这同时排除了 $\sigma_c=-\infty$，故横坐标确为有限实数。若 $G_X$ 在实 $\sigma_c$ 仍全纯，选 $a>\sigma_c$ 足够近，使其 Taylor 圆盘含某个 $a-h<\sigma_c$。各阶导数可在收敛半平面内积分，代入 $-h$ 后每项为非负：

$$
G_X(a-h)=\sum_{k\ge0}\frac{h^k}{k!}
\int_X^\infty g(x)(\log x)^k x^{-a-1}\,dx.
$$

Tonelli 把右式化为 $\int_X^\infty g(x)x^{-(a-h)-1}\,dx<\infty$，违背横坐标定义。这证明所用正性引理，且原稿已给的实轴正则性造成矛盾。函数方程 $\xi(s)=\xi(1-s)$ 及共轭对称使每个左半临界带零点对应一个右半临界带零点，故排除后者即得 RH；该对称性见 [DLMF 25.4](https://dlmf.nist.gov/25.4)。这是从假设 (22) 出发的条件推论。

<!-- editorial:landau-tail:end -->

<a id="subsection-6-3"></a>

## 6.3 RH 反过来给出所需下界

将经典素数显式公式积分一次，可得

<a id="source-display-105"></a>

$$
J(x)
=
-\sum_\rho
\frac{x^{\rho-1}}{\rho(1-\rho)}
+
O(x^{-1}).
$$

积分后的零点和具有二次分母，绝对收敛。素数显式公式及零点计数的标准控制，给出了这一步的依据。[kskedlaya.org](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com)

<!-- editorial:explicit-limit:begin -->

**编者注（显式公式的积分极限）。** 原链接的 von Mangoldt 公式和零点计数给出 $N(H)=O(H\log H)$，所有零点均按重数计。先固定 $2\le x<b<\infty$，取不穿过零点的对称截断高度 $H\to\infty$。在 $[x,b]$ 上，截断误差由 $O_{x,b}((\log H)^2/H)$ 加上 $O_{x,b}(1)\min(1,O_{x,b}(1)/(H\langle u\rangle))$ 控制；后者除有限个素数幂外逐点趋零，并被可积常数控制。因此可以先积分再用支配收敛，而不对未积分零点级数作绝对交换。由 [von Mangoldt 公式原证明页](https://kskedlaya.org/ant/chap-von-mangoldt.html) 的同一误差控制，有限区间上得到

$$
\int_x^b\frac{\psi(u)-u}{u^2}\,du
=-\sum_\rho\frac{x^{\rho-1}-b^{\rho-1}}{\rho(1-\rho)}
-\frac{\zeta'(0)}{\zeta(0)}\left(\frac1x-\frac1b\right)
-\frac12\int_x^b\frac{\log(1-u^{-2})}{u^2}\,du.
$$

零点计数使 $\sum_\rho|\rho(1-\rho)|^{-1}<\infty$；在 $b\ge x\ge2$ 上每个分子模长至多二，且 $0<\Re\rho<1$ 使各个 $b^{\rho-1}\to0$。再次支配收敛令 $b\to\infty$。常数项为 $O(x^{-1})$，平凡零点的最后积分为 $O(x^{-3})$，半跳值与右连续值在积分中无差别。这就给出原稿的 $J$ 公式；在 RH 下逐项模长界统一给 $J(x)=O(x^{-1/2})$。所用的是积分后的绝对收敛，不是假定原始显式级数绝对收敛。

<!-- editorial:explicit-limit:end -->

在 RH 下，$\rho=1/2+i\tau_\rho$，所以

<a id="source-display-106"></a>

$$
J(x)=O(x^{-1/2}).
$$

再对式 (23) 作反向的分部积分转换，得到

<a id="source-display-107"></a>

$$
I_\psi(x)=O\!\left(\frac1{\sqrt x\log x}\right),
$$

从而式 (22) 成立。定理证毕。

<!-- editorial:inverse-ibp:begin -->

**编者注（反向转换的实际公式）。** 在 $x>1$ 置

$$
w(x)=\frac1{B(x)}=\frac{\log x+1}{(\log x)^2},
\qquad
w'(x)=-\frac{\log x+2}{x(\log x)^3}<0.
$$

由 $I_\psi(x)=-\int_x^\infty w(u)J'(u)\,du$ 直接分部积分，并用 $w(u)J(u)\to0$，得到

$$
I_\psi(x)=w(x)J(x)+\int_x^\infty w'(u)J(u)\,du.
$$

这第二项是负导数核，不能只由式 (23) 的正核下界倒推。RH 下 $|J(u)|\le A u^{-1/2}$，第一项为 $O(x^{-1/2}/\log x)$，第二项为 $O(x^{-1/2}/(\log x)^2)$；例如 $x\ge e$ 时用 $|w'(u)|\le3/[u(\log u)^2]$ 及 $\int_x^\infty u^{-3/2}\,du=2x^{-1/2}$。从而统一的大实数尺度界 (22) 确实成立。

<!-- editorial:inverse-ibp:end -->

这使下一步目标变得很集中：

<a id="source-display-108"></a>

<a id="eq-26"></a>

$$
\boxed{
\text{无条件证明 }
\inf_{T\ge T_0}
\bigl[\sqrt T\log T\,I_\psi(T)\bigr]>-\infty,
\quad\text{即可推出 RH。}
}
\tag{26}
$$

---

<a id="section-7"></a>

# 七、你提出的“酉性”，与 RH 还有一个精确的谱对应

前面已经证明了正预算递归的三维酉实现。现在可以进一步说明，**素数振荡本身所对应的自然谱演化**，需要满足什么酉性。

把非平凡零点按重数作为指标，定义

<a id="source-display-109"></a>

$$
\mathcal H=\ell^2(\{\rho\}),
$$

并令

<a id="source-display-110"></a>

$$
V(v)e_\rho
=
e^{(\rho-\frac12)v}e_\rho,
\qquad v\in\mathbb R.
$$

由于 $0<\Re\rho<1$，这些算子形成一个有界、强连续的一参数群。

<!-- editorial:spectral-boundedness:begin -->

**编者注（逐参数有界不等于群的一致有界）。** 零点按重数构成可数指标集，每个固定实 $v$ 上有 $\|V(v)\|_{\mathrm{op}}\le e^{|v|/2}$，且逐坐标乘法给群律与逆 $V(-v)$。在有界 $v$ 区间内该界统一，对每个 $\ell^2$ 向量的平方可和坐标应用支配收敛，即得强连续性。原文“有界”限于每个算子，未证明 $\sup_{v\in\mathbb R}\|V(v)\|<\infty$。式 (27) 的酉性等价由每个标准基向量的范数直接给出；若有 $\Re\rho\ne1/2$，取相应符号的无界 $v$ 就使该模态增长。重归一化不消除另行保留的质量增长，且前三轴的有限维酉编码不能供应此自然零点群的酉性。

<!-- editorial:spectral-boundedness:end -->

直接计算：

<a id="source-display-111"></a>

$$
\|V(v)e_\rho\|
=
e^{(\Re\rho-\frac12)v}.
$$

因此有：

<a id="source-display-112"></a>

<a id="eq-27"></a>

$$
\boxed{
V(v)\text{ 对所有 }v\text{ 都是酉算子}
\iff
\Re\rho=\frac12\text{ 对所有非平凡零点成立}
\iff
\mathrm{RH}.
}
\tag{27}
$$

这给你的直觉一个明确的数学落点：**应当证明的是，与素数显式公式相连的这个自然演化保持范数。**

如果某个零点偏离临界线，则对应模态包含

<a id="source-display-113"></a>

$$
e^{(\Re\rho-\frac12)v}.
$$

把它重新归一化，可以得到单位向量，但这个增长因子会进入被除去的总量；只要仍保留总量，它就依然存在。因此，前面已证明的三轴酉编码，并没有自动证明式 (27) 中的自然谱演化是酉的。

项目已经证明的根尺度修正

<a id="source-display-114"></a>

$$
K(T)
=
\frac{2(\sqrt2-1)+o(1)}{\sqrt T\log T}
$$

说明，正预算在关键尺度上具有确定的主项。经典 RH 条件下的零点控制，确实足以使这个正项压过负振荡，并恢复 Ramanujan 对充分大整数的严格 Robin 裕量；该条件性结果及其常数已有明确的经典来源。[arxiv.org](https://arxiv.org/pdf/1211.6944?utm_source=chatgpt.com)

<!-- editorial:root-and-classical-margin:begin -->

**编者注（根修正的供应范围、积分系数与经典归属）。** 固定 `EulerLayerRootCorrection.strict_inventory_root_correction_statement` 与 `strict_inventory_root_correction` 的实际陈述是：对每个 $\varepsilon>0$，存在同一实阈值，使全部更大实 $t$ 及满足完整严格层赋值的正整数 $U$ 都有

$$
\left|\frac{\log U-\psi(t)}{\sqrt t}-(\sqrt2-1)\right|<\varepsilon.
$$

它没有直接声明原稿的 $K$ 积分渐近式；后者是把该供应应用于同一个 $U=\mathrm{integerAt}(t)$ 的纸面推论。写 $A(t)-\psi(t)=(c+r(t))\sqrt t$，$c=\sqrt2-1$、$r(t)\to0$，则

$$
\sqrt T\log T\int_T^\infty\kappa(t)\sqrt t\,dt
=\int_1^\infty y^{-3/2}
\frac{\log T(\log(Ty)+1)}{(\log(Ty))^2}\,dy\longrightarrow2.
$$

$T\ge e$ 时被积式不超过 $2y^{-3/2}$；$r$ 项由 $\sup_{t\ge T}|r(t)|$ 乘该有界积分控制。因此积分系数确为 $2(\sqrt2-1)$。在 RH 下，经典零点恒等式

$$
\sum_\rho\frac1{\rho(1-\rho)}
=2+\gamma-\log(4\pi)=:B_0
$$

可由 DLMF 原链接的 Hadamard 乘积（25.2.12）对完成函数 $\xi$ 的对数导数在 $0,1$ 作差并用函数方程取得；二次分母保证交换与差分合法。在 RH 下这些分母为正数，第六节积分公式给 $\liminf\sqrt T\log T\,I_\psi(T)\ge-B_0$。故结合 $\mathcal D\ge0$ 的条件严格余量常数是

$$
2(\sqrt2-1)-B_0
=2\sqrt2-4-\gamma+\log(4\pi)>0.
$$

这里的严格正性及充分大整数结论沿用原有 Nicolas–Sondow 文献第 3 页所归属的 Ramanujan 条件定理及其第 9 页的校正归属，不作为本稿首创或本次新 Lean 证明；Robin 的全整数阈值等价另见 Axler 原链接命题 1.1。开头“项目已经证明”只归属上述固定根尺度供应，积分转换在此明示。最终 (26) 的无条件统一下界与 (27) 的自然谱酉性仍未取得。

<!-- editorial:root-and-classical-margin:end -->

**本轮已经完成的推进是：原整数的三项非负分解、无穷层修正的有限正和、每三层减半的递归、累计酉变换的范数收敛，以及逐整数完备的有限证书。** 接下来必须从素数算术独立证明的，是式 (26) 的统一负尾下界，或能够推出它的自然谱酉性。这个最后的全尺度控制，目前仍未证出。
