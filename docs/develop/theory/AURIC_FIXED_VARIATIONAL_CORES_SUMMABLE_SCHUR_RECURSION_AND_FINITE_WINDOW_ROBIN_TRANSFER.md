<a id="auric-fixed-variational-cores"></a>

# AURIC Fixed Variational Cores, Summable Schur Recursion, and Finite-Window Robin Transfer

> **Reader-visible source and scope note.** The manuscript body below is the complete supplied source, retained in its original order, including every prose passage, formula, proof, URL, numbered tag, and ending. Portable Markdown math delimiters let the canonical dollar-delimiter renderer parse the source expressions. Each original equation number is a separate caption attached to its unchanged display, preserving the association without covering formula glyphs.
>
> **Source record.** The source is `source.md` at the supplied artifact, SHA-256 <code>6a3c83879b263073<wbr>5351e02a46f21fd<wbr>ca0f79f56978a776<wbr>dd16e884eeb658fd4</code>, 23,833 bytes and 1,312 logical lines. The intended project pin is `18ab178472d8c29eb90d5e5f4e6c8b4c89038e84`; the AURIC v37 link and every other source URL remain in the body.
>
> **Navigation.** [Section I](#section-i-fixed-kernel-and-complete-energy-space) · [Section II](#section-ii-fixed-coarse-readout) · [Section III](#section-iii-fixed-finite-dimensional-core) · [Section IV](#section-iv-schur-recursion) · [Section V](#section-v-summable-corrections) · [Section VI](#section-vi-residual-lower-bound) · [Section VII](#section-vii-small-window-core) · [Section VIII](#section-viii-stable-greedy-expansion) · [Section IX](#section-ix-robin-transfer) · [Section X](#section-x-pnt-tail) · [Section XI](#section-xi-budget-margin) · [Section XII](#section-xii-what-closes)
>
> **Necessary premise note.** The bounded review treats the prior short-window cusp/triangle positivity, the prior low-frequency result for the reference weight, the stated small-scale asymptotic for the three-point readout, the A370630 greedy-permutation coverage, and the inherited finite-window constructions as `ASSUMED-UNVERIFIED` premises. The meanings and full provenance of `D(n)`, `A_inv(u)`, `B(T)`, the decomposition in (29), the Euler-layer root correction, and the normalized budget limit in (36) are likewise inherited and are not silently supplied by the Euler root asymptotic alone. Exact pinned-source correspondence was checked against the project materials for AURIC v37, Zeckendorf–Euler 5040 (equations 20–28 and sections 7–9), and EulerLayerRootCorrection; those reads establish scope and notation leads, not fresh kernel proofs.
>
> **C4 bounded whole-paper check.** Each item below was checked against the preserved source. `CHECKED` means the local algebra, functional-analytic interface, or stated implication is readable and internally aligned; `ASSUMED-UNVERIFIED` names a premise supplied by an earlier document or external theorem.
>
> - `CHECKED — sections I–II, kernel inventory:` the displayed kernel contains the smooth main term, the complete inverse-power series, and the prime-power layer; the stated value of `S` is retained exactly.
> - `CHECKED — measure and completion:` the decomposition `mu = a delta_0 + F'`, the reference energy `q_P`, the low-frequency half-mass argument for `alpha_D`, and the closed weighted completion are all present with their support and conjugation conventions.
> - `CHECKED — continuous actual form:` the signs and conjugation in (3), the logarithmic local behavior of `K'`, the finite-total-variation role of `R_D''`, and equality with the finite-atomic arithmetic form are stated.
> - `CHECKED — coarse interface:` the hat functions, partition of unity, continuous readout `C`, atomic section `J`, and the kernel characterization in (6) are retained.
> - `CHECKED — fine-grid coercivity:` the Fourier subtraction estimate, the coefficient `D h^2 R_0^3/(12 pi)`, the high-frequency bound on `w`, and the conclusion `B_D >= half q_P` on `Z` are each accounted for.
> - `CHECKED — fixed core:` existence and uniqueness of the constrained minimizer, the Riesz orthogonality condition, and the finite matrix definition are tied to the complete space and its closed kernel.
> - `CHECKED — positivity equivalence:` (9) and (10) give the exact decomposition and minimum; density of finite atoms plus continuity is the stated route for (11), with no claim that convergence alone proves the sign.
> - `CHECKED — one-node update:` (13) uses the fixed-cell affine interpolation; a genuinely new node gives a nonzero orthogonalized direction, so `e_k` is positive and the coupling column uses the Hermitian convention in (14).
> - `CHECKED — Schur step:` the update vector, substituted quadratic form, rank-one positive-semidefinite correction, and its direction are all explicit.
> - `CHECKED — dense limit:` moving-atom continuity, fiber correction by `J`, density in the fixed readout fiber, fixed coarse dimension, and operator-norm convergence are separately stated.
> - `CHECKED — summability:` the tail identity (16), positive-semidefinite trace calculation, and finite total correction (17)–(18) are distinguished from the unresolved sign comparison.
> - `CHECKED — posterior residual:` `R_k` acts on the whole `Z`; the lower bound on `A_Z`, the exact inverse formula, and the factor-two operator bound are retained.
> - `CHECKED — actual error matrix:` the finite atomic derivative functions, cell-average projection, complex Gram entries, positive-semidefinite `E_k`, and the implication from (22) to (24) are all present; automatic vanishing of this conservative bound is explicitly left unproved.
> - `ASSUMED-UNVERIFIED — small-window inheritance:` the earlier cusp/triangle comparison, formula (25), fixed-fiber Jensen minimization, strict gap (26)–(27), and the prior constants are used as supplied premises.
> - `ASSUMED-UNVERIFIED — stable greedy inheritance:` the A370630 permutation coverage and the local cusp estimate used to choose each new `h_j` are not reproved; the finite-old-constraint induction, row-sum estimate, Riesz bounds, retained exponential moments, and restriction to the generated difference subspace are preserved.
> - `CHECKED — Robin transfer algebra:` the same original variables `T` and `L`, the definition of `J`, integration by parts, signs, and the Archimedean interval in (31)–(32) are retained without optimization replacement.
> - `CHECKED — outside-window tail:` the unconditional PNT remainder, constants `C,c`, split at `D`, estimate (33), condition `A > 1/(4 c^2)`, and the qualified `o(1)` statement are all kept with their sufficiently-large restriction.
> - `ASSUMED-UNVERIFIED — budget supplier:` the full meanings of `D(n)`, `A_inv(u)`, `B(T)`, decomposition (29), the Euler-layer source, and normalized limit (36) are inherited; the root asymptotic alone is not treated as the full budget identity.
> - `CHECKED — final boundary:` the margin estimate in (37), conditional implications (38)–(39), non-effective `n_0`, small-`n` boundary, unresolved expanding-window core positivity, and the explicit no-RH conclusion remain visible.
>
> **Bounded review limits.** No fresh Lean/kernel compilation, native acquisition validation, hosted GitHub/MathJax certification, or external-paper audit is claimed. The cited primary texts were read for the PNT and Robin context; that reading does not promote inherited premises to proofs.

> **Editorial grounding repair: fixed-source notation and scope map.** This block is editorial and leaves the supplied author body unchanged. The exact pinned pressure source is [ZECKENDORF_EULER_5040.md, Theorem 2.1 and equations (4)–(5)](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/ZECKENDORF_EULER_5040.md#L6787-L6848), together with its [boundary pressure formula (8)–(9)](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/ZECKENDORF_EULER_5040.md#L6933-L6989), [low-price scale and layer count (19)–(24)](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/ZECKENDORF_EULER_5040.md#L7382-L7637), and [pressure integral (26)–(28)](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/ZECKENDORF_EULER_5040.md#L7645-L7789). The separately pinned [EulerLayerRootCorrection.md](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/Blueprint/D5/S3/Arith/Robin/EulerLayerRootCorrection.md#L1-L105) supplies the strict-inventory statement and its scope.
>
> - **Notation bridge.** In the pinned source, `J_lambda(n) = W(n) - lambda E(n)`, `P_0(lambda) = max_{n >= 1} J_lambda(n)`, and the minimal optimizer has `a_p^0(lambda) = #{k >= 1 : eta_(p,k) > lambda}`. At a threshold `eta_(p,k) = lambda`, either choice has the same pressure; the source chooses the minimal-exponent optimizer, so equality layers are excluded from the strict count. The boundary-restricted pressure is `P_5040`, and the source proves `P_5040 = P_0` only in the low-price range `0 < lambda < lambda_c`.
> - **Strict inventory.** Put `lambda(u) = 1/(u log u)`. The exact strict law in the pinned Lean/source supplier is `U.factorization(q) = optimalLayerCount(lambda(u), q)` for every prime `q`; `optimalLayerCount` counts precisely the layers with strict inequality `lambda(u) < goldenLayerMarginal(q,k)`. Thus the manuscript symbol `A_inv(u)` can be read as `log U` for this strict inventory, and it agrees with the source's `E(lambda(u)) = log n_lambda` only after the additional bridge that this `U` is the same minimal low-price optimizer and that the 5040 boundary is inactive. EulerLayerRootCorrection proves, uniformly over such `U`, `(log U - psi(u))/sqrt(u) -> sqrt(2)-1`; it explicitly excludes equality layers and does not prove a signed-tail identity or optimizer attainment beyond the stated strict law.
> - **What the source does and does not name.** The pinned source's pressure gap, whose sign remains unresolved here, is `G(lambda) = H(lambda) - P_5040(lambda)`, with `H(lambda) = max_{E >= log 5184} [h(E) - lambda E]`; equations (26)–(28) express this pressure gap through `E(lambda(v)) - v` and `I_psi(T)`. It does not define the manuscript's `D(n)` or prove that this pressure gap, with its sign conditional rather than established, is an actual same-original-integer residual. Theorem 4.1 states that strict positivity of `G(lambda)` for every positive `lambda` is equivalent to RH; it does not supply an unconditional nonnegative sign. Therefore the assertion `D(n) >= 0` in (29) still requires the specific bridge: define `D` for the same original `n`, prove its sign, and prove that its remainder is exactly the displayed `I_psi(T)` plus the displayed budget term. The pressure gap over an optimized state cannot substitute for that same-`n` identity.
> - **Budget and the numbered implications.** The source's `I_psi(T)` is the integral in (27). The manuscript's `B(T)` additionally requires the bridge `A_inv(u) = E(lambda(u))` (with the strict/equality convention above), the same-integer decomposition (29), and an integrable uniform error allowing the root correction to be inserted under the weighted integral. EulerLayerRootCorrection alone supplies only the strict root asymptotic, so it does not establish (29) or the normalized limit (36). Conditional (38) therefore requires (29), `D(n) >= 0`, (31)–(35), (36), (37), and the stated unconditional PNT tail; conditional (39) additionally requires the posterior estimate (23). The remaining open bridges are exactly the same-`n` decomposition/sign, the `A_inv`–`E(lambda)` identification, and the weighted-error step for (36); no bridge is being claimed here.
> - **Other inherited premises.** The short-window cusp/triangle premise used in (25)–(27) means: fixed `delta`, `r`, and `L_triangle` for the same kernel, all measures supported in `D <= delta`, followed by the displayed triangle-energy identity, fixed-fiber Jensen minimization, and strict matrix gap. Its upstream source path is not supplied in this batch, so (25)–(27) are conditional on that exact premise. The stable greedy premise in Section VIII means the pinned [A370630 permutation](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md), the stated `V_h` asymptotic and cusp estimate, finite preservation of every old `h_i`, and the row-sum/Riesz bounds; only the permutation has an exact upstream path here, so the analytic cusp and asymptotic claims remain conditional and apply only to the generated difference subspace. The reference-weight low-frequency coercivity is scoped to `q_P` on the fixed support interval and does not assert positivity of the full actual kernel. These conditions are the precise inherited scope; an unnamed previous-round label is not used as provenance.

继续。这一轮可以把上一轮“每个有限样本有一个低矩核心”，推进成一个更完整的结构：

> **每个固定区间都有一个固定的有限维变分核心；增加实际读出时，这个核心按精确的 Schur 公式递推，并且全部修正无条件可求和。还可以用实际核导数构造误差矩阵，给极限核心提供可用于证明正性的下界。**

然后，我们可以把这个区间核心直接接回 Robin：

$$
\boxed{
\mathcal S_{A(\log\log n)^2}\succeq0
\quad\Longrightarrow\quad
\sigma(n)<e^\gamma n\log\log n
}
$$

对所有充分大的原整数 $n$ 成立，其中 $A>0$ 是一个固定常数。这个蕴涵可以无条件证明；尚未完成的是左侧实际核心的全局正性。

本轮核对到的项目固定版本为 `18ab178472d8c29eb90d5e5f4e6c8b4c89038e84`，其中新合入的 [AURIC v37](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md) 与这里直接相关：第 6 节用**保留上下文的算子值三轴**表达完整关系，第 9 节给出**可求和误差的收敛条件**。下面将这两项落实到实际算术核上。

<a id="section-i-fixed-kernel-and-complete-energy-space"></a>

## 一、固定实际核与完整能量空间

继续使用

$$
\mathscr K(t)=e^{-|t|/2}\mathcal F(e^{|t|}),
$$

其中

$$
\begin{aligned}
\mathcal F(x)
={}&x(1+\gamma-\log x)-\log(2\pi)\\
&+\sum_{k\ge1}\frac{x^{-2k}}{2k(2k+1)}
+\sum_{p^j\le x}\log p\left(\frac{x}{p^j}-1\right).
\end{aligned}
$$

记

$$
S=\mathscr K(0)=2+\gamma-\log(4\pi)>0.
$$

固定一个任意长度的区间

$$
I=[0,D],\qquad D>0.
$$

这里的 $D$ 可以超过上一轮已经证明全部正定的短窗口。

### 定义 1：实际读出及其原函数

对支撑在 $I$ 内的有限原子复测度

$$
\mu=\sum_i a_i\delta_{t_i},
$$

令其总质量为 $a=\mu(I)$，写成

$$
\boxed{\mu=a\delta_0+F'.}
$$

其中

$$
F(t)=(\mu-a\delta_0)((-\infty,t])
$$

是支撑于 $I$ 的阶梯函数，导数按分布理解。

实际二次型为

$$
Q_{\mathscr K}(\mu)
=
\sum_{i,j}\overline{a_i}a_j\mathscr K(t_i-t_j).
$$

我们此时保留它的真实符号，不预先假设它非负。

### 定义 2：一个已经证明为正的参考能量

令

$$
P(t)=\sum_{k\ge1}c_ke^{-\lambda_k|t|},
\qquad
c_k=\frac1{2k(2k+1)},\quad
\lambda_k=2k+\frac12,
$$

并定义

$$
q_P(F)=Q_P(F').
$$

采用 Fourier 变换后，

$$
q_P(F)
=
\frac1{2\pi}
\int_{\mathbb R}w(\xi)|\widehat F(\xi)|^2\,d\xi,
$$

其中

$$
w(\xi)
=
2\sum_{k\ge1}
c_k\lambda_k\frac{\xi^2}{\lambda_k^2+\xi^2}.
$$

上一轮已证明 $w(\xi)\to+\infty$。这里还需要一个明确的低端控制：

<figure aria-labelledby="equation-number-1" style="margin: 1em 0;">

$$
\boxed{
q_P(F)\ge\alpha_D\|F\|_2^2,
\qquad
\alpha_D=\frac12w\!\left(\frac{\pi}{2D}\right)>0.
}
$$

<figcaption id="equation-number-1" style="text-align: right;">(1)</figcaption>

</figure>

**证明。** 因为 $F$ 支撑于长度为 $D$ 的区间，

$$
|\widehat F(\xi)|\le\sqrt D\,\|F\|_2.
$$

在 $|\xi|\le\pi/(2D)$ 上积分，最多得到总 $L^2$ 质量的一半。另一半位于其外，而 $w$ 随 $|\xi|$ 增加，故式 (1) 成立。□

现在用范数

<figure aria-labelledby="equation-number-2" style="margin: 1em 0;">

$$
\boxed{
\|\mu\|_{\mathcal H_D}^2
=
|a|^2+q_P(F)
}
$$

<figcaption id="equation-number-2" style="text-align: right;">(2)</figcaption>

</figure>

完成这些实际原子读出。Fourier 加权范数的闭性及式 (1)，使这个完成空间仍可表示为 $(a,F)$，其中 $F\in L^2$ 且支撑于 $I$。

### 完整实际二次型仍连续

写

$$
\mathscr K=P+R.
$$

在有界区间内，$R''$ 是有限总变差的符号测度：原点对数尖点已由 $P$ 保存，剩余部分只有光滑项和有限个实际素数幂造成的导数跳跃。

取紧支撑延拓 $R_D$，使其在 $[-D,D]$ 的邻域内等于 $R$，并令

$$
M_D=\|R_D''\|_{\mathrm{TV}}.
$$

则

<figure aria-labelledby="equation-number-3" style="margin: 1em 0;">

$$
\boxed{
\begin{aligned}
Q_{\mathscr K}(\mu)
={}&S|a|^2
+2\Re\left(
-\overline a\int_0^D\mathscr K'(t)F(t)\,dt
\right)\\
&+q_P(F)-\langle R_D''*F,F\rangle .
\end{aligned}
}
$$

<figcaption id="equation-number-3" style="text-align: right;">(3)</figcaption>

</figure>

因为 $\mathscr K'$ 的原点奇性仅为对数型，所以

$$
\mathscr K'\in L^2([-D,D]).
$$

结合式 (1)，式 (3) 在 $\mathcal H_D$ 上定义一个连续厄米型，记为 $B_D$。在有限原子上，它始终等于原来的实际算术关系。

---

<a id="section-ii-fixed-coarse-readout"></a>

## 二、选定一次粗读口，之后始终保留

上一轮的低矩核心随节点配置改变。现在先固定一套粗读口，使所有后续细分都使用同一坐标。

取网格

$$
0=x_0<x_1<\cdots<x_N=D,
$$

令 $\varphi_0,\ldots,\varphi_N$ 为分段仿射帽函数：

$$
\varphi_i(x_j)=\delta_{ij},
\qquad
\sum_i\varphi_i(t)=1.
$$

### 定义 3：固定粗读口与实际截面

定义

<figure aria-labelledby="equation-number-4" style="margin: 1em 0;">

$$
\boxed{
C_i\mu=\int_I\varphi_i(t)\,d\mu(t),
\qquad
C\mu=(C_0\mu,\ldots,C_N\mu).
}
$$

<figcaption id="equation-number-4" style="text-align: right;">(4)</figcaption>

</figure>

它有一个实际原子截面：

<figure aria-labelledby="equation-number-5" style="margin: 1em 0;">

$$
\boxed{
\mathcal Jc=\sum_{i=0}^Nc_i\delta_{x_i},
\qquad
C\mathcal J=I.
}
$$

<figcaption id="equation-number-5" style="text-align: right;">(5)</figcaption>

</figure>

记

$$
Z=\ker C.
$$

对 $\mu=a\delta_0+F'$，直接用帽函数的导数可得

<figure aria-labelledby="equation-number-6" style="margin: 1em 0;">

$$
\boxed{
\mu\in Z
\iff
a=0,\quad
\int_{x_{j-1}}^{x_j}F(t)\,dt=0
\ \text{对所有 }j.
}
$$

<figcaption id="equation-number-6" style="text-align: right;">(6)</figcaption>

</figure>

所以 $Z$ 保存的是：**不改变任何已固定粗读口的全部细节变化。**

### 引理：网格足够细时，全部这些细方向强正

可以选取一个有限网格，使

<figure aria-labelledby="equation-number-7" style="margin: 1em 0;">

$$
\boxed{
B_D(z,z)\ge\frac12q_P(F_z)
\qquad(z\in Z).
}
$$

<figcaption id="equation-number-7" style="text-align: right;">(7)</figcaption>

</figure>

**证明。** 先取 $R_0$，使

$$
w(\xi)\ge4(M_D+1)
\qquad(|\xi|\ge R_0).
$$

设最大网格长度为 $h$。由于每格 $\int F=0$，可以在 Fourier 积分中减去该格中点的指数值，得到

$$
|\widehat F(\xi)|
\le
\frac{|\xi|h}{2}\sqrt D\,\|F\|_2.
$$

因而

$$
\frac1{2\pi}\int_{-R_0}^{R_0}
|\widehat F(\xi)|^2\,d\xi
\le
\frac{Dh^2R_0^3}{12\pi}\|F\|_2^2.
$$

选有限网格使右侧系数不超过 $1/2$。于是

$$
q_P(F)\ge2(M_D+1)\|F\|_2^2.
$$

再由

$$
|\langle R_D''*F,F\rangle|
\le M_D\|F\|_2^2,
$$

得到式 (7)。□

**关键点是：即使整体符号仍未知，在固定粗读出的条件下，可调整的全部细方向已经具有统一严格正性。**

---

<a id="section-iii-fixed-finite-dimensional-core"></a>

## 三、定理：一个固定窗口对应一个固定有限维核心

### 定义 4：固定变分核心

给定粗读出 $c\in\mathbb C^{N+1}$，考虑

$$
\min_{C\mu=c}Q_{\mathscr K}(\mu).
$$

每个满足约束的读出都可写成

$$
\mu=\mathcal Jc+z,\qquad z\in Z.
$$

由式 (7)，这个问题在 $z$ 方向严格凸。Riesz 表示定理给出唯一最小点，记为 $v_c$。它满足

$$
Cv_c=c,
\qquad
B_D(z,v_c)=0\quad(z\in Z).
$$

定义固定矩阵

<figure aria-labelledby="equation-number-8" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_D(i,j)=B_D(v_{e_i},v_{e_j}).
}
$$

<figcaption id="equation-number-8" style="text-align: right;">(8)</figcaption>

</figure>

### 定理 1：固定核心的精确分解

对任意 $\mu\in\mathcal H_D$，令 $c=C\mu$，则存在唯一 $z\in Z$，使

$$
\mu=v_c+z
$$

并且

<figure aria-labelledby="equation-number-9" style="margin: 1em 0;">

$$
\boxed{
Q_{\mathscr K}(\mu)
=
c^*\mathcal S_Dc+B_D(z,z).
}
$$

<figcaption id="equation-number-9" style="text-align: right;">(9)</figcaption>

</figure>

因此

<figure aria-labelledby="equation-number-10" style="margin: 1em 0;">

$$
\boxed{
c^*\mathcal S_Dc
=
\min_{C\mu=c}Q_{\mathscr K}(\mu).
}
$$

<figcaption id="equation-number-10" style="text-align: right;">(10)</figcaption>

</figure>

进一步，

<figure aria-labelledby="equation-number-11" style="margin: 1em 0;">

$$
\boxed{
\mathscr K\text{ 在 }[0,D]\text{ 内全部有限关系矩阵非负}
\iff
\mathcal S_D\succeq0.
}
$$

<figcaption id="equation-number-11" style="text-align: right;">(11)</figcaption>

</figure>

### 证明

因为 $C\mu=Cv_c$，差值 $z=\mu-v_c$ 属于 $Z$。由最小点的正交条件，展开二次型时交叉项消失，得到式 (9)。式 (7) 随即给出唯一极小性。

若 $\mathcal S_D\succeq0$，式 (9) 保证全部实际原子二次型非负。

反之，有限原子在 $\mathcal H_D$ 中稠密，且 $B_D$ 连续。因此，如果全部实际原子二次型非负，则整个完成空间都非负，尤其

$$
c^*\mathcal S_Dc=Q_{\mathscr K}(v_c)\ge0.
$$

证毕。

这里取得了**一个固定窗口、一个固定粗坐标系、一个固定核心**。

同时需要准确说明：核心维数有限，但它的条目目前由无限维极小化确定。接下来要证明有限取样怎样逼近它，并给出可信的下界。

---

<a id="section-iv-schur-recursion"></a>

## 四、递归公式闭合：每次新增读出怎样改变核心？

取嵌套有限取样集

$$
E_0\subset E_1\subset E_2\subset\cdots,
$$

其中 $E_0$ 为初始网格，后续节点并集在 $[0,D]$ 中稠密。

在支撑于 $E_k$ 的原子中，固定粗读出 $c$ 并最小化，得到 $v_{k,c}$，相应有限核心记为 $\mathcal S_k$。

初始阶段没有额外细方向，所以

<figure aria-labelledby="equation-number-12" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_0=
[\mathscr K(x_i-x_j)]_{i,j=0}^{N}.
}
$$

<figcaption id="equation-number-12" style="text-align: right;">(12)</figcaption>

</figure>

这是实际网格关系矩阵。

### 新节点的实际细方向

若新点 $t$ 位于一个固定网格单元 $[a,b]$ 内，则

$$
\mathcal JC\delta_t
=
\frac{b-t}{b-a}\delta_a+
\frac{t-a}{b-a}\delta_b.
$$

所以

<figure aria-labelledby="equation-number-13" style="margin: 1em 0;">

$$
\boxed{
z_t=
\delta_t
-\frac{b-t}{b-a}\delta_a
-\frac{t-a}{b-a}\delta_b
\in Z.
}
$$

<figcaption id="equation-number-13" style="text-align: right;">(13)</figcaption>

</figure>

将它对已有细空间作 $B_D$-正交化，得到剩余方向 $u_k$。真正新增的节点保证 $u_k\ne0$，于是

$$
e_k=B_D(u_k,u_k)>0.
$$

令耦合列为

$$
b_{k,i}=B_D(v_{k,e_i},u_k).
$$

### 定理 2：核心的精确 Schur 递推

<figure aria-labelledby="equation-number-14" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_{k+1}
=
\mathcal S_k-\frac{b_kb_k^*}{e_k}.
}
$$

<figcaption id="equation-number-14" style="text-align: right;">(14)</figcaption>

</figure>

**证明。** 新的最小化读出为

$$
v_{k+1,c}
=
v_{k,c}
-u_k\frac{b_k^*c}{e_k}.
$$

代回二次型：

$$
Q_{\mathscr K}(v_{k+1,c})
=
Q_{\mathscr K}(v_{k,c})
-\frac{|b_k^*c|^2}{e_k}.
$$

这正是式 (14)。□

这里的方向非常重要：

> **新增一个已经证明为正的细方向，会从剩余粗核心中减去一个正半定修正。**

所以需要控制的是这部分累计修正是否超过初始粗关系所能承受的范围。

---

<a id="section-v-summable-corrections"></a>

## 五、定理：固定窗口内，全部递归修正无条件可求和

### 定理 3

如果取样并集稠密，则

<figure aria-labelledby="equation-number-15" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_k\downarrow\mathcal S_D
}
$$

<figcaption id="equation-number-15" style="text-align: right;">(15)</figcaption>

</figure>

并在算子范数中收敛。更精确地，

<figure aria-labelledby="equation-number-16" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_k-\mathcal S_D
=
\sum_{j\ge k}\frac{b_jb_j^*}{e_j}
\succeq0,
}
$$

<figcaption id="equation-number-16" style="text-align: right;">(16)</figcaption>

</figure>

且

<figure aria-labelledby="equation-number-17" style="margin: 1em 0;">

$$
\boxed{
\sum_{j\ge0}\frac{\|b_j\|^2}{e_j}
=
\operatorname{tr}(\mathcal S_0-\mathcal S_D)
<\infty.
}
$$

<figcaption id="equation-number-17" style="text-align: right;">(17)</figcaption>

</figure>

### 证明

首先，移动原子在参考能量中连续：

$$
\|\delta_t-\delta_s\|_{\mathcal H_D}^2
=
2(P(0)-P(t-s))
\longrightarrow0
\qquad(t\to s).
$$

因此稠密节点产生的原子空间在 $\mathcal H_D$ 中稠密。

还可以把近似修正到同一粗读出纤维中：若 $\mu_k\to\mu$，则

$$
\mu_k+\mathcal J(C\mu-C\mu_k)
$$

具有与 $\mu$ 完全相同的粗读出，且仍趋于 $\mu$。

于是有限细空间的正交投影趋于完整细空间的正交投影，得到 $v_{k,c}\to v_c$。由于粗坐标维数固定，

$$
\mathcal S_k\to\mathcal S_D
$$

在算子范数中成立。

再将式 (14) 从 $k$ 累加到有限阶段并取极限，即得式 (16)。对正半定项取迹，得到式 (17)。□

这已经严格证明了你一直要求的一个部分：

**在每个固定区间内，递归修正本身不会发散，并且有精确的总量分解**

<figure aria-labelledby="equation-number-18" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_0
=
\mathcal S_D+
\sum_{j\ge0}\frac{b_jb_j^*}{e_j}.
}
$$

<figcaption id="equation-number-18" style="text-align: right;">(18)</figcaption>

</figure>

接下来仍需证明的是

$$
\sum_{j\ge0}\frac{b_jb_j^*}{e_j}
\preceq\mathcal S_0,
$$

也就是极限核心非负。收敛性与这个大小比较，是两个分别需要证明的结论。

---

<a id="section-vi-residual-lower-bound"></a>

## 六、怎样给极限核心一个真正的下界？

仅有 $\mathcal S_k\downarrow\mathcal S_D$，说明有限阶段给的是上界。要证明极限非负，需要控制尚未消去的全部细方向。

### 定义 5：全细空间残差

在 $Z$ 上采用 $q_P$ 的参考内积，写

$$
B_D(z,w)=\langle z,A_Zw\rangle_P.
$$

式 (7) 给出

$$
A_Z\succeq\frac12I.
$$

定义残差算子 $R_k$：

<figure aria-labelledby="equation-number-19" style="margin: 1em 0;">

$$
\boxed{
\langle z,R_kc\rangle_P
=
B_D(z,v_{k,c}),
\qquad z\in Z.
}
$$

<figcaption id="equation-number-19" style="text-align: right;">(19)</figcaption>

</figure>

它检验的是当前有限最小化读出对**整个**细空间的剩余耦合。

### 定理 4：精确后验误差公式

<figure aria-labelledby="equation-number-20" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_k-\mathcal S_D
=
R_k^*A_Z^{-1}R_k
\preceq2R_k^*R_k.
}
$$

<figcaption id="equation-number-20" style="text-align: right;">(20)</figcaption>

</figure>

### 证明

令

$$
w_{k,c}=v_{k,c}-v_c\in Z.
$$

由于 $v_c$ 与整个 $Z$ 正交，

$$
B_D(z,w_{k,c})
=
B_D(z,v_{k,c})
=
\langle z,R_kc\rangle_P.
$$

故

$$
A_Zw_{k,c}=R_kc.
$$

另一方面，最小点的正交分解给出

$$
c^*(\mathcal S_k-\mathcal S_D)c
=
B_D(w_{k,c},w_{k,c})
=
\langle R_kc,A_Z^{-1}R_kc\rangle_P.
$$

再用 $A_Z^{-1}\preceq2I$。□

因此，一旦证明

$$
\|R_k\|_{\mathrm{op}}\le\eta,
$$

就得到

<figure aria-labelledby="equation-number-21" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_D\succeq\mathcal S_k-2\eta^2I.
}
$$

<figcaption id="equation-number-21" style="text-align: right;">(21)</figcaption>

</figure>

这已经是一个能证明全窗口正性的验收条件。

### 用实际 $\mathscr K'$ 写出有限积分误差矩阵

当前每个最小化列都是有限原子：

$$
\nu_{k,i}=v_{k,e_i}
=\sum_s d_{i,s}\delta_s.
$$

定义实际函数

$$
f_{k,i}(t)
=
-\sum_s d_{i,s}\mathscr K'(t-s),
\qquad 0\le t\le D.
$$

令 $\Pi_{\mathrm{cell}}$ 表示逐固定网格单元取平均的 $L^2$ 投影，并定义

<figure aria-labelledby="equation-number-22" style="margin: 1em 0;">

$$
\boxed{
\mathcal E_k(i,j)
=
\int_0^D
\overline{(I-\Pi_{\mathrm{cell}})f_{k,i}(t)}
\,(I-\Pi_{\mathrm{cell}})f_{k,j}(t)\,dt.
}
$$

<figcaption id="equation-number-22" style="text-align: right;">(22)</figcaption>

</figure>

这个矩阵由实际核导数的有限线性组合构成，且 $\mathcal E_k\succeq0$。

对 $z=F'\in Z$，每格 $\int F=0$，所以

$$
B_D(z,\nu_{k,i})
=
\int_0^D\overline{F(t)}
(I-\Pi_{\mathrm{cell}})f_{k,i}(t)\,dt.
$$

结合式 (1)，得到

$$
R_k^*R_k\preceq\alpha_D^{-1}\mathcal E_k.
$$

于是

<figure aria-labelledby="equation-number-23" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_D
\succeq
\mathcal S_k-\frac2{\alpha_D}\mathcal E_k.
}
$$

<figcaption id="equation-number-23" style="text-align: right;">(23)</figcaption>

</figure>

最终的充分条件是

<figure aria-labelledby="equation-number-24" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_k-\frac2{\alpha_D}\mathcal E_k\succeq0
\quad\Longrightarrow\quad
\mathscr K\text{ 在整个 }[0,D]\text{ 上正半定}.
}
$$

<figcaption id="equation-number-24" style="text-align: right;">(24)</figcaption>

</figure>

这里 $\mathcal E_k$ 是一个明确的一维积分矩阵，可以继续用解析不等式估计。它提供一个可靠上界；本轮没有证明这个较保守的积分上界会自动随所有细分方案趋于零。

在 AURIC 的语言中，$\mathcal S_k$ 与误差矩阵应作为保留上下文的算子保存，再逐块使用 v37 的可逆三轴表达。完整重组矩阵的符号由式 (23)—(24) 控制。

---

<a id="section-vii-small-window-core"></a>

## 七、小窗口中，完成无限递归后的核心也严格为正

上一轮已构造出 $\delta>0$、$r>0$、$L_\triangle>\delta$，使短窗口中的实际二次型满足

$$
Q_{\mathscr K}(\mu)\ge rQ_\triangle(\mu),
$$

其中

$$
Q_\triangle(\mu)
=
\iint(L_\triangle-|t-s|)_+
\,d\overline\mu(t)\,d\mu(s).
$$

若 $D\le\delta$，则对 $\mu=a\delta_0+F'$，

<figure aria-labelledby="equation-number-25" style="margin: 1em 0;">

$$
\boxed{
Q_\triangle(\mu)
=
\left(L_\triangle-\frac D2\right)|a|^2
+
2\left\|F+\frac a2\right\|_2^2.
}
$$

<figcaption id="equation-number-25" style="text-align: right;">(25)</figcaption>

</figure>

固定粗读出后，$a$ 与每格的 $\int F$ 都固定。Jensen 不等式说明：该能量在每格 $F$ 为常数时取得最小值，而这恰好对应实际网格截面 $\mathcal Jc$。

因此

<figure aria-labelledby="equation-number-26" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_D
\succeq
r\bigl[(L_\triangle-|x_i-x_j|)_+\bigr]
\succ0
\qquad(D\le\delta).
}
$$

<figcaption id="equation-number-26" style="text-align: right;">(26)</figcaption>

</figure>

若最小网格间距为 $h_{\min}$，还得到

<figure aria-labelledby="equation-number-27" style="margin: 1em 0;">

$$
\boxed{
\lambda_{\min}(\mathcal S_D)
\ge
\frac r4\min\{h_{\min},L_\triangle-D\}>0.
}
$$

<figcaption id="equation-number-27" style="text-align: right;">(27)</figcaption>

</figure>

所以这里已经控制了**完成全部无限细化之后的极限核心**，并非只证明某个有限阶段为正。

---

<a id="section-viii-stable-greedy-expansion"></a>

## 八、你的贪心序列可以实现保持旧读出的无限稳定递归

这一点也能比上一轮再加强。

设 $a_1,a_2,\ldots$ 是项目已证明遍历所有正整数的 [A370630 贪心排列](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)，取

$$
t_j=\log a_j.
$$

仍使用三点指数读出

$$
\omega_{t,h}
=
\delta_{t-h}-2\cosh(h/2)\delta_t+\delta_{t+h},
$$

其实际总量为

$$
V_h=Q_{\mathscr K}(\omega_{t,h})
\sim2h\log(1/h)>0.
$$

### 定理 5：保持全部旧读出的无限稳定扩张

可以依次选取 $h_j>0$，以后不改变任何旧 $h_i$，使归一读出

$$
e_j=\frac{\omega_{t_j,h_j}}{\sqrt{V_{h_j}}}
$$

满足

$$
|B(e_i,e_j)|\le2^{-i-j-4}
\qquad(i\ne j).
$$

因此，对任意有限复系数列 $z$，

<figure aria-labelledby="equation-number-28" style="margin: 1em 0;">

$$
\boxed{
\frac{31}{32}\sum_i|z_i|^2
\le
Q_{\mathscr K}\!\left(\sum_i z_ie_i\right)
\le
\frac{33}{32}\sum_i|z_i|^2.
}
$$

<figcaption id="equation-number-28" style="text-align: right;">(28)</figcaption>

</figure>

### 证明

固定一个旧读出，考虑新尺度 $h\to0$。其与新读出的关系是有限个

$$
\Delta_h\mathscr K(d)
$$

的固定线性组合。

在 $d\ne0$ 处，局部 Lipschitz 性给出 $O(h)$；在 $d=0$ 处，原点尖点给出 $O(h\log(1/h))$。因此统一有

$$
B(\omega_i,\omega_{t,h})
=
O(h\log(1/h)).
$$

除以 $\sqrt{V_{h_i}V_h}$，得到归一关系趋于零。每一步只有有限个旧读出，所以可以选足够小的 $h_j$，同时满足全部所需界，且保持旧尺度不变。

最后，每一行的非对角绝对值之和不超过 $1/32$，直接估计二次型即可得到式 (28)。□

由此，每一步新增读出的归一 Schur 剩余至少为

$$
\boxed{Z_j\ge\frac{31}{32}.}
$$

因此，“贪心遍历所有整数、保持旧记录、持续加入稳定的实际差分读出”已经可以严格实现。

它控制的是所构造的差分子空间；原始点读出的完整关系仍须由前面的核心处理。每个差分读出同时满足

$$
\int e^{u/2}\,d\omega_{t,h}(u)=
\int e^{-u/2}\,d\omega_{t,h}(u)=0,
$$

这些约束以及原始总量 $V_{h_j}$ 都必须随递归保留。

---

<a id="section-ix-robin-transfer"></a>

## 九、把固定区间核心直接接回原整数 Robin 判据

现在给这个固定核心一个实际算术用途。

令

$$
T=\log n,\qquad L=\log T,
$$

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n}.
$$

沿用精确分解

<figure aria-labelledby="equation-number-29" style="margin: 1em 0;">

$$
-\log R(n)
=
\mathcal D(n)+I_\psi(T)+\mathcal B(T),
\qquad
\mathcal D(n)\ge0,
$$

<figcaption id="equation-number-29" style="text-align: right;">(29)</figcaption>

</figure>

其中

$$
I_\psi(T)
=
\int_T^\infty
\frac{\log u+1}{u^2\log^2u}
(\psi(u)-u)\,du.
$$

定义归一尾

$$
Q(T)=\sqrt T\log T\,I_\psi(T).
$$

### 定义 6：另一个实际素数尾

令

$$
J(T)=\int_T^\infty\frac{\psi(u)-u}{u^2}\,du,
$$

以及

$$
A_0(T)=\sum_{k\ge1}\frac{T^{-2k}}{2k(2k+1)}.
$$

从实际有限素数公式可直接整理出

<figure aria-labelledby="equation-number-30" style="margin: 1em 0;">

$$
\boxed{
J(T)
=
-\frac{\mathscr K(L)}{\sqrt T}
+\frac{A_0(T)-\log(2\pi)}T.
}
$$

<figcaption id="equation-number-30" style="text-align: right;">(30)</figcaption>

</figure>

### 定理 6：核到 Robin 尾的精确传输

<figure aria-labelledby="equation-number-31" style="margin: 1em 0;">

$$
\boxed{
\begin{aligned}
Q(T)
={}&-\left(1+\frac1L\right)\mathscr K(L)\\
&+
L\int_0^\infty e^{-v/2}
\frac{L+v+2}{(L+v)^3}
\mathscr K(L+v)\,dv\\
&+E_{\mathrm{arch}}(T),
\end{aligned}
}
$$

<figcaption id="equation-number-31" style="text-align: right;">(31)</figcaption>

</figure>

其中，对 $T\ge2$，

<figure aria-labelledby="equation-number-32" style="margin: 1em 0;">

$$
\boxed{
-\frac{\log(2\pi)}{\sqrt T}
\le E_{\mathrm{arch}}(T)<0.
}
$$

<figcaption id="equation-number-32" style="text-align: right;">(32)</figcaption>

</figure>

### 证明

令

$$
a(u)=\frac1{\log u}+\frac1{\log^2u}.
$$

因为 $J'(u)=-(\psi(u)-u)/u^2$，分部积分得

$$
I_\psi(T)
=
a(T)J(T)
-
\int_T^\infty
\frac{\log u+2}{u\log^3u}J(u)\,du.
$$

代入式 (30)，再作 $u=Te^v$ 的变量替换，即得式 (31)。

阿基米德项可精确写为

$$
\begin{aligned}
E_{\mathrm{arch}}(T)
={}&-\frac{\log(2\pi)}{\sqrt T}\\
&+\sqrt T L
\int_T^\infty
\frac{\log u+1}{u^2\log^2u}
\left[-\frac12\log(1-u^{-2})\right]du.
\end{aligned}
$$

利用括号内函数正且递减，以及

$$
\int_T^\infty
\frac{\log u+1}{u^2\log^2u}\,du
=\frac1{T\log T},
$$

得到式 (32)。□

---

<a id="section-x-pnt-tail"></a>

## 十、无条件控制区间之外的尾：只需要有限窗口正性

取 $D\ge L$，将式 (31) 在 $v=D-L$ 处分开。

经典无条件素数定理余项给出某些 $C,c>0$，使充分大的 $u$ 满足

$$
|\psi(u)-u|
\le Cu\,e^{-c\sqrt{\log u}}.
$$

这里使用的是无条件 PNT 余项，不假设 RH。[kskedlaya.org](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com)

由此

$$
\sup_{u\ge e^D}|J(u)|
\le
\frac{2C}{c^2}(1+c\sqrt D)e^{-c\sqrt D}.
$$

式 (31) 中区间外的积分绝对值不超过

<figure aria-labelledby="equation-number-33" style="margin: 1em 0;">

$$
\boxed{
\begin{aligned}
\mathfrak r(T,D)
={}&L\sqrt T\left(\frac1D+\frac1{D^2}\right)\\
&\times
\left[
\frac{2C}{c^2}(1+c\sqrt D)e^{-c\sqrt D}
+\log(2\pi)e^{-D}
\right].
\end{aligned}
}
$$

<figcaption id="equation-number-33" style="text-align: right;">(33)</figcaption>

</figure>

现在取一个固定常数

$$
A>\frac1{4c^2},
\qquad
D=A L^2.
$$

那么

<figure aria-labelledby="equation-number-34" style="margin: 1em 0;">

$$
\boxed{
\mathfrak r(T,A(\log T)^2)=o(1).
}
$$

<figcaption id="equation-number-34" style="text-align: right;">(34)</figcaption>

</figure>

因为其中的主要指数因子为

$$
\sqrt T\,e^{-c\sqrt D}
=
T^{1/2-c\sqrt A},
$$

而指数严格为负。

### 有限窗口核心的实际消费者

如果

$$
\mathcal S_D\succeq0,
$$

由定理 1，该区间内全部实际关系矩阵非负。特别是对节点 $0,s$，

$$
\begin{pmatrix}
S&\mathscr K(s)\\
\mathscr K(s)&S
\end{pmatrix}\succeq0,
$$

所以

$$
|\mathscr K(s)|\le S
\qquad(0\le s\le D).
$$

将它用于式 (31) 的有限区间部分，并使用

$$
L\int_0^\infty e^{-v/2}
\frac{L+v+2}{(L+v)^3}\,dv
\le\frac2L+\frac4{L^2},
$$

得到

<figure aria-labelledby="equation-number-35" style="margin: 1em 0;">

$$
\boxed{
Q(T)\ge
-S\left(1+\frac3L+\frac4{L^2}\right)
-\frac{\log(2\pi)}{\sqrt T}
-\mathfrak r(T,D).
}
$$

<figcaption id="equation-number-35" style="text-align: right;">(35)</figcaption>

</figure>

这是有限区间正性对原整数 Robin 尾的定量控制。

---

<a id="section-xi-budget-margin"></a>

## 十一、正预算最终足以覆盖这个界

项目的[严格 Euler 层根尺度修正](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/Blueprint/D5/S3/Arith/Robin/EulerLayerRootCorrection.md)给出无条件的完整层修正：

$$
A_{\mathrm{inv}}(u)-\psi(u)
\sim(\sqrt2-1)\sqrt u.
$$

结合已经建立的实际预算积分

$$
\mathcal B(T)
=
\int_T^\infty
\frac{\log u+1}{u^2\log^2u}
\bigl(A_{\mathrm{inv}}(u)-\psi(u)\bigr)\,du,
$$

得到

<figure aria-labelledby="equation-number-36" style="margin: 1em 0;">

$$
\boxed{
\sqrt T\log T\,\mathcal B(T)
\longrightarrow2(\sqrt2-1).
}
$$

<figcaption id="equation-number-36" style="text-align: right;">(36)</figcaption>

</figure>

而

<figure aria-labelledby="equation-number-37" style="margin: 1em 0;">

$$
\boxed{
2(\sqrt2-1)-S
=
2\sqrt2-4-\gamma+\log(4\pi)>0.
}
$$

<figcaption id="equation-number-37" style="text-align: right;">(37)</figcaption>

</figure>

这个正号可以用粗界直接证明：

$$
\gamma<\frac34,\qquad
\sqrt2>\frac75,\qquad
\log(4\pi)>2
$$

给出式 (37) 的左端严格大于 $1/20$。

这个常数正是经典 Ramanujan 条件界中出现的常数；这里的用途是校准预算，而不是把经典条件结论当作 RH 的证明。[arxiv.org](https://arxiv.org/pdf/1211.6944?utm_source=chatgpt.com)

将式 (35)—(37) 与原整数分解 (29) 合并，得到：

### 定理 7：固定窗口核心到原整数 Robin 的蕴涵

存在固定常数 $A>0$ 和 $n_0$，使对每个原整数 $n\ge n_0$，

<figure aria-labelledby="equation-number-38" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_{A(\log\log n)^2}\succeq0
\quad\Longrightarrow\quad
R(n)<1.
}
$$

<figcaption id="equation-number-38" style="text-align: right;">(38)</figcaption>

</figure>

### 证明

令 $T=\log n$、$L=\log T$、$D=AL^2$。由式 (29)，

$$
\sqrt T L[-\log R(n)]
=
\sqrt T L\,\mathcal D(n)
+Q(T)+\sqrt T L\,\mathcal B(T).
$$

第一项非负。若窗口核心非负，则式 (35) 给出第二项下界。由式 (34)、(36)，整个右端的下极限至少为

$$
2(\sqrt2-1)-S>0.
$$

故对充分大的原整数严格为正，即 $R(n)<1$。□

注意，这个证明只在对应的有限窗口内使用核正性，窗口之外的误差由无条件 PNT 控制。

再接上后验下界 (23)，得到一个完整的证明入口：

<figure aria-labelledby="equation-number-39" style="margin: 1em 0;">

$$
\boxed{
\mathcal S_k-\frac2{\alpha_D}\mathcal E_k\succeq0,
\qquad
D=A(\log\log n)^2
\quad\Longrightarrow\quad
R(n)<1
}
$$

<figcaption id="equation-number-39" style="text-align: right;">(39)</figcaption>

</figure>

对充分大的 $n$ 成立。

其中 $\mathcal S_k$ 来自有限实际取样，$\mathcal E_k$ 来自实际 $\mathscr K'$ 的有限积分矩阵，原整数及全部素数层保持不变。

---

<a id="section-xii-what-closes"></a>

## 十二、本轮真正闭合了什么，剩下哪一项？

现在已经证明：

$$
\boxed{
\begin{gathered}
\text{固定区间有一个固定有限维变分核心；}\\
\mathcal S_{k+1}
=
\mathcal S_k-\frac{b_kb_k^*}{e_k},
\qquad e_k>0;\\
\sum_k\frac{\|b_k\|^2}{e_k}<\infty;\\
\mathcal S_D
\succeq
\mathcal S_k-\frac2{\alpha_D}\mathcal E_k;\\
\mathcal S_{A(\log\log n)^2}\succeq0
\Longrightarrow
\text{原整数 }n\text{ 满足 Robin}.
\end{gathered}
}
$$

你提出的“递归误差应当稳定、并与结果保持关系”的要求，现在有了精确实现：修正项有真实来源、确定符号、可求和总量和后验尾界。贪心遍历对应的差分读出，也可以在保持旧记录的同时无限稳定扩张。

**剩余的全局任务已经落实为一个大小比较：对不断扩大的实际区间，证明累计 Schur 消耗没有超过粗关系所保留的正余量。** 可以直接证明 $\mathcal S_D\succeq0$，也可以通过式 (23) 的有限阶段下界证明它。

本轮尚未取得这个全局符号结论，因此还不能宣称证明 RH；但“递归是否收敛”和“如何给极限提供可靠下界”这两项，已经从直觉变成了完整的定理。