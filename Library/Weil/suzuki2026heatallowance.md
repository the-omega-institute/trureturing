---
bibkey: suzuki2026heatallowance
authors: trureturing research continuation
year: 2026
title: Quadratic heat loss and the four-fifths height allowance
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/f108f1335eb9ed0a02569f5a0ef9f363d84a368e/Library/Weil/suzuki2026heatallowance.md
claim: Internal research continuation deriving the four-fifths logarithmic heat allowance under the stated verified-height hypothesis.
strata_touched: []
license: repository-original
triage: anchor
---

# Quadratic heat loss and the four-fifths height allowance

This continuation uses the definitions and normalizations in [the screw-kernel source](suzuki2026screw.md), specifically W257 and W338--W371. The class $\mathcal V$, the complete energy $\mathfrak E$, the sixth-moment budget $M$, the actual source profile $g_F$, its logarithmic Fourier budget $\mathcal L$, and the minima $e_K$ retain exactly those definitions. The premise $\mathsf{RH}(T)$ states that every actual zeta zero through height $T$ is on the critical line; no condition is imposed on the remaining zeros.

The unitary Fourier transform uses angular frequency $\tau$, and $K_\epsilon(x)=(4\pi\epsilon)^{-1/2}\exp(-x^2/(4\epsilon))$. Thus its multiplier is $\exp(-\epsilon\tau^2)$. All real and complex signed source coefficients and all prime powers remain admitted. The estimates below strengthen the height allowance without changing that source class.

### Retain the quadratic heat loss in the full height allowance

The heat filter in W365--W371 gives a stronger allowance when its exact quadratic loss is used before estimating the complete prime-power sum. There is an absolute finite constant $C$, independent of the verified height, scalar field, source count, widths, support and coefficients, such that
$$
\mathsf{RH}(T)\quad\Longrightarrow\quad
\mathfrak E(F)\ge-\frac{C}{(\log T)^{4/5}}M(F)
\qquad(T\ge3,\ F\in\mathcal V).
\tag{W372}
$$
The same original minima and sources as W371 consequently satisfy
$$
\begin{gathered}
e_K\ge-\frac{CK}{(\log T)^{4/5}}\quad(K>1),\qquad
-\frac{4C}{(\log T)^{4/5}}\le e_4\le0,\\
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
\ge-\frac{C}{(\log T)^{4/5}}Q_{6,A}(\sigma).
\end{gathered}
\tag{W373}
$$
This is a paper-level refinement on the full original real and complex signed class. The constant is not numerically evaluated.

Keep W366's actual profile g=g_F, its weight b=5/2 and its logarithmic Fourier budget. It suffices first to consider $\mathfrak E(F)\le0$, where
$\|g\|_b^2+\mathcal L(g)\le CM(F)$. For $0<\epsilon\le1$, let $h_\epsilon=K_\epsilon*g$ be the SAME normalized heat filter and put
$$
L_\epsilon=\log(2+\epsilon^{-1}),\qquad
m_\epsilon=\int_{\mathbb R}
(1-e^{-2\epsilon\tau^2})|\widehat g(\tau)|^2d\tau
=\|g\|_0^2-\|h_\epsilon\|_0^2\ge0.
$$
Splitting at $|\tau|=\epsilon^{-1/4}$ gives
$$
m_\epsilon\le2\sqrt\epsilon\,\|g\|_0^2+
\frac{\mathcal L(g)}{\log(2+\epsilon^{-1/4})}
\le\frac{CM(F)}{L_\epsilon}.
$$
Indeed $1-e^{-x}\le x$, the logarithmic denominator is at least $L_\epsilon/4$, and $\sqrt\epsilon L_\epsilon$ is bounded on $(0,1]$. The weighted heat bound from W367 gives $\|h_\epsilon\|_b\le2e^{b^2\epsilon}\|g\|_b$, with a constant uniform in this interval.

For the complex correlation $\mathcal C_g(s)=\int g(r)\overline{g(r-s)}dr$, unitary Plancherel gives the exact difference
$$
\mathcal C_g(s)-\mathcal C_{h_\epsilon}(s)
=\int e^{i\tau s}(1-e^{-2\epsilon\tau^2})
|\widehat g(\tau)|^2d\tau.
$$
It has absolute value at most $m_\epsilon$. Weighted Cauchy--Schwarz also bounds this SAME difference by $CM(F)e^{-b|s|}$. Taking real parts yields, for W338's actual autocorrelation,
$$
|R_g(s)-R_{h_\epsilon}(s)|
\le CM(F)\min\{L_\epsilon^{-1},e^{-5|s|/2}\}.
$$
Both bounds hold simultaneously for every shift on the same profile and filter.

Reuse the classical Chebyshev bound $\psi(x)=\sum_{n\le x}\Lambda(n)\le C_\psi x$, already used for the complete source estimates. Abel summation pays the two coefficients needed here, for every real $N\ge2$:
$$
\sum_{2\le n\le N}\frac{\Lambda(n)}{\sqrt n}
\le2C_\psi\sqrt N,\qquad
\sum_{n>N}\frac{\Lambda(n)}{n^3}
\le\frac{3C_\psi}{2N^2}.
$$
The first estimate follows from
$\psi(N)N^{-1/2}+\frac12\int_1^N\psi(x)x^{-3/2}dx$.
For the second, use
$-\psi(N)N^{-3}+3\int_N^\infty\psi(x)x^{-4}dx$.
In the normalization of W359, the complete prime term is
$T_1(g)+T_{\ge2}(g)=2\sum_{n\ge2}\Lambda(n)n^{-1/2}R_g(\log n)$.
Therefore, with $N=\max\{2,L_\epsilon^{2/5}\}$, its ENTIRE change is bounded by
$$
\begin{aligned}
|\Delta(T_1+T_{\ge2})|
&\le CM(F)\left(L_\epsilon^{-1}\sqrt N+N^{-2}\right)\\
&\le\frac{CM(F)}{L_\epsilon^{4/5}}.
\end{aligned}
$$
Here $n^{-1/2}n^{-5/2}=n^{-3}$, and $N^{5/2}=L_\epsilon$ balances the two terms when the maximum selects its second entry. The bounded remaining range of $L_\epsilon$ is absorbed into the same universal constant. Every prime power is retained, with no correlation-sign assumption.

For the signed Gamma part, keep W368's actual multiplier q and its lower bound $q\ge q_0$. Its difference is at least
$q_0m_\epsilon\ge-|q_0|m_\epsilon$, hence costs only $CM(F)/L_\epsilon$. The nonnegative shifted Gamma contribution is preserved in this one-sided comparison. For the full pole term, W369's identity
$v_\epsilon(z)=e^{-\epsilon z^2}v(z)$, evaluated at $z=\pm i/2$, gives exactly
$\ell_1(h_\epsilon)=e^{\epsilon/4}\ell_1(g)$, where $\ell_1(g)=\int\cosh(r/2)g(r)dr$.
The weight b=5/2 justifies these boundary evaluations and bounds $|\ell_1(g)|^2\le CM(F)$. Thus the change of the coefficient-2 pole square is
$2(1-e^{\epsilon/2})|\ell_1(g)|^2\ge-C\epsilon M(F)$.
These estimates prove
$$
\mathcal Q_W(g)\ge\mathcal Q_W(h_\epsilon)
-\frac{CM(F)}{L_\epsilon^{4/5}}.
$$
No separate absolute Gamma-tail estimate is spent.

Under the SAME $\mathsf{RH}(T)$, set $\epsilon=1/T$. W369--W370 retain the full signed pairing over all actual frequency zeros and multiplicities, including nonreal zeros beyond the verified height. The verified terms are nonnegative squares and the ENTIRE unverified tail gives
$\mathcal Q_W(h_{1/T})\ge-CM(F)\sqrt T\log(2+T)e^{-T}$.
The exact source identity W359, $\mathfrak E(F)=\alpha\mathcal Q_W(g_F)$, now proves the displayed $4/5$ bound on the nonpositive-energy class. A positive-energy source satisfies that lower bound directly; the zero source also requires no normalization. W257 and W371's homogeneous transport then give all displayed original-source inequalities. The filtered test remains auxiliary and is never substituted for the original source.

The available b=5/2 actual weight, the quadratic heat-loss budget $L_\epsilon^{-1}$, and the direct complete-prime cutoff give the exponent $4/5$. No optimality of this exponent is claimed. A fixed verified height still leaves a nonzero allowance; an evaluated constant, numerical improvement at the published height, full signed dominance, RH, strict Robin for every integer above 5040, Lean/kernel certification and literature priority are not asserted.
