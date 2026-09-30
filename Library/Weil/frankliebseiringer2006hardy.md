---
bibkey: frankliebseiringer2006hardy
authors: Rupert L. Frank, Elliott H. Lieb, and Robert Seiringer
year: 2006
title: Hardy-Lieb-Thirring inequalities for fractional Schrodinger operators
doi: null
url: https://arxiv.org/abs/math/0610593v2
claim: The classical nonlocal IMS formula supplies the square-partition error structure. Its application to the actual Weil form must retain the joint pole-prime correction and prime translations between nonadjacent FIB windows; it supplies no all-support positivity estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Nonlocal localization and the actual Weil correction

The primary source is [Frank–Lieb–Seiringer, arXiv:math/0610593v2](https://arxiv.org/pdf/math/0610593v2), 27 October 2006, §3.3, Lemma 3.5 and equation (3.13), printed p.12. For $u\in C_c^\infty(\mathbb R^d)$, $0<s<\min(1,d/2)$ and a finite real Lipschitz square partition $\sum_j\chi_j(x)^2=1$ for all $x\in\mathbb R^d$, it writes the fractional Hardy form as the sum of the localized forms minus an integral-operator correction. That correction has kernel

$$
a_{s,d}|x-y|^{-d-2s}\sum_j(\chi_j(x)-\chi_j(y))^2.
$$

The paper's fractional kernel is not the Weil Gamma kernel and has no prime atoms or zeta pole term. The transferable ingredient is the localization calculation; its arithmetic application below is a separate paper derivation, not an additional theorem attributed to that source or a newly compiled general Weil theorem. A nonnegative pointwise correction kernel need not define a positive semidefinite operator.

## Common test and normalization

Use the project's [actual energy decomposition](../../D5/S3/Weil/Separator/UnconditionalExplicitFormula.lean). Let $f\in C_c^\infty(\mathbb R;\mathbb C)$ be even, with support in $[-L,L]$, $L>0$. Let $\chi_1,\ldots,\chi_m$ be real, even, smooth functions satisfying $\sum_i\chi_i(x)^2=1$ on $[-L,L]$, and put $f_i=\chi_i f$. Each $f_i$ is an admissible even test. Use the same global $L$ for every term. Write

$$
E_t(f)=\int_{\mathbb R}|f(x)-f(x-t)|^2\,dx,
\qquad k_\Gamma(t)=\frac{e^{-t/2}}{1-e^{-2t}},
\qquad P(f)=2\left|\int_{\mathbb R}e^{x/2}f(x)\,dx\right|^2.
$$

With $w_n=\Lambda(n)/\sqrt n$, the source form is

$$
Q(f)=P(f)+\int_0^\infty k_\Gamma(t)E_t(f)\,dt
+\sum_{2\le n\le e^{2L}}w_nE_{\log n}(f)-c_L\|f\|_2^2,
\qquad c_L=2\sum_{2\le n\le e^{2L}}w_n-c_\Gamma.
$$

Here $c_\Gamma=\Re\operatorname{digamma}(1/4)-\log\pi$, and $\Lambda$ includes prime powers. A linear partition $\sum\rho_i=1$ is not automatically a square partition. Taking $\sqrt{\rho_i}$ also needs a smoothness argument at its zeros. The ordinary smooth partition construction in [ExternalSupportInvisibility](../../D5/S3/Weil/TestFunctions/ExternalSupportInvisibility.lean) does not by itself settle these obligations.

Define the real defect correlation

$$
D_\chi(x,t)=\sum_i(\chi_i(x)-\chi_i(x-t))^2,
\qquad K_f(t)=\int_{\mathbb R}D_\chi(x,t)\Re\bigl(f(x)\overline{f(x-t)}\bigr)\,dx.
$$

Square expansion gives the one-shift IMS identity

$$
\sum_i E_t(f_i)-E_t(f)=K_f(t).
$$

There is no extra $1/2$ in this one-shift convention. The mass term cancels because $\sum_i\|f_i\|_2^2=\|f\|_2^2$. The function $K_f$ is real, even, smooth, supported in $[-2L,2L]$, and $K_f(0)=K_f'(0)=0$. It need not be nonnegative for complex or sign-changing $f$.

## Keep the pole and primes together

The global pole does not split into independent local squares. Expanding it gives

$$
P(f)-\sum_iP(f_i)
=\iint e^{(x+y)/2}\sum_i(\chi_i(x)-\chi_i(y))^2
\Re\bigl(f(x)\overline{f(y)}\bigr)\,dx\,dy.
$$

Evenness of both $f$ and the multipliers permits $y\mapsto-y$, changing the exponential to $e^{(x-y)/2}$ without changing the remaining factor. Setting $t=x-y$ and pairing positive and negative $t$ yields

$$
P(f)-\sum_iP(f_i)=2\int_0^\infty\cosh(t/2)K_f(t)\,dt.
$$

Consequently the complete localization correction is

$$
Q(f)-\sum_iQ(f_i)
=\int_0^\infty e^{t/2}K_f(t)\,dt
-\sum_{2\le n\le e^{2L}}\frac{\Lambda(n)}{\sqrt n}K_f(\log n)
-\int_0^\infty\frac{e^{-5t/2}}{1-e^{-2t}}K_f(t)\,dt. \tag{1}
$$

This uses the exact cancellation
$2\cosh(t/2)-k_\Gamma(t)=e^{t/2}-e^{-5t/2}/(1-e^{-2t})$.
Estimating the pole and prime terms separately would discard this common-source cancellation.

Let $\Psi(u)=\sum_{n\le u}\Lambda(n)$ be the right-continuous Chebyshev function, distinct from the golden conjugate, and define $W_f(u)=u^{-1/2}K_f(\log u)$ for $u\ge1$. Equation (1) becomes

$$
Q(f)-\sum_iQ(f_i)
=\int_1^{e^{2L}}(\Psi(u)-u)W_f'(u)\,du
-\int_1^{e^{2L}}\frac{W_f(u)}{u(u^2-1)}\,du. \tag{2}
$$

Indeed the first two terms of (1) equal $-\int W_f\,d(\Psi-u)$. Integration by parts has no boundary charge: $W_f(1)=W_f(e^{2L})=0$. At $u=1$, $W_f(u)=O((u-1)^2)$, so the second integrand is integrable. Compact support makes this a finite-scale identity without any PNT or RH hypothesis. This calculation preserves signs; it is not a bound on the Chebyshev error.

For a joint Lipschitz bound $\|\chi(x)-\chi(y)\|_{\ell^2}\le B|x-y|$ on $[-L,L]$, Cauchy–Schwarz gives $|K_f(t)|\le B^2t^2\|f\|_2^2$. Thus the last term of (1) has absolute value at most $C_*B^2\|f\|_2^2$, where

$$
C_*:=\int_0^\infty\frac{t^2e^{-5t/2}}{1-e^{-2t}}\,dt
=2\sum_{m\ge0}(2m+5/2)^{-3}<\infty.
$$

A cutoff family with $B\le C/L$ would give an $O(L^{-2})$ bound for this Gamma remainder. The existence of such a family subordinate to increasingly fine FIB windows is an additional condition, not a consequence of the window count. The signed first integral in (2) remains the arithmetic obligation for the same actual $f$ and cutoffs. A large absolute-value envelope neither supplies that lower bound nor proves no better estimate is possible.

## A prime edge crossing an intermediate FIB window

The five first-level internal-coordinate intervals have geometric order $[3],[null],[5],[2],[2\ 5]$. Put $\varphi=(1+\sqrt5)/2$. In particular

$$
I_3=[-1,\varphi-2],\qquad I_{null}=[\varphi-2,2\varphi-3],\qquad I_5=[2\varphi-3,\varphi-1].
$$

For this test construction, choose these numerical intervals as windows in the Weil physical $x$ coordinate. This choice does not identify prime translation with an operation on the original golden-coordinate source or prove an intertwining theorem. Translation by $\log2$ sends the entire interval $[-41/100,-39/100]\subset\operatorname{int}I_3$ into $\operatorname{int}I_5$, across $I_{null}$. This is an edge of the actual prime translation, not a legal-digit seam transition.

For a smooth example take a nonzero even real $\eta\in C_c^\infty(-1/100,1/100)$, $a=2/5$, $b=\log2-2/5$, and

$$
f(x)=\eta(x-a)+\eta(x+a)+\eta(x-b)+\eta(x+b).
$$

It is even with support in $[-41/100,41/100]$. At this radius $2<e^{2L}<3$, so the only active prime power is $2$. The four bump supports are disjoint. Exactly the ordered centre pairs $(a,-b)$ and $(b,-a)$ have separation $\log2$, giving

$$
\int f(x)f(x-\log2)\,dx=2\|\eta\|_2^2>0.
$$

The original prime contribution to $Q$ is therefore $-2\sqrt2\log2\,\|\eta\|_2^2$. The pair $(b,-a)$ crosses $I_{null}$, whereas $(a,-b)$ connects $I_{null}$ to $I_5$. Dropping the nonadjacent pair alone loses $-\sqrt2\log2\,\|\eta\|_2^2$, half of the displayed prime contribution, even for a legitimate even smooth test. This is not a negative-full-form example and does not refute RH. Pairing mirrored windows to keep evenness changes their support geometry and must retain the corresponding cross terms.

## Reuse and remaining research target

The standard IMS identity is reusable mathematics, not a new FIB positivity theorem. The project's [smooth rational approximation](../../D5/S3/Weil/TestFunctions/RationalCutoffApproximation.lean) controls the complete paired zero sum; its [golden cofinal interface](../../D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.lean) still requires positivity for every admitted test at every chosen scale. Neither supplies a lower bound for the signed integral in (2).

A sufficient next input would combine genuine lower margins for the localized tests with a lower bound for the **same** $W_f$ against $\Psi-u$, paying the displayed Gamma remainder uniformly over all allowed coefficients and growing supports. The family $W_f$ is constrained by a common $f$ and square partition; it cannot be replaced by arbitrary independently optimized weights. The corresponding Robin research also retains a joint signed prime fluctuation, but identifying those two test families requires another explicit map.

The analytic localization and Stieltjes calculations above are paper-level applications with their hypotheses displayed, not a new Lean closure. Transient exact Lean checks cover only the stated rational interval placement, first-prime support threshold, pointwise four-bump pairing, and scalar Gamma cancellation; no named wrapper is retained. The nonlocal source, these checks, and the missing all-scale arithmetic estimate have different evidentiary roles.
