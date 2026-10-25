---
bibkey: debruyne2026quantified
authors: Gregory Debruyne
year: 2026
title: A general quantified Wiener-Ikehara theorem
doi: null
url: https://arxiv.org/abs/2610.31016v1
claim: A signed residual with monotone compensation and the stated Tauberian conditions has a quantified Tauberian interface without nonnegative residual coefficients; the complete quantitative boundary and root-scale Robin tail conditions remain unproved in the project application.
strata_touched: []
license: citation-only
triage: anchor
---

# A signed-residual alternative and its remaining quantitative input

Debruyne, *A general quantified Wiener-Ikehara theorem*,
[arXiv:2610.31016v1](https://arxiv.org/html/2610.31016v1),
§2.3, Theorem 2.1 and Lemma 3.2, offers a different interface from
[the PTBZ Theorem B interface](../ArithSums/nicolas2025comparison.md#quantitative-tauberian-hypotheses-for-the-complete-response): the residual may have either sign if a specified
compensated function is monotone and the other Tauberian conditions
hold. Example 4.5 already treats the prime-counting functions, including
$\psi$; its PNT application is reused, not a new project deduction.

For the current complete source put

$$
S(y)=\begin{cases}e^{-y}\psi(e^y)-1,&y\ge0,\\0,&y<0.\end{cases}
\qquad
\mathcal L S(s)
=-\frac{\zeta'(1+s)}{(1+s)\zeta(1+s)}-\frac1s,
\quad\Re s>0.
$$

An exact parameter choice for the source's conditions T.1--T.11 is
$F=F_{\rm D}=1$, $h=h_{\rm D}=e^y$, $k(u)=e^u$,
$\alpha=1/2$ and $X=\log3$, with fixed constants. On $y\ge X$ the
compensated function $h(S+F)=\psi(e^y)$ is nondecreasing. The initial
segment matters: taking $X=0$ would fail T.3 because on $y<0$ the
compensated function is $e^y$, with supremum $1$, whereas $\psi(1)=0$.
At $X=\log3$, $\psi(3)=\log6>1$, and the bounded initial segment and
exponential variation bounds satisfy the stated conditions. Thus a
nonnegative-coefficient representation of the residual is not required
by this alternative. Subtracting further finite zero terms changes the
residual and requires rechecking its compensation and all these bounds.

The remaining analytic input is quantitative boundary control of

$$
g(t)=-\frac{\zeta'(1+it)}{(1+it)\zeta(1+it)}-\frac1{it},
$$

with its removable value at $t=0$. One must supply membership in a
selected complete boundary class $\mathcal T_*$, including its
all-height growth or regularity bounds, and the baseline condition
$E_*(y,1)\ll1$ for Theorem 2.1's optimized estimate. The class's cutoff
restrictions must also hold. A finite verified zero head supplies none
of these full quantitative bounds. Lemma 3.2 additionally requires the
global coarse bound (3.2), obtained first through Lemma 3.1 and its
boundary estimate; it cannot be invoked from monotonicity alone.

The exact return to the original Robin source is

$$
I_\psi(A)=\int_L^\infty S(y)\frac{1+y}{y^2}\,dy,
\qquad L=\log A.
$$

The required allowance is for this whole signed integral after
multiplication by $e^{L/2}L=\sqrt A\log A$, with the original reserve and
all remainder terms. A pointwise absolute error from the theorem would
therefore need its complete weighted tail integrated at this scale.
For example, $S(y)=O(e^{-y/2})$ would suffice for boundedness at this
normalization, but is stronger than the needed one-sided integral
condition and is not supplied here. The usual subexponential PNT error
does not pay that absolute tail budget. This source removes the specific
residual-positivity obstruction of the preceding interface; it supplies
no new root-scale estimate, signed Robin margin or RH proof.


## Averaged growth retains a separate all-height pole condition

Alberts, *An Explicit Tauberian Theorem taking Averaged Inputs with an
Application to Counting Abelian Number Fields*,
[arXiv:2508.20814v2](https://arxiv.org/html/2508.20814v2), revised
19 October 2026, Theorem 1.1, permits twisted integral bounds instead of
pointwise vertical growth bounds. Its transform is
$D(s)=s\int_1^\infty N(x)x^{-s-1}\,dx$. Besides absolute convergence
and the stated polynomial interior bounds, it requires meromorphic
continuation to the whole closed half-plane $\Re s\ge\sigma_a-\delta$
with only finitely many poles. On its left edge the input is

$$
\left|\int_T^{2T}D(\sigma_a-\delta\pm it)Z^{\pm it}\,dt\right|
\ll T^\eta(\log T)^\beta,
$$

for both signs, all $Z\ge e/2$ and those $T\ge e$ whose corresponding
dyadic vertical segment contains no pole of $D(s)/s$, with $\eta>0$ and
$\beta\ge0$. The residue expansion then has power saving
$\delta/\max\{\eta,1\}$ and the source's explicit logarithmic factor.
This is a weaker growth-input interface than the pointwise PTBZ
interface; it is not a supplied estimate for the present prime source.

For $N=\psi$, $D=-\zeta'/\zeta$ and $\sigma_a=1$. A left edge at or
below $1/2$ violates the finite-pole hypothesis because infinitely many
actual critical-line zeros give poles. Finite zero subtraction does not
repair that failure. For $\delta<1/2$, the displayed power saving is
strictly below $1/2$, while all-height finiteness of the remaining poles
is still an additional unproved input. Every retained zero residue also
needs its signed estimate. Theorems 1.5 and 1.7 require an increment
majorant $\widehat N$ with
$|N(X)-N(Y)|\le\widehat N(X)-\widehat N(Y)$ for every $X\ge Y$,
and the analytic and averaged hypotheses for both functions; the
majorant $\psi+X$ for $\psi-X$ retains the same zero poles.

The restricted-set variants are not imported here. Theorems 1.4 and 2.2
print a minimum over distances to the set containing the point itself,
whereas the floor/ceiling step in the proof uses consecutive-gap control.
A proposed sparse cutoff set therefore needs an independently justified
gap condition. Neither restricted sampling nor the free truncation
parameter replaces the all-height analytic hypotheses. No new root-scale
bound, complete signed Robin allowance or RH proof follows from this
comparison.
