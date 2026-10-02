---
bibkey: chirrehelfgott2025nonnegative
authors: Andrés Chirre, Harald Andrés Helfgott
year: 2025
title: Optimal bounds for sums of non-negative arithmetic functions
doi: null
url: https://arxiv.org/abs/2512.15709v1
claim: Finite-height zero verification supplies an explicit cumulative half-weighted Mangoldt estimate; partial summation fills its lower interval and transports it to the actual Weil autocorrelation, while leaving the required sign unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Half-weighted Mangoldt sums and the actual Weil remainder

The primary source is [Chirre–Helfgott, arXiv:2512.15709v1](https://arxiv.org/pdf/2512.15709v1), submitted 17 December 2025; the PDF title page is dated 18 December. The arXiv version history checked on 1 October 2026 lists only v1. Proposition 9.1 and Corollary 1.3 were read in the original text, with the proposition also checked against its HTML TeX. This is a source application, not an independent audit of the full paper or a rerun of its finite computations. The integral applications below remain paper-level.

## The existing half-weighted supplier

Write

$$
A_{1/2}(x)=\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n},\qquad
c=\frac{\zeta'(1/2)}{\zeta(1/2)},\qquad
G(x)=A_{1/2}(x)-2\sqrt x+c.
$$

The constant $c$ is real. The half weight refers to $n^{-1/2}$; the ordinary cumulative sum gives full weight to an atom at $n=x$.

Proposition 9.1, printed p.34, assumes that every nontrivial zero with $0<\Im\rho\le T$ lies on the critical line, with $T\ge10^7$. For $x>\max(T,10^9)$, its specialization at $\sigma=1/2$ is

$$
\left|A_{1/2}(x)-m_T\sqrt x+c\right|
\le\frac{\pi\sqrt x}{T-1}+C_T,
$$

$$
m_T=\frac\pi T\coth\frac\pi{2T},\qquad
C_T=\frac1{2\pi}\log^2\frac T{2\pi}-\frac1{6\pi}\log\frac T{2\pi}.
$$

Since $m_T>2$, this implies

$$
|G(x)|\le\eta_T\sqrt x+C_T,\qquad
\eta_T=m_T-2+\frac\pi{T-1}>0. \tag{1}
$$

The source cites Platt–Trudgian's verification through height $3000175332800$. It allows a fixed $T$ in that verified range without assuming global RH. This note does not verify additional heights or silently let $T$ tend to infinity.

## A complete lower-interval budget from the same source

Corollary 1.3, printed p.3, gives for every $x\ge1$

$$
|\psi(x)-x|\le ax+b\sqrt x,\qquad
a=\frac\pi{3\cdot10^{12}},\quad b=113.67.
$$

Its stated whole-range conclusions concern weights $1$ and $1/n$, not $1/\sqrt n$. The following partial summation supplies the latter's lower interval without enumerating primes to $T$. Put $E_\psi(x)=\psi(x)-x$. As $\psi(1)=0$,

$$
A_{1/2}(x)=\frac{\psi(x)}{\sqrt x}+\frac12\int_1^x\frac{\psi(u)}{u^{3/2}}du,
$$

$$
G(x)=c-1+\frac{E_\psi(x)}{\sqrt x}+\frac12\int_1^x\frac{E_\psi(u)}{u^{3/2}}du. \tag{2}
$$

In particular $G(1)=c-2$. Taking absolute values only after this identity gives the explicit all-$x$ envelope

$$
|G(x)|\le B_0(x):=|c-1|+a(2\sqrt x-1)+b(1+\tfrac12\log x). \tag{3}
$$

For any fixed admissible $T$ define

$$
\mathcal B_T(t)=
\begin{cases}
B_0(e^t),& e^t\le\max(T,10^9),\\
\min\{B_0(e^t),\eta_Te^{t/2}+C_T\},&e^t>\max(T,10^9).
\end{cases} \tag{4}
$$

Equations (1)–(3) prove $|G(e^t)|\le\mathcal B_T(t)$ for all $t\ge0$. The strict threshold in the original proposition is respected. Equations (2)–(4) are applications of its existing results, not a stronger prime-number theorem.

The source already gives a sharper finite lower interval. Lemma 9.2, printed p.35, states $|\psi(x)-x|\le\sqrt2\sqrt x$ for $1\le x\le10^{13}$. Applying (2) on that whole initial interval gives

$$
|G(x)|\le B_{\rm low}(x):=|c-1|+\sqrt2(1+\tfrac12\log x),\qquad 1\le x\le10^{13}.
$$

One can therefore also take the minimum with $B_{\rm low}(e^t)$ whenever $e^t\le10^{13}$. For $T$ within the quoted verification height, this interval overlaps the proposition's range, so there is no uncovered transition. This uses the source's existing finite computation as an input; it has not been independently rerun here.

## Exact transport to the same test

For $f\in C_c^\infty(\mathbb R;\mathbb C)$ supported in $[-L,L]$, set

$$
R_f(t)=\Re\int f(x)\overline{f(x-t)}dx,\qquad
m=\|f\|_2^2,\quad H_1=\|f'\|_2^2.
$$

Use the full-form normalization of the [localization note](frankliebseiringer2006hardy.md), with $a_0=\operatorname{digamma}(1/4)+4-\log\pi$. The classical functional equation gives $2c-4=-a_0$. Existing [completed-zeta logarithmic derivative](../../D5/S3/Weil/ZetaExplicit/XiLogDeriv.lean) and [Gamma derivative](../../D5/S3/Weil/ZetaExplicit/GammaRBracket.lean) sources supply the normalization ingredients; it is not an arithmetic sign estimate.

Since $A_{1/2}(1)=0$, $R_f(0)=m$ and $R_f(2L)=0$, Stieltjes integration by parts gives

$$
J_{0,L}(f)=-a_0m+2\int_0^{2L}G(e^t)R_f'(t)dt,\qquad
Q_{\rm full}(f)=E_*(f)+2\int_0^{2L}G(e^t)R_f'(t)dt. \tag{5}
$$

The endpoint mass factor is essential; omitting it presupposes unit normalization. The positive constant reserve exposed by localization is now included in the exact centering, not established as an arithmetic lower bound.

A transient exact Lean application of the existing functional equation, nonvanishing at $1/2$, and Gamma derivative verifies $2c-4=-a_0$, with only the standard logical axioms. No named wrapper was retained. This scalar check does not certify the Stieltjes integral, the external error estimates or the full-form identity (5).

The source legitimately supplies the finite-support estimate

$$
|J_{0,L}(f)+a_0m|
\le2\int_0^{2L}\mathcal B_T(t)|R_f'(t)|dt
\le2\int_0^{2L}\mathcal B_T(t)\min\{tH_1,\sqrt{mH_1}\}\,dt. \tag{6}
$$

The two derivative bounds follow respectively from $R_f'(0)=0$, $\|R_f''\|_\infty\le H_1$, and Cauchy–Schwarz applied to the derivative of the correlation. The theorem's nonnegative arithmetic coefficients are $\Lambda(n)$. Neither $R_f$ nor $R_f'$ is required to be nonnegative. One cannot substitute their signed product into the source's nonnegative-coefficient theorem; (5) is the explicit signed transport.

## The primitive is the existing screw kernel

Define, for $t\ge0$,

$$
P(t)=\int_0^tG(e^u)du,\qquad
K(t)=\int_t^\infty(u-t)\frac{e^{-5u/2}}{1-e^{-2u}}du.
$$

Then direct integration of the same arithmetic atoms gives

$$
P(t)+K(t)-K(0)=g_\zeta(t), \tag{7}
$$

where $g_\zeta$ is precisely the source's existing real even screw function, [Suzuki v3](suzuki2026screw.md), equation (1.3), printed p.4, already recorded in the [project's F16 criterion](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md). To match formulas, write $a_n=2n+1/2$ and $K(t)=\sum_{n\ge1}e^{-a_nt}/a_n^2$. The $n=0$ term in Suzuki's Lerch expression is $4e^{-t/2}$; its difference from its value at zero combines with $-4(e^{t/2}-1)$ in $P$. The linear term is $ct=-\tfrac t2(\operatorname{digamma}(1/4)-\log\pi)$. This accounts for every term and does not define a new kernel.

Two integrations by parts, or the existing same-test screw representation, therefore give

$$
Q_{\rm full}(f)=\iint g_\zeta(x-y)f'(x)\overline{f'(y)}dxdy. \tag{8}
$$

At the lower endpoint, $R_f'(0)=0$, $R_f(0)-R_f(t)=O(t^2)$ and $K'(t)=\tfrac12\log t+O(1)$, so the Gamma singularity contributes no integration-by-parts boundary term. The constant $K(0)$ disappears because $\int f'=0$. An added half-axis drift $dt$, extended evenly as $d|t|$, would instead change this derivative form by $-2d\|f\|_2^2$; zero mean does not remove it. Suzuki's operator identity already owns the representation in (8). The conditional positive definiteness of this actual kernel is an RH criterion, not a consequence of (7).

## Why a finite-height absolute envelope is insufficient

For a fixed nonzero normalized $h\in C_c^\infty$ and $f_R(x)=R^{-1/2}h(x/R)$, write $R_{f_R}(t)=r(t/R)$. The known energy satisfies $0\le E_*(f_R)\le(26/125)\|h'\|_2^2/R^2$. To prove positivity via (5) one still needs

$$
\frac2R\int_0^\infty G(e^t)r'(t/R)dt\ge-E_*(f_R). \tag{9}
$$

The fixed-$T$ term in (1), after this transport, costs $2\eta_T\int e^{Ru/2}|r'(u)|du$. The derivative cannot vanish on the whole positive half-line, since $r(0)=1$ and $r$ has compact support. It has absolute value bounded below on some closed interval with positive left endpoint. Thus this particular error envelope grows exponentially in $R$. Taking the minimum in (4) does not fix the issue: both candidate envelopes retain a positive fixed coefficient of $e^{t/2}$. Improving a fixed verified height changes that coefficient but supplies no unbounded sequence of verified heights.

There is also a scale-independent loss in using only a symmetric constant error box. For $C>0$ and $|U(t)|\le C$, the relaxed worst value of $2\int U(t)R_f'(t)dt$ is $-2C\int|R_f'(t)|dt\le-2Cm$. This is a diagnostic for that relaxation, not a claim that such a worst-case $U$ is the actual arithmetic $G$. A fixed positive absolute allowance alone cannot replace the missing signed relation to the same test. Applying these absolute envelopes on a finer FIB partition supplies no additional signed information. The preceding identities and bounds do not prove (9), all-support Weil positivity, Robin or RH.
