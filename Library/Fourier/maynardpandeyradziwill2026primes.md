---
bibkey: maynardpandeyradziwill2026primes
authors: James Maynard; Mayank Pandey; Maksym Radziwiłł
year: 2026
title: Exponential sums over primes
doi: null
url: https://arxiv.org/abs/2608.14777v1
claim: "Theorem 1.1 replaces the classical 4/5 exponent by 19/24 for additive von Mangoldt sums under its rational-approximant conditions. Harmonic averaging gives a uniform centered golden-interval allowance; the common untwisted prime error and same-root Robin sign remain uncontrolled."
strata_touched: []
license: citation-only
triage: anchor
---

# Additive prime sums and the golden interval interface

The inspected primary is the authors' preprint
[arXiv:2608.14777v1](https://arxiv.org/pdf/2608.14777v1), submitted
14 August 2026. Locators refer to that version: **Theorem 1.1,
printed p.2**, and the introduction's comparison with the classical
bound on pp.1–2. The source statement and the parameter application
below were checked, not the complete analytic proof. This note makes
no peer-review, originality or Lean-verification claim. The new
exponential-sum theorem belongs to its authors and is reused here.

## The source keeps both denominator and frequency offset

Let $e(z)=\exp(2\pi iz)$ and let $\Lambda$ be the von Mangoldt
function, including proper prime powers. For $N\ge1$, write

$$
\alpha=\frac aq+\xi,\qquad (a,q)=1,\qquad
q\le N^{1/2},\qquad |\xi|\le\frac1{qN^{1/2}},
\qquad B=\max(q,qN|\xi|).
$$

Theorem 1.1 states

$$
\left|\sum_{n<N}\Lambda(n)e(n\alpha)\right|
\le N^{o(1)}\left(\frac N{\sqrt B}+N^{19/24}\right).
\tag{M1}
$$

The source compares this with the classical $N^{4/5}$ term and notes
$4/5-19/24=1/120$. Its statement is unconditional, with all the
displayed parameters retained. At zero frequency, $q=1,\xi=0$ gives
$B=1$ and a bound of order $N^{1+o(1)}$; it is not a centered
square-root estimate for $\psi(N)-N$.

## Average the approximant parameter over golden harmonics

Put $\varphi=(1+\sqrt5)/2$. Its quadratic irrationality supplies a
fixed $c>0$ with $\|m\varphi\|\ge c/m$ for all integers $m\ge1$.
For each $h\ge1$, choose the reduced Dirichlet approximant to
$h\varphi$ at scale $N^{1/2}$ required in (M1), and call its
parameter $B_h$. This gives

$$
B_h\le N^{1/2},\qquad
B_h\ge\max\left(q_h,\frac{cN}{hq_h}\right)
\gg\sqrt{N/h}.
$$

It is necessary to average $B_h^{-1/2}$, rather than substitute the
smallest allowed $B_h$ for every harmonic. In a block
$H<h\le2H$, if $B_h\le Q$, then

$$
m=hq_h\le2HQ,\qquad \|m\varphi\|\le Q/N.
$$

Distinct such integers have circle separation at least $c/(2HQ)$.
The union of the two arcs adjacent to zero has total length $2Q/N$,
so it contains $O(1+HQ^2/N)$ such integers. Each integer $m$ has at
most $\tau(m)$ possible divisors $h$. For $H\le N^{5/24}$ and
$Q\le N^{1/2}$, the standard divisor bound absorbs this multiplicity
in $N^{o(1)}$. Hence

$$
\#\{H<h\le2H:B_h\le Q\}
\ll N^{o(1)}(1+HQ^2/N).
\tag{M2}
$$

Split $Q$ into dyadic scales between a constant times
$\sqrt{N/H}$ and $\sqrt N$. Multiplying (M2) by $Q^{-1/2}$
and summing gives

$$
\sum_{H<h\le2H}B_h^{-1/2}
\ll N^{o(1)}\left((H/N)^{1/4}+HN^{-1/4}\right)
\ll HN^{-1/4+o(1)}.
$$

The first block containing $h=1$ obeys the same bound. Applying (M1)
block by block therefore yields, with
$L=\lfloor N^{5/24}\rfloor$,

$$
\sum_{1\le h\le L}\frac1h
\left|\sum_{n<N}\Lambda(n)e(h\varphi n)\right|
\ll N^{19/24+o(1)}.
$$

Use the interval approximants in
[DMS v2, Theorem 3.3, printed p.25](drmotamullnerspiegelhofer2025primes.md),
whose main coefficient is the interval length, nonconstant
coefficients are bounded by $1/(\pi|h|)$, and positive error
coefficients by $1/(L+1)$. Nonnegativity of $\Lambda$ and the classical
bound $\psi(N)=O(N)$ pay the zero coefficient of that error by
$O(N/L)$. The nonconstant error coefficients are paid by the same
harmonic sum since $1/(L+1)\le1/h$. Consequently, uniformly over all
circle intervals $I$,

$$
\sum_{n<N}\Lambda(n)
\bigl(\mathbf1_I(\{n\varphi\})-|I|\bigr)
=O_\epsilon(N^{19/24+\epsilon})
\quad\text{for every fixed }\epsilon>0.
$$

## Remove prime powers before reading a support-prime label

The preceding indicator reads the digits of $n=p^k$, not of its base
prime. Remove **all** terms with $k\ge2$ before identifying a
support-prime class. Their total weight is
$O(N^{1/2}(\log N)^2)$, uniformly in $I$, so it is smaller than
the displayed allowance. Define

$$
\Theta_I(X)=\sum_{\substack{p\le X\\\{p\varphi\}\in I}}\log p,
\qquad
\Pi_I(X)=\#\{p\le X:\{p\varphi\}\in I\}.
$$

Endpoint changes between $n<N$ and $p\le X$ cost only $O(\log X)$.
Abel summation of the centered logarithmic prime count then gives,
for each fixed $0<\epsilon<5/24$, uniformly in $I$ and $X\to\infty$,

$$
\Theta_I(X)-|I|\vartheta(X)
=O_\epsilon(X^{19/24+\epsilon}),
\qquad
\Pi_I(X)-|I|\pi(X)
=O_\epsilon(X^{19/24+\epsilon}/\log X).
\tag{M3}
$$

Finite endpoint conventions and unions of at most two circle intervals
preserve these uniform constants. This is a parameter application of
(M1) and standard interval approximation, not a new prime-distribution
theorem. DMS's exact low-address detection transports (M3) to the
[same actual CA correction](drmotamullnerspiegelhofer2025primes.md#quantitative-resolution-of-the-same-prime-axis-cut),
including a sufficient range of growing Fibonacci prefixes.

The centering in (M3) is the actual total prime count and weight. It
does not supply a power-saving bound for their ordinary PNT error, a
single CA integer's digit law, or a sign for the
[full-support Robin residual](../Analytic/polak2026finiterobinca.md).
