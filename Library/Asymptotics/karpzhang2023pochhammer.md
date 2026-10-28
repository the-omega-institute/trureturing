---
bibkey: karpzhang2023pochhammer
authors: Dmitrii Karp and Yi Zhang
year: 2023
title: Log-concavity and log-convexity of series containing multiple Pochhammer symbols
doi: 10.1007/s13540-023-00238-0
url: https://arxiv.org/abs/2305.09029
claim: "Conjecture 5.2 asserts coefficient-wise log-concavity of both the reciprocal-Pochhammer series and the related gamma series for a log-concave coefficient sequence."
strata_touched:
  - D5/S3/Analytic/KarpZhangReciprocal/BirthDeath
  - D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
  - D5/S3/Analytic/KarpZhangReciprocal/Result
  - D5/S3/Analytic/KarpZhangGamma/Series
  - D5/S3/Analytic/KarpZhangConjecture/Result
  - D5/S3/Analytic/KarpZhangCatalanPower/Result
  - D5/S3/Analytic/KarpZhangNinh/Result
  - D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations
license: citation-only
triage: anchor
---

# Karp--Zhang reciprocal-Pochhammer coefficients

## Verified locator

DOI: 10.1007/s13540-023-00238-0

Source: https://arxiv.org/abs/2305.09029

Pinned source: [arXiv:2305.09029v3](https://arxiv.org/abs/2305.09029v3).
The locators below use the printed page numbers of that version.

## Conjecture 5.2, page 12

> Suppose that $\{y_k\}_{k=0}^{\infty}$ is a log-concave sequence. Then the functions $\mu\to\widetilde y(\mu;x)$ and $\mu\to\widehat y(\mu;x)$ are coefficient-wise log-concave on $\mu>0$.

Immediately before the conjecture, the source defines

$$
\widetilde y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{(2\mu)_k}{(\mu)_k k!}x^k,
\qquad
\widehat y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{\Gamma(\mu+k)}{\Gamma(2\mu+k)k!}x^k.
$$

## Definition 1.1, page 2

> Let $\{f_k\}_{k=0}^{\infty}$ be a non-negative nontrivial real sequence. We call $\{f_k\}_{k=0}^{\infty}$ log-concave (or Pólya frequency two – $PF_2$, or doubly positive) if $f_k^2\ge f_{k-1}f_{k+1}$ for each $k\in\mathbb N$, and $\{f_k\}_{k=0}^{\infty}$ is supported on an interval of integers (i.e., $f_N=0$ implies either $f_{N+i}=0$ for all $i\in\mathbb N_0$ or $f_{N-i}=0$ for $i=0,\ldots,N$).

The sequence convention includes nonnegativity, nontriviality, the adjacent
log-concavity inequalities and absence of internal zeros. A formal power
series assertion is a separate inequality in every natural degree, without
any convergence requirement.

## Mathematical correspondence

`Coeff.c` is exactly the coefficient $(2t)_n/((t)_n n!)$ of the reciprocal
series. `Coeff.lambda` is its adjacent-degree ratio before division by
$n+1$. `Coeff.eta`, `Coeff.psi` and `Coeff.chi` give the adjacent score
increment, score and negative logarithmic curvature as explicit rational
finite sums. `Coeff.coefficient_calculus` includes the degree-uniform
curvature estimate.

`BirthDeath.variance_bound` is a finite variance estimate used to control
the score variance in interval convolutions. `IntervalConvolution.shift_tail`
and finite Abel summation give `KarpZhangReciprocal.Result.reciprocal_half`.
Exponential smoothing, the one-sign-change reciprocal-gamma kernel and the
positive diagonal transformation give `KarpZhangGamma.Series.gamma_half`.
`KarpZhangConjecture.Result.claim` states the conjunction of the two
coefficient assertions using those exact finite coefficients, and
`KarpZhangConjecture.Result.result` proves it for the source's full sequence
and parameter range.

## Conjecture 4.2, page 8

> Assume that $\{h_k\}_{k=0}^{\infty}$ is log-concave (log-convex ) and independent of $\mu$. Then the function $\mu\to h(\mu;x)$ defined in (15) is coefficient-wise log-concave (log-convex ).

Formula (15), page 8:

> We consider the series

$$
h(\mu;x)=\sum_{k=0}^{\infty}h_k\frac{(\mu)_{2k}}{(\mu+1)_k k!}x^k.
$$

## Lemma 4.1(2), page 8

> Lemma 4.1. [17, Lemma 7] The hypergeometric function $\lambda(\mu;x)$ has the following properties.
>
> 2. Index law
>
> $\lambda(\alpha;x)\lambda(\beta;x)=\lambda(\alpha+\beta;x)$.

The source attributes this lemma to its reference [17], Lemma 7; no
independent verification of that earlier reference is asserted here.
Equating degree-$m$ Cauchy coefficients gives the finite index law used
in `KarpZhangCatalanPower.Index.index_law`. Formula (15) and this index law
are literature statements; the polynomial continuation and Lean proofs
are authored formalizations.

The log-convex clause of Definition 1.1, page 2, reads:

> If $f_k^2\le f_{k-1}f_{k+1}$ for all $k\in\mathbb N$, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).

The initial nonnegative, nontrivial sequence assumption applies to both
classes. Here $\mathbb N=\{1,2,\ldots\}$. Taken literally, the
log-convex inequalities also allow a nontrivial sequence supported on
$\{0\}$; the coefficient assertion includes that case and imposes no
extra positivity hypothesis.

`KarpZhangCatalanPower.Coeff.a` is the quotient in (15).
`KarpZhangCatalanPower.Index.index_law` is its convolution index law.
`KarpZhangCatalanPower.Index.b_eq_centralBinom` identifies the positive
derivative generator. `KarpZhangCatalanPower.Interval.tail_nonneg` proves
nonnegative central tails by reflected-interval cancellation and balancing.
`KarpZhangCatalanPower.Result.result` proves both coefficient signs for
all nonnegative base parameters and nonnegative real shifts, reusing the sequence class
and finite Abel identity from `KarpZhangReciprocal.Result`.

## Coefficient-wise convention, page 1

> if the coefficients $\delta_k$ at all powers of $x$ in (2) are non-negative (non-positive) for all $\alpha,\beta\ge0$ we will say that $\mu\to f(\mu;x)$ is coefficient-wise log-concave (log-convex ).

## Lemma 3.1, page 4

> Let $k,m\in\mathbb N_0$ with $k\le m/2$, $\mu\ge0$ and $\alpha,\beta>0$. Set
>
> $$
> T_{k,m}:=(\mu+\alpha)_k(\mu+\beta)_{m-k}+(\mu+\alpha)_{m-k}(\mu+\beta)_k
> -(\mu)_k(\mu+\alpha+\beta)_{m-k}-(\mu)_{m-k}(\mu+\alpha+\beta)_k.
> $$
>
> If $T_{k,m}\le0$ for some $1\le k\le m/2$, then $T_{k-1,m}<0$.

This is formula (8). `KarpZhangNinh.Result.Kernel.pairPoch` uses $a,b,c,N$
for $\mu,\alpha,\beta,m$ respectively.
`KarpZhangNinh.Result.Kernel.paired_sign_step` proves the positive-$\mu$
specialization of the published backward-sign implication. The paired
length argument is part of `D5/S3/Analytic/KarpZhangNinh/Result.lean`.

## Conjecture 3.8, page 8

> Assume that $\{f_n\}_{n=0}^{\infty}$ is log-concave and independent of $\mu$. Then the function
>
> $$
> \mu\to f(\mu;x)=\sum_{n=1}^{\infty} f_n\frac{(\mu)_{3n}}{(3n-1)!}x^n
> $$
>
> is coefficient-wise log-concave.

The sum starts at $n=1$, so its degree-zero coefficient is zero.
The sequence class is Definition 1.1, including interval support.
Coefficient-wise log-concavity means nonnegativity of every finite Cauchy
coefficient of
$f(\mu+\alpha;x)f(\mu+\beta;x)-f(\mu;x)f(\mu+\alpha+\beta;x)$,
for nonnegative real $\mu,\alpha,\beta$.

Remark 3.7, on the same page, states that the analogous unweighted family
with $(\mu)_{rn}/(rn-1)!$ is neither coefficient-wise log-convex nor
coefficient-wise log-concave for $r\ge4$ by numerical computations.
This is a source-reported numerical boundary, not an all-parameter
formal refutation supplied by the $r=3$ assertion.

## Rising-factorial log-concavity, equation (6), page 4

> Note that
>
> $$
> [\log((\mu)_{nr})]''=\psi'(\mu+rn)-\psi'(\mu)\le0, \tag{6}
> $$

Here $\psi$ is the digamma function. For any degree $d\ge2$, take the
source index $n=1$ and multiplier $r=d$. The log-concavity assertion gives
the four-point inequality below: for $F(t)=\log((t)_d)$, concavity makes
$F(t+\alpha)-F(t)$ nonincreasing in $t$. Comparing $t=\mu$ and
$t=\mu+\beta$ and exponentiating gives

$$
(\mu+\alpha)_d(\mu+\beta)_d
\ge (\mu)_d(\mu+\alpha+\beta)_d
\qquad(\mu>0,\ \alpha,\beta\ge0).
$$

Degree zero is equality and the degree-one difference is $\alpha\beta$.
This is `KarpQuadraticTruncations.pochhammer_turan_nonneg`; its owner is
`D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.lean`.
The homogeneous trisection identities for Conjecture 3.8 are in the
`Homogeneous` namespace of `D5/S3/Analytic/KarpZhangNinh/Beta.lean`;
the same module supplies symmetric beta lifting.
