---
bibkey: kalmykovkarp2017pfq
authors: S. I. Kalmykov and D. B. Karp
year: 2017
title: Log-concavity and Turán-type inequalities for the generalized hypergeometric function
doi: 10.1007/s10476-017-0503-z
url: https://arxiv.org/abs/1611.06724
claim: "Conjectures 1 and 2 assert coefficient nonnegativity for shifted hypergeometric Turanians when mu is at least one."
strata_touched:
  - D5/S3/Analytic/HypergeometricShiftTuran/Defs
  - D5/S3/Analytic/HypergeometricShiftTuran/Result
  - D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
  - D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult
license: citation-only
triage: anchor
---

# Shifted hypergeometric Turanian coefficients

## Verified locator

DOI: 10.1007/s10476-017-0503-z

Source: https://arxiv.org/abs/1611.06724

Pinned version: https://arxiv.org/abs/1611.06724v1, Section 3,
equations (2), (3), (9), (10), (13), Theorem 3 and Conjectures 1 and 2. Journal publication:
*Analysis Mathematica* 43 (2017), 567–580.

## Mathematical correspondence

Equation (10) defines

$$
f(\mu;x)=\sum_{n=0}^{\infty}
\frac{\Gamma(a+\mu+n)}{\Gamma(b+\mu+n)}\frac{x^n}{n!}.
$$

In the generalized parameter notation, the coefficient ratio is

$$
c(t)=\frac{\prod_{i=1}^{p}\Gamma(a_i+t)}
{\prod_{j=1}^{q}\Gamma(b_j+t)},
\qquad
f(\mu;x)=\sum_{n=0}^{\infty}c(\mu+n)\frac{x^n}{n!}.
$$

Equation (9) defines the shifted Turanian

$$
\Delta_f(\alpha,\beta;x)=
f(\mu+\alpha;x)f(\mu+\beta;x)
-f(\mu;x)f(\mu+\alpha+\beta;x),
$$

and its degree-$m$ coefficient is

$$
\delta_m=\sum_{k=0}^{m}
\frac{c(\mu+\alpha+k)c(\mu+\beta+m-k)
-c(\mu+k)c(\mu+\alpha+\beta+m-k)}{k!(m-k)!}.
$$

Condition (13) is the descending chain of consecutive ratios of elementary
symmetric functions of the denominator and numerator parameters:

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le
\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}
\qquad(0\le j<p).
$$

Theorem 3 proves $\Delta_f(\alpha,\beta;x)\ge0$ for $x\ge0$ when
$\mu,\beta\ge0$ and $\alpha\in\mathbb N$, under $p\le q$ and (13); if
$\alpha\le\beta+1$, it also proves $\delta_m\ge0$ for every
$m\in\mathbb N_0$. Conjecture 1 states verbatim:

> All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

The Lean definitions `Defs.coeff`, `Defs.turanCoeff`, `Defs.esymm` and
`Defs.cond13` encode the coefficient ratio, the finite Cauchy coefficient,
the elementary symmetric functions and condition (13). `Defs.claim` records
the coefficient conclusion in the $p\le q$ branch, while `Result.result`
refutes that coefficient clause.

The bounded literature scope and its limitations are stated in
`Problems/kalmykov-karp-pfq-conjecture-one-coefficients.md`.

## Two parameter blocks and Conjecture 2

Conjecture 2 on page 6 of arXiv:1611.06724v1 states verbatim:

> Conjecture 2. Suppose p1 ≤ q1 , p2 ≤ q2 and conditions (13) hold for a1 , b1 and a2 , b2 . Then the function µ → f (µ; x) defined in (3) is log-concave on [1, ∞) and the corresponding generalized Turánian ∆f (α, β; x) has nonnegative coefficients at all powers of x.

Section 2, page 3, states verbatim:

> We will always assume that a2 is not empty (i.e. p2 ≥ 1), while all other subvectors are allowed to be empty.

Equation (3) on page 2 is

$$
f(\mu;x)=\frac{\Gamma(\mathbf a_2+\mu)}{\Gamma(\mathbf b_2+\mu)}
\,{}_pF_q(\mathbf a_1,\mathbf a_2+\mu;
\mathbf b_1,\mathbf b_2+\mu;x),
\qquad p=p_1+p_2,\quad q=q_1+q_2.
$$

Vector Gamma and rising factorial expressions mean products over the entries.
The unshifted vectors are $\mathbf a_1,\mathbf b_1$; the shifted vectors
are $\mathbf a_2,\mathbf b_2$. Its Taylor coefficients are

$$
F_n(\mu)=
\frac{\prod_i(a_{1,i})_n}{\prod_j(b_{1,j})_n}
\frac{\prod_i\Gamma(a_{2,i}+\mu+n)}
{\prod_j\Gamma(b_{2,j}+\mu+n)}\frac{1}{n!}.
$$

`TwoBlockResult.pochRatio` is the unshifted rising factorial ratio,
`TwoBlockResult.seriesCoeff` is $F_n(\mu)$, and
`TwoBlockResult.twoBlockTuranCoeff` is the degree-$m$ finite Cauchy
coefficient of equation (2). `TwoBlockResult.claim` imposes positivity,
$p_1\le q_1$, $1\le p_2\le q_2$, and `Defs.cond13` separately on
both blocks, with $\mu\ge1$ and arbitrary nonnegative shifts.
`TwoBlockResult.result` refutes that coefficient clause with empty
unshifted blocks, shifted numerator $(1)$, seven shifted denominator
entries equal to $1/2$, and shifts $\alpha=\beta=1/2$ at $\mu=1$.
The log-concavity clause at a fixed nonnegative $x$ is not settled here.

The shared half-integer Gamma values in `Defs` follow from Mathlib's
`Real.Gamma_nat_add_half`; their reciprocal power products and the bound
$640/567<32/(9\pi)$ supply both coefficient calculations. The two-block
family, correspondence and bounded literature scope are stated in
`Problems/kalmykov-karp-pfq-conjecture-two-coefficients.md`.

## Function clause of Conjecture 1

Theorem 3, page 5 of arXiv:1611.06724v1, states verbatim (line breaks joined):

> Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.
> If p ≥ q and conditions (12) are satisfied, then ∆f (α, β; x) ≤ 0 for x ≥ 0, β ≥ 0 and α ∈ N. Moreover, if α ≤ β + 1, then δm ≤ 0 for all m ∈ N0.

Conjecture 1, page 6, states verbatim:

> Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

`FunctionResult.fval` is the real infinite sum in equation (10), using the
frozen Gamma ratio `Defs.coeff`. `FunctionResult.turanian` is equation (9).
`FunctionResult.claim` imposes $1\le p\le q$ and the remaining function
hypotheses, without the extra restriction needed only for coefficients.
The nonempty-$a_2$ sentence in Section 2 is followed by “In this section we
will consider log-convexity of the function f (µ; x) defined in (3) under these
assumptions.” Its scope in Section 3 need not be decided: the claim with
$1\le p$ is refuted by a witness valid under both the standing and
section-local readings. `FunctionResult.result` uses $p=1$, $a=(1)$,
$q=12$, $b_j=1/2$, $\mu=1$, $\alpha=\beta=1/2$, $x=2000$. The proof establishes convergence
and estimates the infinite sums; it does not infer a function sign from a
negative Taylor coefficient. Its exact scope is recorded in
`Problems/kalmykov-karp-pfq-conjecture-one-function.md`.
