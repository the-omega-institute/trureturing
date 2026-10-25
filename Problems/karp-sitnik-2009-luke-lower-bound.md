---
slug: karp-sitnik-2009-luke-lower-bound
bibkey: karpsitnik2009luke
doi: 10.1016/j.jat.2008.10.002
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KarpSitnikLuke/Result.result
url: https://arxiv.org/abs/math/0703084
---

# Refutation of the sum-condition Luke lower bound

## Problem

D. Karp and S. M. Sitnik, *Inequalities and monotonicity of ratios for
generalized hypergeometric function*, J. Approx. Theory 161 (2009),
337–352, DOI 10.1016/j.jat.2008.10.002, arXiv:math/0703084v2,
Conjecture 1, printed p. 14:

> Theorem 3 is true for all σ > 0 and ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0.

Theorem 3, printed p. 6, equation (23):

> For bₖ > aₖ > 0, k = 1, . . . , q, x > −1 and σ ≥ 1 the inequality
>
> $\displaystyle\frac{1}{(1+x\prod_{i=1}^q(a_i/b_i))^\sigma}<{}_{q+1}F_q(\sigma,(a_q);(b_q);-x)$
>
> holds true.

### Formal reading

Lean names below have prefix `D5.S3.Analytic.KarpSitnikLuke.Result`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Rising-factorial product ratio | `D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio` | Existing quotient of upper and lower rising-factorial products. |
| Summand of (1) | `hyperTerm` | Extra upper parameter σ, factorial denominator and power zⁿ. |
| Function inside the convergence disk | `hyper` | Real infinite sum of these summands. |
| Restricted Conjecture 1 | `claim` | All positive vectors with positive sum(b−a), σ>0, −1<x<1, positive real-power base and summability. |
| Refutation | `result` | Exactly ¬ claim. |

Restricting to the power-series disk and adding summability and positive
base assumptions gives a weaker assertion than the conjecture with analytic
continuation on x>−1. Its refutation refutes the conjecture.
For q=0 the positive-sum assumption is impossible.

## Motivation

The settling declaration is `D5/S3/Analytic/KarpSitnikLuke/Result.result`.
The source note is `D5/L/Asymptotics/karpsitnik2009luke`.
The sum condition allows one denominator parameter to be smaller than its
numerator partner. That change destroys the second-order comparison
underlying the lower bound.

## Gap

The sum-condition extension is false. The witness is
q=2, σ=1, a=(1,1), b=(1/10,2), x=1/10. Every parameter is positive,
sum(b−a)=1/10>0 and product(a/b)=5. The real-power base is 3/2>0.
The witness lies strictly inside the power-series disk, where the series
converges absolutely. The first component violates b₁>a₁, so Theorem 3
under its original componentwise assumptions is not contradicted.

## Route

At the witness the function is

$$\sum_{n=0}^{\infty}(-1)^n u_n,\qquad
u_n=\frac{n!}{(1/10)_n(n+1)}(1/10)^n.$$

Here $u_n\ge0$ and

$$\frac{u_{n+1}}{u_n}=
\frac{(n+1)^2}{10(n+1/10)(n+2)}\le\frac12.$$

The last inequality is equivalent to $4n^2+(17/2)n\ge0$.
Geometric comparison proves absolute convergence and monotonicity of the
magnitudes. The alternating-series upper bracket yields

$$ {}_3F_2(1,1,1;1/10,2;-1/10)
\le 1-\frac12+\frac2{33}=\frac{37}{66}<\frac23
=\frac1{1+(1/10)5}.$$

## Falsifier

One parameter choice satisfying every hypothesis of `claim` with a series
value below the proposed lower bound contradicts that universal assertion.
An error in the rising-factorial correspondence, summability or the
alternating-series bound would invalidate this refutation.

## Evidence

**PROVED.** `D5.S3.Analytic.KarpSitnikLuke.Result.result` states `¬ claim`
without additional hypotheses. Its private helpers prove absolute
convergence and the strict bound below 2/3 for the exact witness.

The experiments are in the immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6cf2b3329008f300a09c9a4f07eb94ee343b8786/experiments/karp-sitnik-luke-lower-bound).

- **COMPUTED.** `python3 ks-cert.py`, exit code 0; script `ks-cert.py`,
  SHA-256 `3de8121aa81b37dc242160722e20088439fbc2172d090ca5325a79b958203d70`.
  Using the uniform ratio bound |t_{n+1}/t_n| ≤ 1/2 and the alternating-series
  bracket, the exact rational partial-sum comparisons give an enclosure with both
  endpoints printed as 0.554720974172, below 2/3. The printed decimals are
  approximations; the certificate's comparisons use exact fractions.
- **COMPUTED.** `python3 ks-scan.py`, exit code 0; script `ks-scan.py`,
  SHA-256 `50b649a64f54794e1375fd91ce38d762f759f899037550fbf3f17810d8d1dcda`.
  This finite scan uses 25 decimal digits, σ in
  {0.1,0.3,0.5,0.8,1,1.5,3}, each parameter in
  {0.1,0.3,0.5,1,2,4,8}, and x in {−0.9,−0.5,0.5,2,10,100}.
  It retains positive sum(b−a), excludes the case b₁>a₁ and b₂>a₂,
  and retains positive bases and real returned values. The minimum
  relative difference (function−bound)/|bound| is approximately
  −8.10236×10⁶ at (σ,a₁,a₂,b₁,b₂,x)=(3,1,1,0.1,2,100).
  These continuation values are numerical observations outside the
  formal counterexample's disk restriction.

The supplied literature scope is the 56 citing works listed by OpenAlex
for the source DOI. Karp, arXiv:1409.3071, and Karp–Prilepkina,
arXiv:1609.02340, impose stronger structural conditions; they do not state
a settlement of this sum-condition conjecture in the supplied check.
arXiv:1410.6120 concerns different monotonicity conjectures. No settlement
was found in the supplied Formal Conjectures and conjectures.io scope.
This bounded scope does not establish exhaustive coverage or priority.

## Triage

### What the settlement shows

The second-order Taylor comparison at x=0 forces
$Q=\prod_i(a_i+1)/(b_i+1)\ge P=\prod_i a_i/b_i$.
Indeed, the proposed lower expression and the hypergeometric series have
the same constant and linear terms. Their quadratic coefficients are
$\sigma(\sigma+1)P^2/2$ and $\sigma(\sigma+1)PQ/2$, respectively.
Their difference, function minus lower expression, is
$\sigma(\sigma+1)P(Q-P)x^2/2+O(x^3)$.
For each fixed σ>0 the series is analytic near zero and the base is
positive there. If Q<P, the difference is therefore negative for all
sufficiently small positive x. Componentwise bᵢ≥aᵢ implies
$(a_i+1)/(b_i+1)\ge a_i/b_i$, so it implies Q≥P.
At this witness Q=40/33≈1.21<5=P. Thus the sum condition cannot replace
the componentwise condition for any σ>0. This Taylor argument is an
explanatory derivation; the Lean theorem certifies the single σ=1 witness.

- **PROVED.** The universal restricted assertion is false:
  `D5.S3.Analytic.KarpSitnikLuke.Result.result`. The witness shows failure
  already at σ=1, within Theorem 3's original σ range.
- **COMPUTED.** The certificate and scan have the commands, exit codes,
  hashes and tested scopes in Evidence. The approximate value near
  0.554720974172 is a numerical refinement of the formal strict bound.
- **OPEN.** The other half of Conjecture 1, 0<σ<1 with every bₖ>aₖ>0,
  is not settled here. The componentwise hypothesis avoids this particular
  second-order obstruction, which alone does not establish sufficiency.
- **OPEN.** Conjecture 2 of the same paper is not addressed. No other
  assertion depending on Conjecture 1 receives a positive conclusion from
  this counterexample. Theorem 3 retains its original parameter range.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The supplied bibliographic search is bounded; no new
network search is asserted. The scan uses numerical continuation and
finite precision; its results are not uniform inequalities over continuous
parameter regions. The Taylor explanation is not a Lean formalization
of the all-σ failure family.
