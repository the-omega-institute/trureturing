---
slug: karp-sitnik-2009-luke-upper-bound
bibkey: karpsitnik2009luke
doi: 10.1016/j.jat.2008.10.002
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KarpSitnikLuke/UpperResult.result
url: https://arxiv.org/abs/math/0703084
---

# Refutation of the sum-condition Luke upper bound

## Problem

D. Karp and S. M. Sitnik, *Inequalities and monotonicity of ratios for
generalized hypergeometric function*, J. Approx. Theory 161 (2009),
337–352, DOI 10.1016/j.jat.2008.10.002, arXiv:math/0703084v2,
Conjecture 2, printed p. 14, equation (38):

> For 0 < σ ≤ min(a₁, a₂, . . . , a_q), ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0 and x > 0:
>
> $\displaystyle {}_{q+1}F_q(\sigma,(a_q);(b_q);-x)<\frac{1}{\left[1+x\prod_{i=1}^q\frac{\Gamma(a_i)\Gamma(b_i-\sigma)}{\Gamma(b_i)\Gamma(a_i-\sigma)}\right]^\sigma}.\qquad (38)$

The preceding sentence reads:

> The asymptotic formula (16) and numerical experiments suggest the following

Formula (16), printed p. 5, is preceded by:

> It follows that for σ < min(a₁, a₂, . . . , a_q) we will have

$$ {}_{q+1}F_q(\sigma,(a_q);(b_q);-z)
=\frac{\prod_i\Gamma(a_i-\sigma)\Gamma(b_i)}
{\prod_i\Gamma(a_i)\Gamma(b_i-\sigma)}z^{-\sigma}
+o(z^{-\sigma}),\qquad z\to\infty. $$

The quotation transcribes the extracted display, which places a $\sigma$
next to the Gamma product. Write
$K=\prod_{i=1}^q\Gamma(a_i)\Gamma(b_i-\sigma)/(\Gamma(b_i)\Gamma(a_i-\sigma))$.
Separately, the asymptotically precise reading via (16) is
$1/(1+xK^{1/\sigma})^\sigma$: the inner exponent $1/\sigma$
makes its leading asymptotic coefficient agree with (16).
The counterexample has $\sigma=1$, where both readings coincide.

### Formal reading

Lean names below have prefix `D5.S3.Analytic.KarpSitnikLuke.UpperResult`,
except where their frozen owner is specified.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Rising-factorial ratio | `D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio` | Quotient of the products for a and b. |
| Summand of (1) | `D5.S3.Analytic.KarpSitnikLuke.Result.hyperTerm` | Extra upper parameter σ, factorial denominator and zⁿ. |
| Series value | `D5.S3.Analytic.KarpSitnikLuke.Result.hyper` | Real infinite sum of these summands. |
| Gamma product in (38) | `gammaProduct` | Exactly K defined above, with finite index type Fin q. |
| Restricted Conjecture 2 | `claim` | Positive parameters, positive sum(b−a), 0<σ≤aᵢ, 0<x<1, summability, K>0 and the strict upper bound. |
| Refutation | `result` | Exactly ¬ claim. |

Each additional condition weakens the universal assertion: $x<1$
restricts to the power-series disk, summability restricts to convergent
series, and $K>0$ restricts the parameter set. The latter, with $x>0$,
makes the real-power base positive. Refuting the weaker assertion
refutes the conjecture. The $q=0$ positive-sum assumption is impossible.

## Motivation

The settling declaration is `D5/S3/Analytic/KarpSitnikLuke/UpperResult.result`.
The source note is `D5/L/Asymptotics/karpsitnik2009luke`.
The sum condition permits an individual denominator parameter smaller
than its numerator partner, destroying the first-order comparison
required by the upper expression.

## Gap

The sum-condition upper assertion is false. Its witness is
$q=2$, $\sigma=1$, $a=(2,2)$, $b=(3/2,3)$, $x=1/2$.
All entries are positive, $\sum_i(b_i-a_i)=1/2>0$,
$0<\sigma\le a_i$, and $0<x<1$.
The Gamma product is $K=1>0$. The proposed upper expression is $2/3$,
and the convergent hypergeometric series exceeds $2/3$.
The first denominator parameter is smaller than the corresponding
numerator parameter; the componentwise case is not contradicted.

## Route

At the witness the defining series is

$$\sum_{n=0}^{\infty}(-1)^n u_n,\qquad
u_n=\frac{(2)_n^2}{(3/2)_n(3)_n}\left(\frac12\right)^n.$$

The magnitudes are nonnegative and

$$u_{n+1}=\frac{(n+2)^2}{2(n+3/2)(n+3)}u_n\le\frac12u_n.$$

The inequality follows from
$(n+3/2)(n+3)-(n+2)^2=(n+1)/2\ge0$.
Geometric comparison gives summability and monotonicity. The six-term
alternating lower bracket gives

$$\frac23<1-\frac49+\frac15-\frac{16}{175}+\frac8{189}-\frac{32}{1617}
=\frac{249826}{363825}
\le{}_3F_2(1,2,2;3/2,3;-1/2).$$

The Gamma recurrence $\Gamma(t+1)=t\Gamma(t)$ and positivity of
$\Gamma(1/2)$ give $\Gamma(2)=1$, $\Gamma(3)=2$ and
$\Gamma(3/2)=\Gamma(1/2)/2$. Hence the two factors in $K$ are
$2$ and $1/2$, giving $K=1$ and the upper expression $2/3$.

## Falsifier

A single parameter choice satisfying all hypotheses of `claim` with
the function above its proposed upper bound contradicts that universal
assertion. An error in the Gamma evaluation, summand identity,
summability or alternating-series enclosure would invalidate this refutation.

## Evidence

**PROVED.** `D5.S3.Analytic.KarpSitnikLuke.UpperResult.result` states `¬ claim`
without additional hypotheses. The private helpers `witness_gamma`,
`witness_summable` and `witness_lower` establish K=1, convergence and the
strict comparison with 2/3 at the exact witness.

**COMPUTED.** The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ba0a5ed33f26b244ab9ec9d6775617cbef8b0a96/experiments/karp-sitnik-luke-lower-bound)
contains `ks2-upper-cert.py`. Command `python3 ks2-upper-cert.py`, exit
code 0; SHA-256
`c5126bff3504c30dc22f27626d62e430135922a7c04f3cfd9b40c98523c063d2`.
The exact rational enclosure uses 40 successive-term checks and the
alternating bracket with the uniform ratio bound. Both printed endpoints
are 0.692994117069, above the bound 2/3. The decimal endpoints are
approximations; the comparisons use exact fractions.

The supplied literature scope is the 56 citing works listed by OpenAlex
for the source DOI. Karp, arXiv:1409.3071, and Karp–Prilepkina,
arXiv:1609.02340, impose stronger structural conditions and do not state
a settlement of Conjecture 2 in that bounded check. No settlement was
found in the supplied Formal Conjectures and conjectures.io scope.
These supplied readings do not establish exhaustive coverage or priority.

**COMPUTED.** The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ba0a5ed33f26b244ab9ec9d6775617cbef8b0a96/experiments/karp-sitnik-luke-lower-bound)
contains `ks2-upper-scan.py`. Command `python3 ks2-upper-scan.py`, exit
code 0; SHA-256
`014a74b262865cd087356a336ea9d9c143f53df1c8db534fee0acc39a0d876f6`.
With mpmath `mp.dps = 30`, $a=(1,1)$, $b=(1/10,2)$,
$\sigma\in\{0.01,0.05,0.09\}$ and
$x\in\{0.01,0.1,0.5,2,10,1000\}$, all 18 output lines report
`F<bound False`. These are finite numerical observations of the
hypergeometric function and the proposed upper expression, not a
continuous-interval inequality or a Lean result.

## Triage

### What the settlement shows

The first-order Taylor comparison at $x=0$ forces
$P=\prod_i a_i/b_i\ge K^{1/\sigma}$.
The function has expansion $1-\sigma Px+O(x^2)$, whereas the proposed
upper expression has expansion $1-\sigma K^{1/\sigma}x+O(x^2)$.
Thus their difference, function minus upper expression, is
$\sigma(K^{1/\sigma}-P)x+O(x^2)$.
If $P<K^{1/\sigma}$, positivity of this coefficient violates the upper
bound for every sufficiently small positive $x$.
At $\sigma=1$ with all $a_i,b_i>1$, the Gamma recurrence gives
$K=\prod_i(a_i-1)/(b_i-1)$.
Componentwise $b_i\ge a_i>1$ implies
$a_i/b_i\ge(a_i-1)/(b_i-1)$, because the difference has numerator
$b_i-a_i\ge0$ and positive denominator $b_i(b_i-1)$.
For the witness $P=8/9<1=K$. This is an explanatory Taylor derivation;
the Lean theorem proves the exact $\sigma=1$, $x=1/2$ counterexample.

- **PROVED.** `D5.S3.Analytic.KarpSitnikLuke.UpperResult.result` refutes
  the universal restricted upper assertion. Its counterexample meets
  $0<\sigma\le\min a_i$ and has positive Gamma product.
- **COMPUTED.** The exact certificate above refines the strict formal
  lower bound to approximately 0.692994117069.
- **COMPUTED.** The numerical scan
  [`ks2-upper-scan.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/ba0a5ed33f26b244ab9ec9d6775617cbef8b0a96/experiments/karp-sitnik-luke-lower-bound/ks2-upper-scan.py),
  command `python3 ks2-upper-scan.py`, exit code 0, SHA-256
  `014a74b262865cd087356a336ea9d9c143f53df1c8db534fee0acc39a0d876f6`,
  uses mpmath `mp.dps = 30`, $a=(1,1)$, $b=(1/10,2)$,
  $\sigma\in\{0.01,0.05,0.09\}$ and
  $x\in\{0.01,0.1,0.5,2,10,1000\}$.
  All 18 lines report `F<bound False`. This is numerical evidence only;
  it proves neither an inequality over a continuous interval nor a Lean result.
- **OPEN.** The componentwise case $b_k>a_k>0$ with
  $0<\sigma\le\min a_i$ is not settled. Avoiding the first-order
  obstruction does not prove the upper inequality.
- **OPEN.** Conjecture 1's remaining componentwise $0<\sigma<1$ case is
  not settled by this result. The frozen sibling's sum-condition lower
  counterexample remains a separate result. No positive conclusion for
  other source results follows from this refutation.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified; no new network search is asserted. The asymptotic
motivation uses continuation, whereas the formal witness is strictly
inside the power-series disk. The Taylor explanation is not a Lean
formalization of a parameter family. Finite numerical continuation
values do not establish uniform inequalities on continuous intervals.
