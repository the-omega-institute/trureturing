---
slug: davies-sandhu-seo-tan-2026-multivariate-occupancy-refutation
bibkey: davies2026multivariateoccupancy
doi: 10.48550/arXiv.2605.05149
url: https://arxiv.org/abs/2605.05149v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result
---

# The unrestricted multivariate hard-core occupancy bound is false

## Problem

Davies, Sandhu, Seo and Tan, arXiv:2605.05149v1, Section 1 after Theorem 1,
state:

> Strengthening the conjecture, we believe that the multivariate version should hold for any λ in the positive orthant.

> The bound in Theorem 1 is tight by the example of a disjoint union of complete graphs (such that λ is constant on each component), though we believe that the upper bound on the entries of λ can be removed.

The proposed bound is

$$
\mathbb E_{G,\lambda}|I|\geq
\sum_{v\in V(G)}\frac{\lambda_v}{1+(d_v+1)\lambda_v},
\qquad \lambda_v>0.
$$

Lee and Seo, arXiv:2602.02450v2, Section 5, write:

> Having seen the Davies–Kang conjecture, it seems plausible to look for a strengthening of Theorem 1.1 in terms of occupancy fractions.

Their inequality (5.2), at t = 1, is the same bound after multiplication
by the vertex count and identification of the sum of vertex marginals with
expected independent-set cardinality. Its nonnegative orthant contains
the strictly positive witness used here. The formal `claim` quantifies all
natural n, all simple graphs on Fin n, all adjacency-decision instances,
and every strictly positive real fugacity vector. Classical decidability
supplies such an instance for every graph. The empty graph gives 0 ≤ 0.

## Motivation

The external Tier-1 positive-orthant conjecture and this exact refutation
are preregistered in [#12413](https://github.com/the-omega-institute/trureturing/issues/12413).
The frozen declaration
`D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result`
proves `¬ claim`. It answers the unrestricted multivariate question with
the three-vertex star K_{1,2} and fugacities (15,2,2).

## Gap

The literature census in #12413 reports no settlement in the inspected
arXiv versions, follow-ups, author note, MathDB and OpenAlex records.
Those census readings are orchestrator-reported; completeness of external
literature coverage is not a kernel fact. The source passages are present
in arXiv:2605.05149v1 and arXiv:2602.02450v2. Searches by target name,
source identifiers, normalized expected cardinality and degree/fugacity
shape find no prior owner in the searched repository and pinned Mathlib
scope. No worldwide priority is claimed.

## Route

Use the existing `IndependentPartitionDeletion.configurations` and
`partition`: actual independent subsets and their product-weight sum.
`expectedSize` is their cardinality-weighted sum divided by the partition.
For the star centered at 0 in Fin 3, the independent sets are exactly
∅, {0}, {1}, {2}, {1,2}. Their weights are 1,15,2,2,4.
Thus Z = 24 and the weighted cardinality sum is 27. Degrees are (2,1,1).
All graph and fugacity data and intermediate certificates are local to
the sole theorem `result`.

## Falsifier

Proved in `result`: every witness fugacity is positive, the expectation
is 27/24 = 9/8, and the proposed lower bound is
15/46 + 2/5 + 2/5 = 259/230. Exact rational comparison contradicts the
specialized universal inequality. The shortfall is 1/920.

## Evidence

The sole public theorem is
`D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result : ¬ claim`.
Its independent-set and degree certificates use `decide`; finite
sum/product expansions and exact real arithmetic use `norm_num`.
No approximation, private axiom or additional hypothesis supplies the
contradiction. The accepted axiom closure is propext, Classical.choice
and Quot.sound. The Scribe `OpenProblemResolutionClaim` records Refuted
for this dossier. Public definitions are only `expectedSize` and `claim`.

## Triage

The unrestricted multivariate bound is refuted. The theorem's
`proof_shape` is bind-only, its `escape_witness` is none, and its
`admission_basis` is open-problem-resolution (#12413; Refuted).
Utility is certified-instance with a verified refutes edge to `claim`.
This external-problem route has no atom or coverage edge.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- Proved in this module, inside `result`: the witness has the five actual
  independent configurations, Z = 24, numerator 27 and the strict failure
  9/8 < 259/230. Its center excludes both leaves when occupied, whereas
  each leaf's proposed contribution is 2/5 independently of the center's
  fugacity. The kernel-certified obstruction is this unequal-fugacity
  star, rather than a failure of the hard-core normalization.
- Computed by the Python command below: for center fugacity L and equal
  leaf fugacity x, Z = L + (1+x)² and the numerator is L + 2x + 2x².
  As L tends to infinity, the expectation tends to 1 while the proposed
  lower bound tends to 1/3 + 2x/(1+2x). The latter exceeds 1 precisely
  when x > 1. The leaf marginals x(1+x)/Z tend to zero. This limiting
  family explains the mechanism; it is not an additional Lean theorem.
- Computed by exact rational enumeration below: among L = 1,...,39 and
  x,y = 1,...,9 there are 378 failures out of 3159 triples. Minimum
  coordinate sum is 15, attained by (12,1,2) and (12,2,1), with
  expectation 19/18 and bound 587/555. Exhausting every positive integer
  triple of coordinate sum below 15 gives 364 triples and zero failures,
  so the same minimum holds without restricting to the scan rectangle.
  Equal-leaf witness (15,2,2) is the delivered certificate, not a claim
  of smallest coordinate sum.
- Computed by symbolic rational simplification below: every simple graph
  with at most two vertices satisfies the bound. Edgeless graphs give
  equality. For K₂ with a,b > 0, expectation minus the bound equals
  (a−b)²/((1+a+b)(1+2a)(1+2b)), which is nonnegative. These statements
  are computational and elementary algebraic evidence, not additional
  kernel-checked results in this module.
- Open here: univariate Davies–Kang Conjecture A. The witness is
  nonuniform and gives no counterexample to it. The proved small-fugacity
  range of Davies et al. Theorem 1 is consistent with this witness:
  Δ = 2 requires every λ_v < 1/2, whereas the witness has entries 15,2,2.
  This is a source-theorem scope comparison, not a new Lean proof of
  Theorem 1. Lee–Seo Theorem 1.1 is a partition-function bound and is
  not refuted: the false pointwise strengthening is a sufficient route
  to that theorem, rather than its conclusion or a necessary condition.
- Open: a multivariate bound that incorporates neighboring fugacities;
  any valid range extending λ_v < 1/Δ; and a sharp admissible region of
  fugacity vectors. Neither the smallest-witness computation nor failure
  of this proposed bound settles these follow-up questions.

The computational readings above are reproducible with Python 3,
`fractions` and SymPy:

```sh
python3 - <<'PY'
from fractions import Fraction as F
import sympy as s
def gap(L, x, y):
    return F(L+x+y+2*x*y, L+(1+x)*(1+y)) - (
        F(L,1+3*L)+F(x,1+2*x)+F(y,1+2*y))
w = [(L+x+y,L,x,y) for L in range(1,40)
     for x in range(1,10) for y in range(1,10) if gap(L,x,y)<0]
m = min(t[0] for t in w)
print(3159, len(w), m, [t[1:] for t in w if t[0]==m])
small = [(L,x,y) for L in range(1,15) for x in range(1,15)
         for y in range(1,15) if L+x+y<15]
print(len(small), sum(gap(*t)<0 for t in small))
a,b,L,x = s.symbols('a b L x', positive=True)
print(s.factor((a+b)/(1+a+b)-a/(1+2*a)-b/(1+2*b)
      -(a-b)**2/((1+a+b)*(1+2*a)*(1+2*b))))
print(s.factor((a+b+2*a*b)/((1+a)*(1+b))-a/(1+a)-b/(1+b)))
print(s.limit((L+2*x+2*x*x)/(L+(1+x)**2),L,s.oo))
print(s.limit(L/(1+3*L)+2*x/(1+2*x),L,s.oo))
print(s.limit(x*(1+x)/(L+(1+x)**2),L,s.oo))
print(s.factor(s.Rational(1,3)+2*x/(1+2*x)-1))
PY
```

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal negation, not the external publication,
literature completeness, or the semantic correspondence of source prose
with the formal claim. Source interpretation and absence of a prior
external settlement remain literature-review obligations. The symbolic
and enumeration results in Triage are labeled computed and are not
additional frozen declarations. The univariate problem and weaker
multivariate bounds remain open here.
