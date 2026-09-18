---
slug: hypercube-inequality
bibkey: averkovvondichtersoprunov2026logsubmodularity
doi: null
url: https://arxiv.org/html/2608.14909v1#S4.E16
triage: theorem
motivation_gids:
  - D5/S0/FiniteGeometry/HypercubeInequality
---

# The all-dimensional Hypercube Inequality

## Problem

Let `d>=1`, let `x_v>=0` for every vertex `v` of `{0,1}^d`, and let
`A_d` be the integer matrix whose column at `v` is `(v,1)`. For each
unordered `(d+1)`-vertex subset `S`, let `A_S` be the square submatrix of
those actual columns. Prove

```text
(sum_{|S|=d+1} |det A_S| * product_{v in S} x_v)
  * (sum_v x_v)^(d-1)
<= product_{i in Fin d}
     (sum_{v_i=0} x_v) * (sum_{v_i=1} x_v).
```

Each subset occurs once and there is no factorial factor. The formal
definitions are `augmentedCube` and `hypercubeWeight`; `result` proves the
displayed assertion for every positive natural dimension, including zero
weights, zero facets and singular determinant data.

## Motivation

Averkov, von Dichter and Soprunov state this as the Hypercube Inequality
in Section 4.4, Equation (16), after reducing a proposed geometric
log-submodularity inequality to it. Section 7.5 says that the inequality
remains open for `d>=4`. The exact external assertion was preregistered in
https://github.com/the-omega-institute/trureturing/issues/8541 before the
production proof. The registration and source citation establish the
approved open-problem target; they do not establish worldwide priority.

## Gap

The primary v1 source proves the low-dimensional case and explicitly
leaves `d>=4` open. The inspected repository and pinned Mathlib contained
determinant expansions, Schur complements, positive-semidefinite matrix
facts and volume bounds, but no theorem with the complete Equation (16)
quantifiers and coefficients. The bounded literature inspection supplied
with issue #8541 found no verified full all-dimensional settlement. This
is a finite search statement, not an exhaustive absence claim.

## Route

The canonical owner is
`D5/S0/FiniteGeometry/HypercubeInequality`, generality `G`. It contains
only the two source definitions and the theorem `result`.

The proof uses the pinned library's coefficient formula for
`det(1+X M)` and `det(1+PQ)=det(1+QP)` to derive a rectangular maximal-
minor expansion inline. Applied to the augmented cube matrix and the
diagonal weight matrix, this expresses the weighted Gram determinant as
the sum of squared integer minors. Since integer absolute determinants
are natural numbers, `|det|<=|det|^2`; nonnegative weight products then
bound `hypercubeWeight` by that Gram determinant.

When the total weight is zero, every weight vanishes and the result is
immediate. Otherwise the bottom-right scalar Gram block is positive. The
scaled Schur complement
`C=s*(Q-b*D^-1*b^*)` is positive semidefinite, and its `i`th diagonal is
exactly `(sum_{v_i=0} x_v)*(sum_{v_i=1} x_v)`. A positive-semidefinite
factorization and `Orientation.abs_volumeForm_apply_le` give
`det C<=product_i C_ii`. The block determinant and scalar determinant laws
give `det C=s^(d-1)*det M`, completing the inequality without assuming
that the full Gram matrix or any facet sum is positive.

## Falsifier

A positive dimension and a nonnegative cube weighting for which the
determinant-defined left side exceeds the paired-facet product would
refute the theorem. A purported counterexample must use unordered subsets
exactly once, absolute determinants of the augmented integer columns and
the exponent `d-1`; ordered tuples, Euclidean volume with an unaccounted
factorial, or a different facet multiplicity address a different claim.
A prior published proof would change open-problem eligibility and priority,
not the truth of the kernel-checked statement.

## Evidence

The primary HTML at arXiv:2608.14909v1 was read at Equation (16) and
Section 7.5; its locally supplied 2026-08-14 version has SHA-256
`b439f4eab795c6e2091720f5a2025616231035b9eaffa0c9d5158b8228fd8d4f`.
The source gives the exact title and authors Gennadiy Averkov, Katherina
von Dichter and Ivan Soprunov; it displays no DOI.

The canonical Lean report binds source SHA-256
`dc2c88800ba1f2ac338e5a5fb17d2e5fff3556ce31aca7951a6ee2ae3249df85`
and the public declarations `augmentedCube`, `hypercubeWeight` and
`result`. The result's axiom closure is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `admit`, private
axiom or native-decision premise. The first freeze has module statement ID
`sha256:0297ecc26c752dcd3b6bac346609f1840d066afb512f3f85e058b1d6994973d6`.

## Triage

First tier: a fixed recent source-labelled open problem, preregistered in
issue #8541. `admission_basis: open-problem-resolution`;
`question_answered: Equation (16) for every d>=1 and every nonnegative
weighting`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `augmentedCube` | N/A (definition) | none | open-problem-resolution |
| `hypercubeWeight` | N/A (definition) | none | open-problem-resolution |
| `result` | bind-only | none | open-problem-resolution |

After inlining the local lets and haves, the maximal-minor expansion
instantiates `Matrix.det_one_add_mul_comm` and
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors`, then reindexes and
normalizes determinants. The integer-minor bound uses `Nat.le_mul_self`;
the Gram and Schur bounds instantiate the pinned PSD diagonal, congruence
and `Matrix.PosDef.fromBlocks₂₂` results. The determinant bound uses
`CStarAlgebra.nonneg_iff_eq_star_mul_self` and
`Orientation.abs_volumeForm_apply_le`; the block determinant and facet
identities finish by library rewrites, finite sums and algebraic
normalization. No live intermediate step escapes these permitted binding
and normalization operations. The external Equation (16) remains admitted
under `open-problem-resolution` through preregistration in issue #8541,
not through an escape witness. The result is uniform in the dimension and
is not bounded enumeration, a checker, numeric reduction or a certified
finite instance. Thus `utility: none`; all computational-use fields are
not applicable. The ordered dominating-theorem search covered repository
D5, pinned Mathlib and the external Lean ecosystem scope recorded by the
preregistration; no exact dominating theorem was found in that scope.

## ASSUMED-UNVERIFIED

The literature finding is bounded to the inspected sources and does not
claim exhaustive global novelty, priority or absence of an independent
proof. The formal theorem is the determinant polynomial Equation (16).
The source's normalized-volume interpretation is cited, but the geometric
reduction to the broader zonoid log-submodularity conjecture is not
formalized here; no full zonoid-volume theorem is claimed. The `d=0` case,
equality classification and the paper's broader geometric conjecture are
outside this result.
