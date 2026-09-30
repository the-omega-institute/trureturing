---
slug: debrota-2020-rank-one-mic-seven-orthogonal-pairs-refutation
bibkey: debrota2020varieties
doi: 10.1142/S0219749920400055
url: https://arxiv.org/abs/1812.08762v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result
---

# A rank-one qutrit MIC with nine orthogonal pairs

## Problem

J. B. DeBrota, C. A. Fuchs and B. C. Stacey, “The Varieties of Minimal
Tomographically Complete Measurements”, arXiv:1812.08762v5 (quant-ph),
Conjecture 1 on printed page 6 states:

> A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements.

A MIC is a POVM of exactly d² positive semidefinite effects summing to the
identity whose real span is the Hermitian operators. Orthogonality is
`tr(E_a E_b) = 0`; distinct unordered pairs are counted once. Issue #11474
preregisters the literal reading for d = 3 before Lean implementation.
The conjecture imposes no unbiasedness condition, although its preceding
seven-pair example is explicitly called unbiased.

## Motivation

The zero entries of a MIC Gram matrix constrain the geometry of minimal
quantum measurements. The frozen declaration
`D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result` negates
the universally quantified seven-pair bound using a rank-one qutrit MIC.

## Gap

The literature check recorded in #11474 found no settlement in the searched
scope. The citing-work scan is reported by a codex-cli search seat; the
source-version and MathDB checks are reported by the Claude Code orchestrator in that issue.
These are attributed readings, not an exhaustive literature or priority claim.
The different orthocross inverse-Gram conjecture is settled by
`OrthocrossGramHalfInteger.result`; it does not imply this pair-count bound.

## Route

For indices 0 through 8 let

```
v = [(1,i,-1), (1,-1,1+i), (1-i,0,-1), (1,-1+i,1+i),
     (0,1,i), (-1-i,i,1), (1,1,1), (1,i,-1-i), (1,-i,0)]
k = [3,2,2,4,3,3,9,7,11]
E_a = (k_a/46) v_a v_a†.
```

Positive scaling of an outer product gives positive semidefiniteness and
rank at most one; a nonzero diagonal entry proves rank at least one.
Entrywise complex arithmetic proves `Σ E_a = I`. Write x for the nine real
Hermitian coordinates `(H00,H11,H22,Re H01,Im H01,Re H02,Im H02,Re H12,Im H12)`.
The Lean source provides an integer matrix J such that the real coefficients
`c_a = (Jx)_a/k_a` reconstruct every Hermitian H as `Σ c_a E_a`.
The nine pairs `(0,1),(0,8),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8)`
have zero trace product, giving at least nine distinct unordered pairs.

## Falsifier

A failed positivity, rank, identity-sum, real-spanning or trace-zero check
would invalidate this counterexample. Using only real parts of traces or
counting both orders of a pair would change the claim. The formal definition
uses full complex trace equality and increasing pairs `a < b`.

## Evidence

The canonical Lean module has public definitions `IsRankOneMIC`,
`orthogonalPairs`, `claim`, and the sole theorem `result : ¬ claim`.
Its proof constructs all five MIC conjuncts, the nine-pair subset, its
cardinality nine, and the contradiction with seven. This establishes a
lower bound of nine; the formal result does not assert an exact pair count.

The effect traces are `9/46,4/23,3/23,10/23,3/23,6/23,27/46,14/23,11/23`,
so the counterexample is biased. A separate numerical search reports
candidate unbiased configurations;
these have no exact certificate or Lean proof and do not settle a conjecture
restricted to unbiased MICs.

## Triage

Tier 1 published quant-ph conjecture, preregistered in #11474.
The Scribe theorem node records `Refuted`. The theorem is classified
`proof_shape: bind-only`: finite reconstruction and arithmetic use pinned
Mathlib positivity and rank bounds, with no independent escape witness.
Admission uses `open-problem-resolution`; utility is `certified-instance`
with basis `refutes` the formal `claim`.

## ASSUMED-UNVERIFIED

The Preston thesis and Gaussian-noise citing paper recorded as inaccessible
in #11474 remain unverified. The bounded literature check establishes no
exhaustive novelty or priority. Numerical unbiased candidates are uncertified.
The Lean kernel checks the stated predicate and proof, not the authenticity
or version history of the external paper. Template registration of this
refutation is unfinished: the enrolled CounterexampleRecord witness interface
needs separate actual-witness, variation and sensitivity evidence; this
module exposes only the closed refutation and keeps its concrete witness private.
