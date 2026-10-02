---
slug: bertuzzo-2026-simplex-coverage-optimality
bibkey: bertuzzo2026coveragedepth
doi: 10.48550/arXiv.2603.06489
url: https://arxiv.org/html/2603.06489v1
triage: theorem
motivation_gids:
  - D5/S3/Resource/SimplexCoverageOptimality.result
---

# The original simplex coverage optimizer

## Problem

Bertuzzo–Ravagnani–Yaakobi, arXiv:2603.06489v1, Section 3,
Conjecture 3.2, asks whether the q-ary simplex code solves Problem B.
The predecessor is arXiv:2507.20639v1, Section III, its unnumbered
simplex-optimizer paragraph. Issue
https://github.com/the-omega-institute/trureturing/issues/11799
preregisters the complete assertion before its mathematical probes.

For every finite field K of cardinality q and every k at least two,
set n=(q^k-1)/(q-1). For every rank-k k-by-n physical generator G
and every actual simplex generator S with exactly one nonzero
representative of each projective line, prove E[T_S] <= E[T_G].
T is the original minimum time at which the sampled columns span K^k;
each physical Fin n position is drawn independently, uniformly and
with replacement. Zero, repeated and scalar-parallel competitor
positions remain in the alphabet without conditioning or renormalization.

## Motivation

This decides the source's complete optimizer assertion at the simplex
parameters. A nonzero-only or projective-only comparison, a restricted
field or dimension, a rank-deficient expectation, a changed sampling
law or a known closed-form expectation does not decide it. No uniqueness
claim is required or asserted.

## Gap

The missing assertion is the universal comparison with arbitrary
full-rank physical generators at the exact simplex length. Computing
the simplex expectation alone does not supply this comparison. The
formal result below addresses the complete assertion without removing
zero columns from the original sampling alphabet.

## Route

The source's Theorem 3.1 already computes the simplex expectation.
That formula is context, not an independent new result. Frozen
repository interfaces provide the represented root concavity, exact
spanning word normalization, actual uniform recovery probabilities,
and actual stopping-time/expectation bridge. Pinned Mathlib provides
projective cardinality, linear-group action and pretransitivity, finite
Jensen and measure/order interfaces. Routine orbit and physical fiber
deductions are local steps, not retained standalone results.

Only zero competitor columns are replaced, on the same positions and
sample space. Span containment preserves rank and dominates original
recovery at every horizon. Local orbit averaging and physical fiber
transport compare replacement recovery with uniform projective recovery.
The simplex's actual physical alphabet bijection identifies that law,
and its representatives are proved to span the ambient space. Measurable
complements and the actual tail bridge compare ENNReal sums first, using
original finiteness before `toReal` and both real-integral conversions.

## Falsifier

The claimed resolution would fail if its public type excluded a finite
field, a dimension at least two, or an admissible full-rank competitor;
if simplex generators at the exact length did not exist; if physical
multiplicities or zero positions were discarded from the original iid
law; or if the final real integrals were not the original first-full-span
expectations. A finite admissible generator with strictly smaller actual
expectation than its simplex competitor would refute the assertion.

## Evidence

The sole handle is
`D5/S3/Resource/SimplexCoverageOptimality.result`. Its public type
uses actual matrices, exact length n and the rank-k premise. Its simplex
ray map is bijective, expressing exactly one nonzero representative per
line on physical Fin n positions. The sampling carrier's nonempty
instance is derived, not an extra assumption. Its conclusion is the real
integral inequality for the existing `retrievalTime` and `uniformSamples`.

The full theorem is kernel-checked with the standard three axioms only.
Its `proof_shape` is `bind-only`; its `admission_basis` is
`open-problem-resolution` for #11799. No escape-witness claim,
additional public or private theorem wrapper, or intermediate settlement
is attached to it.

Transient exact controls check the original type and sampling law,
simplex existence at the stated length over every finite field, and
application to a rank-two three-column generator over ZMod 2 containing
a zero physical column. These checks are evidence, not additional
retained mathematical declarations or independent settlements.

## Triage

Bounded readings of the primary and predecessor arXiv version histories
retain the full assertion. The related papers arXiv:2608.20152v1,
2609.36067v1 and 2507.20645v1 concern formulas, restricted systematic
generators, or singleton and partial recovery. Section VI of
arXiv:2601.07053v2 also treats full recovery: Theorems 4 and 5 and
Corollary 6 give bounds and asymptotics, rather than the exact universal
simplex optimizer. The checked texts do not supply a dominating full resolution. This
result concerns complete recovery at the exact simplex parameters;
it asserts neither uniqueness nor a new closed-form expectation.

## ASSUMED-UNVERIFIED

The supplier search and exact versioned source readings are bounded
evidence. Unindexed work and inaccessible final publisher texts remain
unverified; no exhaustive global novelty or priority certificate is
claimed. Kernel verification establishes the stated mathematical
inequality. Canonical admission, freezing, coverage and merged delivery
are separate machine and repository facts, not consequences of the
theorem alone. No manual closure or erasure of unrelated residual atoms
is asserted.
