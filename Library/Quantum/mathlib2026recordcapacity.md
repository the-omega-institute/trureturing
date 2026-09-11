---
bibkey: mathlib2026recordcapacity
authors: Junyan Xu and the mathlib community
year: 2026
title: Wedderburn–Artin structure and trace of idempotent endomorphisms
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean
claim: Finite-dimensional semisimple complex algebras are products of full matrix algebras; the associated record-count bounds follow by applying the trace-rank identity to their faithful actions.
strata_touched:
  - D5/S3/Quantum/Matrix/RecordCapacity
license: Apache-2.0
triage: anchor
---

# Algebraic record capacity

## Verified locator

The exact upstream locator is:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean

The pinned source was opened through GitHub's raw endpoint successfully.
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` supplies the
matrix-block decomposition. In the same pinned tree,
`Mathlib/LinearAlgebra/Trace.lean`, also opened through the raw endpoint,
contains `LinearMap.IsProj.trace` and `IsIdempotentElem.trace_eq_zero_iff`.
The first identifies the trace of an idempotent with the dimension of its range;
the second detects a zero idempotent by its trace in characteristic zero.

The capacity argument combines these results with trace additivity and the faithful
block diagonal action. The source supplies structure and trace identities, rather than
the complete record-count statement. The D5 theorem keeps the common action and
equivariance explicit. It also supplies a dimension bound without semisimplicity.
The relation between a separately specified irrep decomposition and these block sizes
is outside the delivered formalization.
