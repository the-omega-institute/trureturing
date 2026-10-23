---
bibkey: mathlib2026compactspectral
authors: Mathlib contributors
year: 2026
title: Compact self-adjoint spectral theorem and full Hilbert bases
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean
claim: A compact symmetric operator on an arbitrary complete complex Hilbert space has eigenspaces with trivial common orthogonal complement, including the zero eigenspace.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/Spectral
license: Apache-2.0
triage: anchor
---

# Full compact spectral representation

## Verified locator

The pinned compact spectral theorem is
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Spectrum.lean
at `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`.
The same source supplies `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`
and `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`.

The compatible Hilbert-basis constructors are in
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/l2Space.lean
at `exists_hilbertBasis`, `HilbertBasis.mkOfOrthogonalEqBot`, and
`HilbertBasis.hasSum_repr`.

## Composition and analytic attribution

The repository chooses a Hilbert basis in every closed complex eigenspace,
combines them using Mathlib's orthogonal sigma-family theorem, and proves
completeness using the compact spectral theorem. The zero eigenspace remains
in the full basis, including for zero and finite-rank operators on a
nonseparable space. This is a formal composition of standard spectral theory,
with no mathematical originality claim.

`TraceClass/Compact.isCompactOperator_of_nonneg_isTraceClass` supplies
compactness from the actual trace-class predicate. The analytic diagonal
summability and positive trace-basis identity are the attributed Physlib
suppliers described in `Library/QuantumBounds/diem2026traceclass.md`.
No supplier proof is copied or reproved in the spectral module.

The resulting real eigenvalues are summable before their sum is identified
with the real trace. Their complex casts sum to the actual complex trace.
Applying the original continuous operator to its genuine Hilbert-basis
expansion proves convergence of the weighted vector series to that operator's
value, rather than merely defining a separate diagonal operator.

For a faithful normalized positive trace-class operator, a zero eigenvalue
would place a nonzero basis vector in its trivial kernel. Strict positivity
and genuine summability therefore make the full index countable. A finite
index is transported bijectively to `Fin n`; an infinite index is transported
bijectively to `Nat`. No uniform spectral gap or zero-vector padding is used.
A general nonfaithful trace-one operator has no such full-index countability
conclusion. These results supply spectral data only; no entropy, logarithmic
energy, heat-trace or unbounded Hamiltonian theorem is asserted.
