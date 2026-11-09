---
bibkey: suzuki2025topologicalschur
authors: Keisuke Suzuki
year: 2025
title: Selfadjoint Schur lemma for topologically irreducible bounded operators
doi: null
url: https://github.com/kencyke/quantum-system/blob/5d67fe8030eaf1bdaf081e2acfcbe3fbaecfda7c/QuantumSystem/ForMathlib/Analysis/InnerProductSpace/InvariantSubspace.lean
claim: A bounded selfadjoint operator commuting with a topologically irreducible operator set on a complete complex Hilbert space is a real scalar; irreducibility quantifies closed invariant subspaces.
strata_touched:
  - D5/S3/Quantum/Algebra/TopologicalSchur
  - D5/S3/Quantum/Algebra/AnticommutingInvariantPlane
license: Apache-2.0
triage: anchor
---

# Topological selfadjoint Schur

## Verified locator

https://github.com/kencyke/quantum-system/blob/5d67fe8030eaf1bdaf081e2acfcbe3fbaecfda7c/QuantumSystem/ForMathlib/Analysis/InnerProductSpace/InvariantSubspace.lean

The immutable source has SHA256
`96a1bbcca39cff497d9f703db546646663f72b7b3fc330d37ba7713c56bfdec4`.
Its toolchain is Lean 4.35.0 and its mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The source repository has an Apache-2.0 LICENSE and no root NOTICE file.
The copyright and full license accompany the transplanted source.

`InnerProductSpace.IsTopologicallyIrreducible` quantifies closed complex-linear
subspaces. `exists_eq_algebraMap_of_isSelfAdjoint_of_commute` uses the continuous
functional calculus to prove scalarity without an ambient finite-dimensional
hypothesis. The transplant retains those declarations and the kernel-invariance
lemma used by the proof. It can be retired when the pinned mathlib contains an
equivalent closed-subspace selfadjoint Schur theorem.

For an anticommuting represented triple, the selfadjoint product i A B C
commutes with its closed generated algebra. This supplies the scalar product
formula for the third operator. The construction of an actual orthonormal
invariant plane and its coordinate map is separate from this upstream theorem.
