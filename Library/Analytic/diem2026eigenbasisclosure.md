---
bibkey: diem2026eigenbasisclosure
authors: Tom Ole Diem; Adam Bornemann; Gregory J. Loges
year: 2026
title: Self-adjoint closure from a real Hilbert eigenbasis
doi: null
url: https://github.com/HEPLean/PhysLean/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean
claim: A real Hilbert eigenbasis gives a closable finite-span operator with self-adjoint closure.
strata_touched:
  - D5/S3/Quantum/Analysis/EigenbasisClosure
license: Apache-2.0
triage: anchor
---

# Real eigenbasis closure

## Verified locator

https://github.com/HEPLean/PhysLean/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean

Tom Ole Diem, HEPLean/PhysLean, revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`,
`PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean`,
`isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors`.
The supporting polarization, adjoint-order, closure-symmetry and range
arguments are from Adam Bornemann and Gregory J. Loges,
`Physlib/QuantumMechanics/Operators/Unbounded.lean` at the same revision.
The full Apache-2.0 license is in
`docs/reports/oscillator-suppliers/physlib-LICENSE.txt`.
The authenticated donor tree has no NOTICE-named file.

The selected original proof constructs resolvent coefficients at plus and
minus the imaginary unit, with simultaneous finite-sum limits in both graph
coordinates. It allows zero and repeated real eigenvalues and an arbitrary
basis index type. The supporting arguments are local in one theorem.
The original copyright and grant headers are retained verbatim.
No originality is claimed for this construction.
