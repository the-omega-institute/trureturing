# Signed variational interface

## Abstract

Signed orthonormal pairings and the Ky Fan variational interface.

**Definition 1.1 (Signed orthonormal witness).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

A finite orthonormal family together with unit signs records a signed spectral witness.

**Definition 1.2 (Signed quadratic pairing).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedPairing`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedPairing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The pairing sums the signed quadratic forms of the matrix on the orthonormal family.

**Theorem 1.3 (Pairing bound).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

A signed orthonormal family gives a pairing bounded by the Ky Fan sum.

**Theorem 1.4 (Attainment by signed eigenvectors).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.exists_signed_pairing_eq_kyFan`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.exists_signed_pairing_eq_kyFan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

For a real symmetric matrix and a prefix no larger than its dimension, sorting an orthonormal eigenbasis by absolute eigenvalue and choosing its signs attains the Ky Fan sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.exists_signed_pairing_eq_kyFan`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedPairing`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/Defs](Defs.md)
