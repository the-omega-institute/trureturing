# Signed variational interface

## Abstract

Signed orthonormal pairings and the Ky Fan variational interface.

**Definition 1.1 (Signed orthonormal witness).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness` (`✓ std3`).

*Citation.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

A finite orthonormal family together with unit signs records a signed spectral witness.

**Definition 1.2 (Signed involution predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedInvolution`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedInvolution` (`✓ std3`).

*Citation.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The predicate records symmetry, the cubic involution equation, and the prescribed finite rank.

**Theorem 1.3 (Pairing bound).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan_of_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan_of_one` (`✓ std3`). ∎

*Citation.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

When all witness signs are positive, the paired real inner product is bounded by the Ky Fan sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.SignedWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signedInvolution`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational.signed_pairing_le_kyFan_of_one`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/Defs](Defs.md)
