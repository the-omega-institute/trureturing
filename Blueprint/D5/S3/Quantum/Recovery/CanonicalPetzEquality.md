# Supported entropy equality exactly characterizes fixed Petz recovery

## Abstract

Supported entropy equality exactly characterizes fixed Petz recovery.

**Theorem 1.1 (Actual entropy equality controls modular functions).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.equality_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalPetzEquality.equality_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Equality of the supported canonical finite relative entropy for the actual channel model gives f(A) xi = V f(B) eta for every real f. The model is constructed from the same actual channel and states; it is not an arbitrary abstract witness supplied as the conclusion.

**Theorem 1.2 (Actual inverse-square-root recovery coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.inverse_sqrt_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalPetzEquality.inverse_sqrt_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Apply the functional intertwining to the inverse square root on the positive relative modular spectrum. The resulting coordinates give the input support columns of the actual adjoint recovery core.

**Theorem 1.3 (One fixed channel, then all supported input states).**

Lean statement: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For arbitrary finite decidable nonempty input and output carriers, every bundled quantum channel Phi and density sigma admit one completed Petz recovery channel. The statement first fixes its full-matrix action and proves recovery of sigma, then quantifies over every rho with ker sigma contained in ker rho. For every such rho, equality of finite trace-log relative entropy before and after Phi is equivalent to recovery of rho by that same channel. All inverse square roots are spectral pseudoinverses; no full-rank, commutativity, or dimension-specific assumption is imposed. The unsupported infinite-entropy branch is outside this equivalence: infinity=infinity is not a recovery criterion. The forward implication consumes log rigidity, spectral support reconstruction, Schwarz and equal-trace positive-order rigidity; the converse consumes the existing DPI twice. This is a formalization of the classical Petz sufficiency theorem, not a claim of literature novelty. See Hiai-Mosonyi-Petz-Beny, Quantum f-divergences and error correction, arXiv:1008.2529, equation (3.2), Lemma 3.2 and Theorem 5.1, with the full-space CPTP completion following that theorem.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.equality_intertwining`
- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.inverse_sqrt_coordinates`
- Truth anchor: `D5/S3/Quantum/Recovery/CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Divergence/LogEqualityResolventRigidity](../Divergence/LogEqualityResolventRigidity.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSchwarzRecovery](PetzSchwarzRecovery.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](PetzSpectralCoordinates.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
