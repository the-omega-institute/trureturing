# Normalization and reconstruction on the actual support of the pair

## Abstract

Normalization and reconstruction on the actual support of the pair

The generalized inverse square root is used only through its support identities. No inverse of A, B or A+B is assumed. These repository proofs implement common-support localization and trace transport.

**Definition 1.1 (normalize).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalize`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

normalize S X is invSqrt(S) X invSqrt(S), using the repository generalized inverse square root. OriginalPair takes S=A+B and C=normalize S A.

**Definition 1.2 (reconstruct).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

reconstruct S Y is sqrt(S) Y sqrt(S). It sends normalized feasible overlaps and positive spectral components back to the original matrix pair.

**Theorem 1.3 (pair supported).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.pair_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.pair_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and P=spectralSupport(A+B), PA=AP=A and PB=BP=B. normalized_pair and reconstruction use all four support identities.

**Theorem 1.4 (normalized pair).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalized_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalized_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B, both normalized matrices are PSD and sum to spectralSupport(A+B). The original-pair proof derives its normalized contraction and complementary upper bound from this identity.

**Theorem 1.5 (reconstruct normalize).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD S and any X supported by spectralSupport(S) on both sides, reconstruct S (normalize S X)=X. The overlap bijection consumes this recovery statement.

**Theorem 1.6 (overlap bijection).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.overlap_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.overlap_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and every real t, normalization sends each positive overlap of A,tB to an overlap of the two normalized upper bounds and reconstructs it exactly. Conversely reconstruction sends each normalized overlap to an original feasible overlap and normalization recovers it. OriginalPair uses this actual two-way feasible transport.

**Theorem 1.7 (reconstruction trace).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruction_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruction_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD S and arbitrary Y, Tr(reconstruct S Y)=Tr(SY), by cyclic trace. Weighted normalized optimization and the canonical spectral test consume this exact objective transport.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalize`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.normalized_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.overlap_bijection`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.pair_supported`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruct_normalize`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSupport.reconstruction_trace`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap](MaximalHockeyStickOverlap.md)
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransformer](../Lieb/SupportPerspectiveTransformer.md)
