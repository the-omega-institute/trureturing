# Common-support compression without invertibility assumptions

## Abstract

Common-support compression without invertibility assumptions

All coordinate and spectral corners are allowed to be empty. These source-owned geometry results implement the common-support localization antecedent credited to GGJ, without importing a general-convex classifier from that literature.

**Definition 1.1 (inclusion).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

inclusion p is the rectangular coordinate inclusion from the subtype satisfying p into the ambient finite index type. CornerOptimization uses it to extend compressed feasible matrices.

**Theorem 1.2 (inclusion isometry).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

The adjoint of inclusion p times inclusion p is the identity on the subtype, also for an empty subtype. Compression and extension consume this isometry.

**Theorem 1.3 (inclusion projection).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

inclusion p times its adjoint is the ambient diagonal indicator of p. This identifies the support projection used to reconstruct a supported matrix.

**Theorem 1.4 (inclusion compress).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_compress`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_compress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Adjoint-inclusion times X times inclusion is exactly the subtype submatrix of X. CornerOptimization consumes this identification for feasibility and trace transport.

**Theorem 1.5 (compress le).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.compress_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.compress_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Loewner inequalities between ambient matrices remain valid on the subtype submatrices. No positivity of each matrix is separately assumed. Optimization reduction uses this order preservation.

**Theorem 1.6 (extend le).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.extend_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.extend_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Loewner inequalities between subtype matrices remain valid after extension by inclusion and its adjoint. Optimization reduction uses this to construct ambient feasible overlaps.

**Theorem 1.7 (diagonal corner support).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.diagonal_corner_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.diagonal_corner_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For d_i in [0,1], real t and PSD X below diag(d) and t(1-diag(d)), the diagonal indicator P of 0<d_i<1 satisfies PX=X and XP=X. Endpoint columns vanish by positivity. The conclusion does not assume t>0; feasibility supplies the necessary restrictions.

**Theorem 1.8 (overlap supported).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.overlap_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.overlap_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For any PSD contraction C, any real t and X in positiveOverlaps C (t(1-C)), P=interiorProjection C satisfies PX=X and XP=X. Spectral diagonalization transfers the coordinate support argument. SingularCriterion and optimization reduction use this exact common corner.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.compress_le`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.diagonal_corner_support`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.extend_le`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_compress`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_isometry`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.inclusion_projection`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCorner.overlap_supported`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickSupport](MaximalHockeyStickSupport.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold](MaximalHockeyStickThreshold.md)
