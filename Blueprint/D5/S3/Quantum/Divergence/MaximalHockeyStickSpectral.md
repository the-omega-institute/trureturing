# Spectral cuts detect commutation on the common interior

## Abstract

Spectral cuts detect commutation on the common interior

The spectral argument retains repeated eigenvalues, endpoint eigenspaces, zero projections and empty finite matrix spaces. These are repository geometric derivations; HMT supplies the divergence question, while GGJ supplies an antecedent for common-support localization.

**Definition 1.1 (thresholdPositive).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdPositive`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdPositive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

thresholdPositive D t is the continuous functional calculus of x -> max(x-t(1-x),0). Threshold.canonical_residuals identifies it as the left residual of the canonical scalar minimum.

**Definition 1.2 (thresholdNegative).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdNegative`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdNegative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

thresholdNegative D t is the continuous functional calculus of x -> max(t(1-x)-x,0). It is the right residual, and its sandwich with the compressed weight is the threshold optimality obstruction.

**Theorem 1.3 (all thresholds iff commute).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_thresholds_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_thresholds_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian D,W whose nonzero entries in a D-eigenbasis connect only eigenvalues strictly between zero and one, vanishing thresholdPositive(D,t) W thresholdNegative(D,t) for every t>0 is equivalent to WD=DW. A positive threshold separates any two unequal interior eigenvalues. The common-corner version and the faithful threshold criterion consume this exact condition.

**Definition 1.4 (interiorProjection).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.interiorProjection`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.interiorProjection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

interiorProjection C is the functional-calculus projection onto eigenvalues in (0,1). Both zero and one eigenspaces are omitted. Corner.overlap_supported and the final original-pair commutator use this actual spectral projection.

**Theorem 1.5 (all common thresholds iff commute).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_common_thresholds_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_common_thresholds_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For arbitrary Hermitian C,W and P=interiorProjection C, vanishing thresholdPositive(C,t) (PWP) thresholdNegative(C,t) for every t>0 is equivalent to (PWP)C=C(PWP). No positivity or nonempty-corner premise is imposed here. SingularCriterion uses the result after geometric compression.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_common_thresholds_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.all_thresholds_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.interiorProjection`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdNegative`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.thresholdPositive`
