# Weighted threshold optimality in the faithful interior

## Abstract

Weighted threshold optimality in the faithful interior

These finite matrix statements separate the positive-definite interior argument from later singular support reduction. The scalar canonical overlap is an antecedent of the Hiai canonical spectral preparation; its optimality for arbitrary weights is not assumed.

**Theorem 1.1 (weighted overlap optimal iff).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.weighted_overlap_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.weighted_overlap_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian A,B, positive-definite W,Y and Y<=A,B, Y maximizes Re Tr(WX) over PSD common lower bounds exactly when (A-Y) W (B-Y)=0. Congruence by sqrt(W), interior relaxation and Hermitian trace uniqueness prove the equivalence. The diagonal common-corner criterion consumes it.

**Definition 1.2 (canonicalOverlap).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonicalOverlap`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonicalOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

canonicalOverlap D t is the functional calculus of x -> min(x,t(1-x)). It is defined for arbitrary real t. Its PSD feasibility requires the contraction and nonnegative-threshold hypotheses proved elsewhere.

**Theorem 1.3 (canonical residuals).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_residuals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_residuals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian D and every real t, D-canonicalOverlap(D,t)=thresholdPositive(D,t), and t(1-D)-canonicalOverlap(D,t)=thresholdNegative(D,t). The one-threshold criterion uses both exact residual identities.

**Theorem 1.4 (canonical optimal iff).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian D with all eigenvalues in (0,1), positive-definite W and t>0, the canonical overlap maximizes the weighted PSD trace exactly when thresholdPositive(D,t) W thresholdNegative(D,t)=0. The candidate is positive definite in this scope. SingularCriterion obtains its broader scope by compression.

**Theorem 1.5 (canonical all thresholds iff commute).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_all_thresholds_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_all_thresholds_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For a strict positive contraction D and positive-definite W, canonical weighted optimality at every positive threshold is equivalent to WD=DW. This combines the one-threshold condition with spectral separation and serves the common-interior analysis.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonicalOverlap`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_all_thresholds_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_optimal_iff`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.canonical_residuals`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.weighted_overlap_optimal_iff`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap](MaximalHockeyStickOverlap.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral](MaximalHockeyStickSpectral.md)
