# The exact threshold obstruction for a singular diagonal contraction

## Abstract

The exact threshold obstruction for a singular diagonal contraction

Only the weight restricted to the common interior must be positive definite. Endpoint weights, off-corner entries and empty corners remain in scope. This geometry is used in the singular functional-calculus criterion.

**Theorem 1.1 (diagonal optimal iff).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion.diagonal_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion.diagonal_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For d_i in [0,1], t>0 and W whose subtype compression to 0<d_i<1 is positive definite, let D=diag(d), Y=diag(min(d,t(1-d))) and P the interior indicator. Y is weighted-optimal over positiveOverlaps D (t(1-D)) exactly when diag((d-t(1-d))_+) (PWP) diag((t(1-d)-d)_+)=0. Corner reduction and the faithful weighted criterion prove this equivalence; SingularCriterion consumes it.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion.diagonal_optimal_iff`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization](MaximalHockeyStickCornerOptimization.md)
