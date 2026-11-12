# Removing the positive lower constraint at an interior optimum

## Abstract

Removing the positive lower constraint at an interior optimum

All matrices have the same arbitrary finite complex index type. The trace objective is its real part. This finite perturbation lemma is a repository proof used by the weighted overlap criterion; it is not a general-convex reverse-test optimality assertion.

**Theorem 1.1 (positive interior relaxation).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickInterior.positive_interior_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickInterior.positive_interior_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian-feasible Y0 positive definite and below Hermitian upper bounds A and B, and arbitrary matrix weight W, optimality of Re Tr(WY) over positive common lower bounds is equivalent to optimality over all Hermitian common lower bounds. Given a Hermitian competitor, a sufficiently small convex displacement from Y0 remains positive definite. Threshold.weighted_overlap_optimal_iff consumes this removal of the positivity constraint.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickInterior.positive_interior_relaxation`
- Dependency: [D5/S3/Quantum/Matrix/RpowPencilTaylor](../Matrix/RpowPencilTaylor.md)
