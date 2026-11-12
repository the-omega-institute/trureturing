# Canonical overlap optimality on a singular common interior

## Abstract

Canonical overlap optimality on a singular common interior

C may have eigenvalues zero and one. Neither C nor 1-C is assumed invertible. Strict positivity is required only for the compressed trace weight, as supplied for the original pair by CornerWeight.

**Theorem 1.1 (canonical feasible).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.canonical_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.canonical_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For a PSD contraction C and t>=0, canonicalOverlap C t belongs to positiveOverlaps C (t(1-C)). OriginalPair reconstructs this candidate into an actual feasible overlap for A,B.

**Theorem 1.2 (common canonical optimal iff).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_canonical_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_canonical_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD C<=1, t>0 and W with positive-definite interior compression, canonical weighted optimality is equivalent to thresholdPositive(C,t) (PWP) thresholdNegative(C,t)=0 for P=interiorProjection C. This transports the diagonal criterion through the eigenvector unitary.

**Theorem 1.3 (common all thresholds iff commute).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_all_thresholds_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_all_thresholds_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD C<=1 and Hermitian W with positive-definite interior compression, canonical optimality at every t>0 is equivalent to (PWP)(PCP)=(PCP)(PWP). OriginalPair consumes this all-threshold geometric classification; no general-f attainment is part of its assumptions.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.canonical_feasible`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_all_thresholds_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.common_canonical_optimal_iff`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion](MaximalHockeyStickCornerCriterion.md)
