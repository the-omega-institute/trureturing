# The all-threshold classifier for the original singular pair

## Abstract

The all-threshold classifier for the original singular pair

Let S=A+B, C=normalize(S,A), P=interiorProjection(C). Every statement retains arbitrary traces, zero matrices and empty finite dimension. This geometry is a repository derivation used in quadratic and general-convex equality, not a theorem attributed to GGJ.

**Theorem 1.1 (original optimal iff normalized).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_optimal_iff_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_optimal_iff_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and t>=0, original trace optimality of the reconstructed canonical overlap is equivalent to weighted optimality of canonicalOverlap C t among PSD overlaps of C and t(1-C), with weight S. The support bijection handles the complementary endpoint piece.

**Theorem 1.2 (original canonical feasible).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_canonical_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_canonical_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and t>=0, reconstruct S (canonicalOverlap C t) is an actual element of positiveOverlaps A (tB). This candidate supplies the lower bound needed to turn optimality into equality of the value.

**Theorem 1.3 (original all thresholds iff commute).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_all_thresholds_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_all_thresholds_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B, maximalHockey A B t = Tr(A)-Re Tr(S canonicalOverlap(C,t)) for every t>0 exactly when (PSP)(PCP)=(PCP)(PSP). No optimizer, commutation, nonzero pair or faithfulness is assumed. The integrated quadratic criterion consumes this geometric iff; general convex necessity is then obtained from approximate tests.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_all_thresholds_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_canonical_feasible`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.original_optimal_iff_normalized`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickProfile](MaximalHockeyStickProfile.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion](MaximalHockeyStickSingularCriterion.md)
