# Regularity of the actual overlap value

## Abstract

Regularity of the actual overlap value

These estimates concern the actual common-PSD feasible set for arbitrary finite PSD A,B and their original masses. They supply uniform continuity constants for approximate-test gap transfer, not an optimizer for an arbitrary convex cost.

**Theorem 1.1 (feasible le value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.feasible_le_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.feasible_le_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Every feasible positive common lower bound X has real trace at most overlapValue A B. Boundedness follows from the upper bound A. ReverseTest.maximal_hockey_le and original-pair optimality use this supremum bound.

**Theorem 1.2 (overlap increment).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_increment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For 0<=s<=t and PSD A,B, the overlap increment O(t)-O(s) lies between zero and (t-s) Tr(B). Monotonic inclusion proves the first inequality; rescaling a maximizing overlap proves the upper bound. overlap_lipschitz consumes both bounds.

**Theorem 1.3 (overlap lipschitz).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For nonnegative s,t and PSD A,B, |O(t)-O(s)| <= |t-s| Tr(B). This two-sided estimate follows from ordered increments. Approximate.actual_gap_profile_data uses it together with the classical test estimate.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.feasible_le_value`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_increment`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.overlap_lipschitz`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap](MaximalHockeyStickOverlap.md)
