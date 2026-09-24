# Feasibility is detected by all level laws

## Abstract

Feasibility is detected by all level laws.

**Theorem 1.1 (Feasibility is detected by all level laws).**

$$\operatorname{feasible}\left(Q\right) \iff \forall l, \operatorname{feasible}\left(\operatorname{push}\left(l, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws.feasible_iff_all_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A feasible probability has full mass on the prescribed legal support, every node marginal equal to the prescribed marginal probability, and zero expected cycle excess.

For a probability on tuples of threads, completed feasibility is equivalent to feasibility of all actual finite projections. The completed legal support is the intersection of the legal support cylinders. The finite marginal probabilities are the actual projections of the completed marginal probability.

Countable intersections transfer full support. Equality of every finite projection determines each completed node marginal by the full-event total-variation identity. The expected-excess characterization transfers the final condition. No support-preservation assumption is needed for this correspondence about an already completed law.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws.feasible_iff_all_levels`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess](InverseLimitZeroExcess.md)
