# Invariant Separation Forces Infinite Observer Distance

## Abstract

A bounded invariant observable separating two points forces infinite observer distance.

**Theorem 1.1 (Invariant separation forces infinite observer distance).**

$$\operatorname{Bounded}(f), L_\tau(f) = 0, f(x) \neq f(y) \Rightarrow d_\tau(x, y) = \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/InvariantObservableInfinity.invariant_separation_distance_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a bounded complex observable on the update index set. Its update defect L_tau(f) vanishes exactly when f is invariant under the permutation. If f separates x and y, their endpoint gap is strictly positive.

Every natural-number multiple of f remains bounded and has zero update defect, hence remains in the unit admissible ball. The corresponding endpoint gaps are unbounded, so their ENNReal supremum is infinity. The theorem uses the repository's frozen update-defect definition; the nearby visible-phase result is a concrete solenoid instance of this general scaling mechanism.

## References

- Truth anchor: `D5/S3/Observer/Separation/InvariantObservableInfinity.invariant_separation_distance_eq_top`
- Dependency: [D5/S3/Observer/ObserverMetric](../ObserverMetric.md)
