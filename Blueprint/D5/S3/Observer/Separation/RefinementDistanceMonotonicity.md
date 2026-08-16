# Observer Distance Monotonicity Under Refinement

## Abstract

Refining observables without changing old costs cannot decrease dual distance.

**Theorem 1.1 (Observer distance is monotone under refinement).**

$$d_{m} \leq d_{m+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/RefinementDistanceMonotonicity.observer_distance_mono_of_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each layer, take the supremum of the endpoint evaluation gap over observables in that layer whose seminorm cost is at most one. The distance is extended-valued, so unbounded families are retained.

If the old observable family is contained in the refined family and the new seminorm restricts to the old one, every old admissible observable remains admissible. Pinned Mathlib's iSup_mono' compares the two differently indexed suprema directly.

## References

- Truth anchor: `D5/S3/Observer/Separation/RefinementDistanceMonotonicity.observer_distance_mono_of_refinement`
