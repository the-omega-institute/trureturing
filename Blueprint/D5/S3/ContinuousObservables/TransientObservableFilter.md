# Transient Observable Filter

## Abstract

Finite pullback observables form a descending fiber filtration with exact image and rank dimensions.

**Theorem 1.1 (Finite pullback observables have exact fiber and rank dimensions).**

$$\operatorname{transientObservableFilter}(tau, k).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/TransientObservableFilter.transient_observable_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier and a self-map tau, the k-step pullback image is a unital commutative subalgebra of the source function space. The next image is contained in it, and membership is exactly constancy on fibers of tau iterated k times.

The algebra is constructed from pointwise evaluation along tau. Its dimension is identified by restriction to the actual image of the iterated state map, and the canonical transfer operator supplies the matching range rank and image cardinality.

## References

- Truth anchor: `D5/S3/ContinuousObservables/TransientObservableFilter.transient_observable_filter`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics](../ObserverMemory/InverseLimits/TraceRankCombinatorics.md)
