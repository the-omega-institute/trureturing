# Controllability Gramian Reachable Range

## Abstract

The stable ordinary controllability Gramian has exactly the reachable-state range.

**Theorem 1.1 (The controllability Gramian range is reachable).**

$$\begin{aligned}\forall K, V, U: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)],\\{}[\operatorname{InnerProductSpace}(K, V)], [\operatorname{FiniteDimensional}(K, V)],\\{}[\operatorname{NormedAddCommGroup}(U)], [\operatorname{InnerProductSpace}(K, U)],\\{}[\operatorname{FiniteDimensional}(K, U)],\\{}\forall A: \operatorname{LinearMap}(K, V, V), B: \operatorname{LinearMap}(K, U, V),\\{}\operatorname{Summable}(\operatorname{discountedGramianTerm}(\operatorname{adjoint}(A), \operatorname{adjoint}(B), 1)) \Rightarrow \operatorname{range}(\operatorname{toLinearMap}(\operatorname{controllabilityGramian}(A, B))) = \operatorname{reachableSubspace}(A, B).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/ControllabilityGramianReachableRange.controllability_gramian_range_eq_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The controllability Gramian is constructed as the weight-one observability Gramian of the adjoint system, so its terms are the source operators A^k B B-adjoint (A-adjoint)^k. The displayed summability premise is the exact series form of stability.

The imported ordinary-Gramian theorem identifies its kernel with the all-future adjoint-input kernel. Infinite observability duality turns that kernel into the orthogonal complement of the canonical reachable span; self-adjointness then identifies the range.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/ControllabilityGramianReachableRange.controllability_gramian_range_eq_reachable`
- Dependency: [D5/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy](../LinearMemory/ObservabilityGramianKernelEnergy.md)
- Dependency: [D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability](../LinearMemory/ReachableObservableQuotientReachability.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality](../../ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.md)
