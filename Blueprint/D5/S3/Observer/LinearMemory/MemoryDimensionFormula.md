# Memory Dimension Formula

## Abstract

The canonical linear memory quotient has dimension equal to the all-future observable dimension minus the current readout rank.

**Theorem 1.1 (Memory dimension is future visibility beyond current rank).**

$$\forall K, V, Y, T, C,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}T \in \operatorname{LinearMap}(K, V, V) \land C \in \operatorname{LinearMap}(K, V, Y) \Rightarrow\\{}\operatorname{finrank}(K, \operatorname{memoryQuotient}(C, T)) = \operatorname{finrank}(K, \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid k \in N, y \in Y\})) - \operatorname{finrank}(K, \operatorname{range}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/MemoryDimensionFormula.memory_dimension_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. Let T evolve V linearly and let C read V linearly into Y.

The memory object is the canonical quotient of the current kernel by the all-future kernel. The observable space is independently constructed as the span of every adjoint-observable iterate.

Quotient dimension, the imported orthogonal duality between the all-future kernel and observable span, and rank-nullity reduce both sides to the same finite-dimensional subtraction.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/MemoryDimensionFormula.memory_dimension_formula`
- Dependency: [D5/S3/Observer/LinearMemory/ZeroMemoryCriterion](ZeroMemoryCriterion.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality](../../ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.md)
