# Factorial Recurrence and Solenoid Real-Flow Non-Embedding

## Abstract

Factorial times recur to zero along the faithful solenoid real flow.

**Theorem 1.1 (Factorial times return to zero in the solenoid).**

$$\lim_{n\to\infty} realFlow(n!) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/RealFlowRecurrence.realFlow_factorial_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive modulus m. Once n is at least m, divisibility of factorials writes n factorial as m times an integer, so the m-th additive-circle coordinate of the real flow is exactly zero. Thus every coordinate is eventually constant at zero.

The induced subtype topology and the product convergence criterion lift these coordinatewise limits to convergence in the universal solenoid. The pinned library supplies factorial divisibility and product-neighborhood convergence.

**Theorem 1.2 (The faithful real flow is not an embedding).**

$$\operatorname{Injective}(realFlow) \land \neg\operatorname{IsEmbedding}(realFlow).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/RealFlowRecurrence.realFlow_injective_not_isEmbedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity is the established trivial-kernel theorem for the real flow. If the flow were a topological embedding, it would reflect the factorial recurrence to convergence of the real factorial times at zero. But each factorial dominates its index, so the same sequence diverges to positive infinity, giving incompatible eventual bounds.

## References

- Truth anchor: `D5/S1/Solenoid/RealFlowRecurrence.realFlow_factorial_tendsto_zero`
- Truth anchor: `D5/S1/Solenoid/RealFlowRecurrence.realFlow_injective_not_isEmbedding`
- Dependency: [D5/S1/Solenoid/RealFlowInjectivity](RealFlowInjectivity.md)
