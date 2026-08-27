# Memoryless Action Obstruction

## Abstract

Repeated public states with different actions rule out a memoryless policy.

**Theorem 1.1 (A repeated public state cannot support two different actions).**

$$\forall x3 \in \left(\forall x3 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x4 \in \left(\forall x4 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x5 \in \mathord{\cdot},\; \forall x6 \in \mathord{\cdot},\; \mathit{x3}\left(\mathit{x5}\right) = \mathit{x3}\left(\mathit{x6}\right) \Rightarrow \left(\mathit{x4}\left(\mathit{x5}\right) \ne \mathit{x4}\left(\mathit{x6}\right) \Rightarrow \left(\neg \left(\exists x9 \in \left(\forall x9 \in \mathord{\cdot},\; \mathord{\cdot}\right),\; \forall x10 \in \mathord{\cdot},\; \mathit{x9}\left(\mathit{x3}\left(\mathit{x10}\right)\right) = \mathit{x4}\left(\mathit{x10}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.no_memoryless_policy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public-state map and action trace are source primitives. If two times have the same public state but distinct actions, any policy depending only on that public state would assign equal actions at those times, contradicting the observed action inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.no_memoryless_policy`
