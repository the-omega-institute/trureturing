# Precision Separation Persistence

## Abstract

Separation at one layer of a compatible precision tower persists at every finer layer.

**Theorem 1.1 (Separated states remain separated at every finer precision).**

$$\begin{aligned}\forall X: \operatorname{Type}, O: \mathbb{N} \to \operatorname{Type},\\q: \forall n: \mathbb{N}, X \to O_{n},\\rho: \forall n: \mathbb{N}, O_{n+1} \to O_{n},\\k, m: \mathbb{N}, x, y: X,\\(\forall n: \mathbb{N}, q_{n} = rho_{n} \circ q_{n+1}) \land k \leq m \land\\q_{k}(x) \neq q_{k}(y) \Rightarrow q_{m}(x) \neq q_{m}(y).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence.precision_separation_persists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each lowering map recovers the readout at its coarser layer exactly. Thus equality at a finer layer projects to equality at the preceding layer.

Induction across the interval from k to m transports any hypothetical equality back to layer k, contradicting the stated separation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence.precision_separation_persists`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity](../RefinementFactorization/CompatiblePrecisionTowerMonotonicity.md)
