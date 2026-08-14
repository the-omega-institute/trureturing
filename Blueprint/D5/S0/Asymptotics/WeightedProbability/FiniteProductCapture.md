# Finite Product Capture Law

## Abstract

Independent column-weighted finite listings have an exact one-row twisted-diagonal capture mass.

**Theorem 1.1 (Exact one-row weighted capture probability).**

$$(\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \forall a,\ \operatorname{captureProbability}\left(q, f, a\right) = \operatorname{fixedMass}\left(q, f, a\right) \prod_{b\neq a} \operatorname{collisionMass}\left(q, f, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture.capture_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sample stores the listing diagonal and each off-diagonal row as independent coordinates, and reassembly uses EscapeCount.diagonal.

Summing the free rows gives one; the captured row leaves exactly fixedMass and the remaining column collisionMass factors.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture.capture_probability_exact`
- Dependency: [D5/S0/Asymptotics/SkewedEscapeMass](../SkewedEscapeMass.md)
- Dependency: [D5/S0/Diagonal/EscapeCount](../../Diagonal/EscapeCount.md)
