# Solenoid Path-Orbit Classification

## Abstract

Path-connected universal-solenoid points are exactly points on one real-flow orbit.

**Theorem 1.1 (Path-connected points are exactly one real-flow orbit).**

$$\forall x, y \in \mathcal{S},\ \operatorname{Joined}(x, y) \iff \exists t \in \mathbb{R},\ y = realFlow(t) + x.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two universal-solenoid points are joined by a continuous path exactly when the second is the sum of the first and a real-flow element. For the forward implication, extend the unit-interval path continuously to the real line and apply the existing unique streamline decomposition; subtracting its endpoint lift values gives the required flow parameter. The reverse implication uses the explicit real-flow segment.

Pinned Mathlib supplies Path, Joined, and the canonical continuous interval extension. No library theorem classifies path components of the universal solenoid, so the forward direction reuses the repository's established streamline decomposition.

This is a partial closure of the source corollary's path-orbit clause. The quotient parametrization, uncountability, classification of hidden jumps, transverse two-leaf structure, and cocycle law remain outside this deposit.

## References

- Truth anchor: `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit`
- Dependency: [D5/S1/Solenoid/StreamlineDecomposition](StreamlineDecomposition.md)
