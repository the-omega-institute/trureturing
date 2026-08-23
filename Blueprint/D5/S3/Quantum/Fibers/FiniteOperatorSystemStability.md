# Finite Operator-System Stability

## Abstract

Finite operator-system stability at one step persists at every later step.

**Theorem 1.1 (One stable operator-system step is permanently stable).**

$$\begin{gathered}\forall d, \operatorname{Finite}\left(d\right),\\{}H: \operatorname{CompletelyPositiveMap}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right), \operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right), H(I) = I,\\{}S_{0}: \operatorname{OperatorSystem}\left(\operatorname{Hermitian}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right)\right), m\in \mathbb{N},\\{}\operatorname{predictionTower}\left(H, S_{0}, m\right) = \operatorname{predictionTower}\left(H, S_{0}, m+1\right) \Rightarrow\\{}\forall r\in \mathbb{N}, \operatorname{predictionTower}\left(H, S_{0}, m+r\right) = \operatorname{predictionTower}\left(H, S_{0}, m\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiniteOperatorSystemStability.finite_operator_system_once_stable_permanently` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite carrier is the full real self-adjoint part of a complex matrix algebra. The initial operator system and prediction tower are the canonical objects supplied by the operator-system tower family.

The Heisenberg action is a unital completely positive map. Each tower step joins the current system with its image under that map, so the tower is constructed from the source channel and initial accessible system.

The imported permanent-stability theorem applies directly to equality of stages m and m plus one, yielding equality of every stage m plus r with stage m.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiniteOperatorSystemStability.finite_operator_system_once_stable_permanently`
- Dependency: [D5/S3/Quantum/Fibers/OperatorSystemTowerStability](OperatorSystemTowerStability.md)
