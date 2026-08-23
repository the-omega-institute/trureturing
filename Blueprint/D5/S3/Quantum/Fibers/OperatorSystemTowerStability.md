# Permanent Stability of the Operator-System Tower

## Abstract

One-step stability of a full Hermitian operator-system tower is permanent.

**Theorem 1.1 (One-step operator-system stability is permanent).**

$$\begin{gathered}\forall d, \operatorname{Finite}\left(d\right),\\{}\phi^{*}: \operatorname{CompletelyPositiveMap}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right), \operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right), \phi^{*}(I) = I,\\{}S_{0}: \operatorname{OperatorSystem}\left(\operatorname{Hermitian}\left(\operatorname{Matrix}\left(d, d, \mathbb{C}\right)\right)\right), n\in \mathbb{N},\\{}\operatorname{predictionTower}\left(\phi^{*}, S_{0}, n\right) = \operatorname{predictionTower}\left(\phi^{*}, S_{0}, n+1\right) \Rightarrow\\{}\forall r\in \mathbb{N}, \operatorname{predictionTower}\left(\phi^{*}, S_{0}, n+r\right) = \operatorname{predictionTower}\left(\phi^{*}, S_{0}, n\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OperatorSystemTowerStability.operator_system_tower_once_stable_permanently` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the full real self-adjoint part of the finite complex matrix algebra, rather than its centered trace-zero subspace. An operator system is a real subspace of that carrier containing the identity.

The Heisenberg action is supplied by a unital completely positive map. Each prediction step joins the current operator system with its Heisenberg image, and the finite tower is the iteration of this source closure step from the initial operator system.

Equality of stages n and n plus one says that stage n is a fixed point of the closure step. Fixed-point iteration then identifies every stage n plus r with stage n.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OperatorSystemTowerStability.operator_system_tower_once_stable_permanently`
- Dependency: [D5/S3/Quantum/Fibers/CenteredEffectTowerStability](CenteredEffectTowerStability.md)
