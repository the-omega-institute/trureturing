# Finite Bilateral Trajectories

## Abstract

Bilateral trajectories of a finite system are uniquely based at periodic points.

**Theorem 1.1 (Finite systems have unique bilateral periodic trajectories).**

$$\forall Y, [\operatorname{Finite} Y],\ F: Y \to Y,\ (\forall x \in B(F), \forall n \in \mathbb{N},\ x_{n} \in P(F)) \land\ (\forall y \in P(F),\ \exists! b: B_{per}(F),\ b_{0} = y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FiniteBilateralTrajectory.finite_bilateral_trajectory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be finite and F a self-map. A bilateral trajectory is represented by its backward half x, satisfying F(x(n+1))=x(n); its forward half is then generated uniquely by F. A bilateral periodic trajectory is the subtype for which every represented state is periodic.

The exact repository coordinate-periodicity theorem proves the first conjunct and shows that every compatible trajectory belongs to that subtype. The exact coordinate-zero bijection supplies one trajectory through each periodic point and proves its uniqueness.

The imported repository results apply the pinned-Mathlib declarations Function.bijOn_periodicPts, Function.IsPeriodicPt.eq_of_apply_eq, and Fintype.exists_ne_map_eq_of_card_lt. Repository and pinned-Mathlib searches found no theorem packaging both displayed clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FiniteBilateralTrajectory.finite_bilateral_trajectory`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore](BackwardOrbitCore.md)
