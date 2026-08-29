# Barycenter Defect Decomposition

## Abstract

The completion barycenter and anti-coordinate separate center from mirror displacement.

**Theorem 1.1 (Barycenter and anti-coordinate separate mirror pairs).**

$$\begin{gathered}\forall \rho\in \mathbb{C}, \operatorname{completionBarycenter}(\rho) := \frac{\rho+\operatorname{mirror}(\rho)}{2},\quad \operatorname{antiCoordinate}(\rho) := \frac{\rho-\operatorname{mirror}(\rho)}{2},\\{}((\forall \rho\in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho) \Rightarrow \Re(\rho) = \operatorname{criticalAbscissa}) \Leftrightarrow (\forall \rho\in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho) \Rightarrow \operatorname{antiCoordinate}(\rho) = 0)) \land\\{}\forall \Delta, \Gamma\in \mathbb{R}, \Delta \neq 0 \Rightarrow \operatorname{let} r: \mathbb{C} := (\operatorname{criticalAbscissa}+\Delta)+i\Gamma; \operatorname{let} \ell: \mathbb{C} := (\operatorname{criticalAbscissa}-\Delta)+i\Gamma;\\{}\operatorname{let} c: \mathbb{C} := \operatorname{criticalAbscissa}+i\Gamma; \operatorname{completionBarycenter}(r) = c \land \operatorname{completionBarycenter}(\ell) = c \land\\{}\operatorname{antiCoordinate}(r) = \Delta \land \operatorname{antiCoordinate}(\ell) = -\Delta \land \operatorname{mirror}(r) = \ell \land \operatorname{mirror}(\ell) = r \land\\{}\operatorname{card}\{r, \operatorname{mirror}(r)\} = 2 \land \left\lVert r-c \right\rVert = \left|\Delta\right| \land \left\lVert \ell-c \right\rVert = \left|\Delta\right|.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/BarycenterDefectDecomposition.barycenter_defect_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The barycenter and anti-coordinate are constructed from the frozen conjugate-reflection map. Vanishing anti-coordinate on every nontrivial zero is exactly the critical-line condition.

For every real nonzero displacement and real height, the explicitly constructed symmetric pair has a common completion center, opposite anti-coordinates, and is exchanged by the mirror map. Its canonical two-point mirror orbit has radius equal to the absolute displacement.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/BarycenterDefectDecomposition.barycenter_defect_decomposition`
- Dependency: [D5/S3/Zeros/Symmetry/ZeroSymmetryAction](ZeroSymmetryAction.md)
