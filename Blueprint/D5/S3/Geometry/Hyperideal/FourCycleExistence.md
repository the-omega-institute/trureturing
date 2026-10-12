# A simultaneous solution for all global edge equations

## Abstract

Every four-cycle incidence system has one shared interior zero-curvature vector.

Let T be a finite type of tetrahedra and E a type of global edge labels with decidable equality. The incidence s assigns a label to each of the six local edges of every tetrahedron and a low/high colour to each global label. FourCycle(s) requires the four low slots to form the prescribed local cycle, degree eight at each low label, and degree at least twelve at each high label. Degrees are actual fibre cardinalities, including repeated occurrences.

The lower and upper endpoints L(s) and U(s), local cosine C(s,x,o), and curvature K(s,x,e) are exactly those of FourCycleCurvature. In particular, each local coordinate reads the same global vector x:E -> Real. K is 2pi minus the sum of arccos(C) over the actual occurrence fibre.

**Theorem 1.1 (An interior vector with all angle sums equal to 2pi).**

$$\forall T \in Type, E \in Type, s \in Incidence\left(T, E\right),\; \left(Fintype\left(T\right) \land \left(DecidableEq\left(E\right) \land FourCycle\left(s\right)\right)\right) \Rightarrow \left(\exists x \in E \to Real,\; \left(\forall e \in E,\; L\left(s\right)\left(e\right) < x\left(e\right) \land x\left(e\right) < U\left(s\right)\left(e\right)\right) \land \left(\left(\forall o \in Product\left(T, Fin\left(6\right)\right),\; -1 < C\left(s, x, o\right) \land C\left(s, x, o\right) < 1\right) \land \left(\forall e \in E,\; K\left(s, x, e\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every global label has a nonempty finite occurrence fibre, so the incidence map is surjective and the edge-label type is finite. This finiteness is derived from FourCycle(s); it is not an additional hypothesis.

The established box has strictly positive radicands, strictly admissible cosines, and inward curvature margins on all faces. Polynomial operations, square roots away from zero, division and arccos make the actual shared curvature map continuous on this box.

Normalize the box to a unit cube. The cube is a retract of a simplex: divide its n coordinates by n+1, append the slack coordinate one minus their sum, and project back by multiplying the n non-slack weights by n+1 and clamping to [0,1]. The classical simplex fixed-point theorem therefore applies to the clamped curvature self-map. Strict face signs exclude every boundary coordinate of its fixed point; interior clamp cancellation then forces every curvature to vanish.

The conclusion concerns the real incidence system. It does not assert that arbitrary incidence data form a manifold, supply face pairings or vertex-link conditions, or prove unrestricted CFMP. The geometric interpretation of the cosine formula and the passage to a complete hyperbolic realization retain their separate hypotheses.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature`
- Dependency: [D5/S3/Geometry/FixedPoint/Brouwer](../FixedPoint/Brouwer.md)
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleCurvature](FourCycleCurvature.md)
