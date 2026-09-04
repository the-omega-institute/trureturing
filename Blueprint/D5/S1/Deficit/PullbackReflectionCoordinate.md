# Pullback Reflection Coordinate

## Abstract

Golden-square scaling conjugates the pulled-back affine reflection to the classical reflection, with an invariant structural line and a single pointwise fixed point.

**Definition 1.1 (Pulled-back reflection).**

$$J_{qc}(s)=\frac{1}{\varphi^{2}}-s$$

*Formalization.* `D5/S1/Deficit/PullbackReflectionCoordinate.qcReflection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the affine reflection obtained by pulling z maps to one minus z back through multiplication by phi squared.

**Theorem 1.2 (Conjugacy, invariant line, and fixed point).**

$$\forall s\in\mathbb{C},\quad phi^{2}J_{qc}(s)=1-phi^{2}s\quad \land\quad (\Re(J_{qc}(s))=s_{star}\iff\Re(s)=s_{star})\quad \land\quad (J_{qc}(s)=s\iff s=s_{star})$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/PullbackReflectionCoordinate.pullback_reflection_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s, golden-square scaling carries the pulled-back reflection to one minus the scaled coordinate. The real-part equivalence proves that the structural vertical line is invariant.

The source calls this vertical line a fixed line. For the displayed holomorphic affine map that wording is false pointwise: solving J_qc(s) = s leaves only the real structuralZero. The theorem records both the valid setwise statement and the corrected fixed locus.

Repository searches found the scaling owner but no conjugacy or fixed-locus theorem. Pinned Mathlib contributes field normalization and complex linear arithmetic only.

## References

- Truth anchor: `D5/S1/Deficit/PullbackReflectionCoordinate.pullback_reflection_coordinate`
- Truth anchor: `D5/S1/Deficit/PullbackReflectionCoordinate.qcReflection`
- Dependency: [D5/S1/Deficit/Beatty/GoldenSpectralCoordinate](Beatty/GoldenSpectralCoordinate.md)
