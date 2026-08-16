# Negative Direction in a Full Evaluation Image

## Abstract

A full two-coordinate complex evaluation image contains a strictly negative cross direction.

**Theorem 1.1 (A full two-coordinate evaluation has a negative cross direction).**

$$\forall T, \forall E: T \to C^{2}, \forall m\in\mathbb{N}, 0<m \land \operatorname{dim}(\operatorname{im}(E))=2 \Rightarrow \exists g\in T, 4 m\Re(E(g)_1\cdot\overline{E(g)_2})<0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection.two_dimensional_evaluation_has_negative_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T be a complex vector space and E a complex-linear map from T to two complex coordinates. If the image of E has complex dimension two, then it is the entire coordinate space. For every positive natural multiplicity m, the theorem produces g in T for which four times m times the real part of the first coordinate multiplied by the conjugate of the second is strictly negative.

Mathlib's maximal-finrank submodule theorem turns the rank hypothesis into surjectivity. Lift the coordinate pair (1,-1) through E; its cross value is -4m, which is negative because m is positive. The identity evaluation on the two-coordinate complex space witnesses that the hypotheses are jointly satisfiable.

The cross value is the same multiplicity-weighted real cross term used by the neighboring convolution-square orbit formulas.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection.two_dimensional_evaluation_has_negative_direction`
