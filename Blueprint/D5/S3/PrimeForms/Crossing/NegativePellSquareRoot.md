# The Negative-Pell Matrix Square Root

## Abstract

A trace-zero square root of the negative-Pell discriminant produces a determinant-minus-one matrix.

**Theorem 1.1 (The trace-zero discriminant root yields determinant minus one).**

$$\forall j\in\mathbb{Z}, V\in\operatorname{Mat}_{2}(\mathbb{Z}), \operatorname{tr}(V)=0 \land V^{2}=(36j^{2}+1)I \Rightarrow delta=6jI+V, \operatorname{det}(delta)=-1, delta^{2}=(72j^{2}+1)I+12jV$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/NegativePellSquareRoot.negative_pell_square_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an integer 2x2 matrix of trace zero whose square is (36 j^2 + 1) times the identity. The matrix delta = 6 j I + V then has determinant -1, and delta^2 is exactly (72 j^2 + 1) I + 12 j V. This is the matrix form of the negative-Pell square-root construction in residual E.43.

Mathlib's trace_fin_two turns trace V = 0 into V_11 = -V_00. The (0,0) entry of the square hypothesis gives V_00^2 + V_01 V_10 = 36 j^2 + 1. Substitution in Mathlib's det_fin_two formula gives det(6 j I + V) = -1. For the square formula, distributivity, commutation of scalar matrices, and the assumed value of V^2 reduce the result to two integer ring identities.

Repository and pinned-Mathlib searches found no theorem combining a trace-zero 2x2 scalar square with this determinant and explicit square conclusion. Exact Mathlib hits were Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.scalar, and Matrix.scalar_comm; the proof imports and applies those declarations. This formalization closes only the delta-construction clause of E.43. It does not claim the inert-prime valuation lemma, the divisibility construction of V, the purity theorem, or the representation criterion.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/NegativePellSquareRoot.negative_pell_square_root`
