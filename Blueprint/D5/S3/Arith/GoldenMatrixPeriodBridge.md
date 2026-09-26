# Golden Matrix Period Bridge

## Abstract

Golden residues act faithfully as two-dimensional multiplication matrices.

**Definition 1.1 (Multiplication in the golden residue algebra).**

Lean statement: `D5/S3/Arith/GoldenMatrixPeriodBridge.goldenMatrixHom`

*Formalization.* `D5/S3/Arith/GoldenMatrixPeriodBridge.goldenMatrixHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the ordered basis consisting of the golden generator and one, the residue a+b*phi acts by the matrix with rows (a+b,b) and (b,a). This assignment preserves zero, one, addition and multiplication over any modulus.

**Theorem 1.2 (Faithful Fibonacci matrix representation).**

Lean statement: `D5/S3/Arith/GoldenMatrixPeriodBridge.golden_matrix_faithful`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenMatrixPeriodBridge.golden_matrix_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix assignment is injective: its lower-right and upper-right entries recover both golden coordinates. The golden generator maps to the Fibonacci matrix with rows (1,1) and (1,0). Consequently the generator and this matrix have the same multiplicative order for every modulus.

## References

- Truth anchor: `D5/S3/Arith/GoldenMatrixPeriodBridge.goldenMatrixHom`
- Truth anchor: `D5/S3/Arith/GoldenMatrixPeriodBridge.golden_matrix_faithful`
