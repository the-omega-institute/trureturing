# Golden Cubic Order Discriminant and Index Form

## Abstract

The golden cubic coordinate order has an exact trace discriminant and index form.

**Theorem 1.1 (Trace discriminant and power-basis determinant).**

Lean statement: `D5/S3/Arith/Lattices/GoldenCubicIndexForm.golden_cubic_discriminant_index_form`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GoldenCubicIndexForm.golden_cubic_discriminant_index_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual Lucas block B_j = L_(3^j)^2 + 3, write a_j = (B_j - 1)/9. The integral coordinate ring on (1, theta, beta) uses the cubic multiplication table. The determinant of its regular-trace Gram matrix is -3 B_j^2. For alpha = r + b theta + c beta, the signed determinant of (1, alpha, alpha^2) is 3b^3 + 3b^2c + bc^2 - a_j c^3, and nine times this determinant is (3b+c)^3 - B_j c^3. The theorem concerns this constructed coordinate order; its embedding in the cubic number field and the maximal order index remain separate obligations.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GoldenCubicIndexForm.golden_cubic_discriminant_index_form`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
