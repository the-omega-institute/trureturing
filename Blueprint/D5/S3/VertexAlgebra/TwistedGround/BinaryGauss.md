# Binary Gauss Sums and the Determinant Modulo Eight

## Abstract

Binary Gauss Sums and the Determinant Modulo Eight.

**Theorem 1.1 (Binary Gauss Sums and the Determinant Modulo Eight).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.binary_gauss_of_integral_unit_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.binary_gauss_of_integral_unit_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binary Gram block H(a,b,c) over Z/8 has rows (2a,b) and (b,2c), with b odd. Its half-norm on two mod-two coordinates is q(x,y)=a*x^2+b*x*y+c*y^2 modulo two. The sum of (-1)^q over the four coordinates is 2 times the existing quadratic character chi_8(det H). The hyperbolic block has positive sign, while blocks with a and c both odd have negative sign.

For any finite family of such blocks, the sum over all binary coordinates factors as the product of the binary sums. Multiplicativity of Mathlib ZMod.chi_8 identifies the sign of this product with chi_8 of the product of the block determinants. The empty family has Gauss sum one.

If the product determinant is u^2*d modulo eight, where u is odd and d is an integer unit, then u^2=1 modulo eight and d is 1 or -1. In both cases chi_8(d)=1. Thus the complete block sum is the positive value 2 to the number of blocks. The integer-unit condition is stronger than invertibility modulo two: the block with a=b=c=1 has determinant three and negative Gauss sign.

This theorem evaluates a supplied binary decomposition. It does not construct the decomposition of a general integral lattice Gram matrix, identify its half-norm under a change of coordinates, or assert symmetry of the pairing on ActualGround. Those additional implications require their respective mathematical bridges.

**Theorem 1.2 (The Binary Block Sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.block_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.block_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary block over Z/8 with odd off-diagonal coefficient b, the sign sum of its quadratic half-norm over the four mod-two coordinates is 2*chi_8(det H). In binary Schur elimination, this value multiplies the Gauss sum of the residual quadratic form. It permits either Gauss sign and imposes no integer-unit determinant premise.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.binary_gauss_of_integral_unit_congruence`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BinaryGauss.block_sum`
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../LatticeTwistedGroundRealization.md)
