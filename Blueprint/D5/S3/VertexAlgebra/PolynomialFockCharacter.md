# Polynomial Fock Character

## Abstract

The concrete polynomial Fock zero-mode character is the partition Euler product.

The theorem uses the actual Sugawara L_0 eigenspaces from Polynomial Fock LZero Spectrum. An exponent vector of energy N is converted to a multiset of positive parts by replacing index i with part i + 1 and repeating it d i times. The resulting formal graded dimension is the unshifted partition Euler product.

**Theorem 1.1 (Energy fibers are equivalent to integer partitions).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockCharacter.energyFiberEquivPartition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockCharacter.energyFiberEquivPartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N, the finite exponent vectors whose weighted energy is N are in bijection with Nat.Partition N. The same construction includes the unique zero-energy object.

**Theorem 1.2 (The concrete zero-mode formal character is the Euler product).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockCharacter.lZero_character_euler_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockCharacter.lZero_character_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The power series whose N-th coefficient is the complex finrank of the actual lZeroEigenspace N equals the infinite product over j >= 1 of (1 - X^j)^(-1). This result is the unshifted graded dimension identity; it does not construct state fields, a Virasoro center, Monster action, fusion data, or a vacuum-energy shift.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockCharacter.energyFiberEquivPartition`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockCharacter.lZero_character_euler_product`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum](PolynomialFockLZeroSpectrum.md)
