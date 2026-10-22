# The Hyperbolic Projector Product

## Abstract

The binary character projector equals the product of commuting half-sum involutions.

**Theorem 1.1 (The Hyperbolic Projector Product).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct.product_equals_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct.product_equals_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The operator (I+F_i)/2 is attached to each coordinate unit. The factors commute by the binary subgroup law. In the commutative additive group algebra, expanding the product corresponds to choosing either zero or one in each binary coordinate.

The product of coordinate-unit group elements is the original binary half itself. The universal algebra homomorphism into the given endomorphism algebra sends each group element to its actual F-action. Thus the finite product is exactly 2^(-n) times the sum of all F-actions. This identity is used for the original chosen native projector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct.product_equals_plus`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryOrbit](BinaryOrbit.md)
