# Actual Ground Products and Cocycle Exchange

## Abstract

The chosen actual quotient representation realizes the lattice cocycle product and exchange.

For D:LatticeData and hu:IsUnit D.G.det, groundAction is the lift of a charge through the same groundRepresentation on ActualGround D hu used by the charged tensor coefficients. The inherited representation theorem supplies the central sign action -1. Natural-sign induction and reduction to F2 identify every central scalar; no new representation or exchange-law hypothesis is introduced.

**Theorem 1.1 (Actual ground actions multiply with the integral cocycle).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all charges left and right, groundAction(left)*groundAction(right) equals epsilon D left right smul groundAction(left+right) as endomorphisms of ActualGround D hu. Multiplication in the actual sign extension and the representation homomorphism yield the exact cocycle normalization.

**Theorem 1.2 (The actual ground product exchanges by the pairing parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The product in left/right order equals paritySign(bilinear D left right) smul the product in right/left order. This consumed helper applies ground_action_product twice and the existing epsilon_skew identity, with charge-addition commutativity. PhysicalLocality uses it on the actual ground vector.

The construction and cocycle mechanism are inherited from the repository's twisted ground realization and actual lattice cocycle. These exact consequences on the chosen ActualGround are repository-derived. FLM is background attribution; its full text is not an inspected source here. The determinant-unit premise is retained, and the statements cover every charge and ground vector, including zero charges and rank-zero data satisfying that premise. They supply ground factors, without asserting oscillator locality, twisted Jacobi or analytic CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_exchange`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
