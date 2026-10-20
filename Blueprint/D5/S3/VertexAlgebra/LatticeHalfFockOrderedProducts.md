# Native Ordered Half-Fock Products

## Abstract

Native half-Fock oscillator coefficient composition equals its supported contraction expansion.

Fix arbitrary lattice data D, charges left and right, integer indices first and second, and an oscillator polynomial p. Normalize each oscillatorCoefficient index by subtracting chargeNorm of its own charge. The ordered expansion uses halfContraction coefficients and commonKernel at first+d,second-d. Rectangular lower bounds give finite support in d separately for each p.

**Theorem 1.1 (The actual oscillator composition is the finite ordered-diagonal sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

oscillatorCoefficient D left (first-chargeNorm D left) applied to oscillatorCoefficient D right (second-chargeNorm D right) p equals the finsum over natural d of halfContraction.coeff(d) smul commonKernel D left right (first+d) (second-d) p. No positivity, determinant-unit, homogeneity, nonzero-charge or bounded-index assumption is added.

The constant case converts the actual oscillator sum to finite polynomial convolution and uses half_creation_coefficient_transport. Polynomial induction then handles addition and creators. On the creator branch, both actual coefficient recurrences are reused through oscillator_coefficient_X_mul, whose original private proof remains in ChargedTensorCoefficients. The common-kernel creator recurrence and finite-sum algebra identify the three shifted induction terms.

The private orderedExpansion is linear because addition and scalar multiplication are justified by finite supports after fixing each polynomial. This does not claim a uniformly finite sum in the endomorphism space. PhysicalLocality consumes the theorem in its pure tensor product expansion; ground actions and cocycle exchange are supplied there separately.

The half-Fock construction and transport APIs are inherited; this exact polynomial induction and finite coefficient composition are repository-derived. FLM is background attribution with no full-text inspection or literature novelty claim here. The theorem establishes an algebraic ordered product, without asserting analytic convergence, all-source locality or twisted Jacobi.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockProductKernel](LatticeHalfFockProductKernel.md)
