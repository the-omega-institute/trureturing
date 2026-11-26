# The Fixed-Sector Action on the Relative Twisted Quotient

## Abstract

The actual fixed-sector C2 quotient acts on the negative twisted relative C2 quotient.

For lattice data D with unit Gram determinant, the negative twisted carrier is the parity -1 subspace. Its relative C2 subspace is the complex span of the minus-two modes of the corrected fixed-source field applied to negative twisted states.

**Theorem 1.1 (Higher negative modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.fixed_odd_mode_mem_relativeOddC2`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.fixed_odd_mode_mem_relativeOddC2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fixed-source mode of index at most minus two sends the negative twisted carrier into the relative C2 subspace. Translation reduces each successive mode to the preceding one with the source translated and a nonzero scalar inverted.

**Definition 1.2 (Descent of the minus-one action).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The commutator identity gives preservation of the relative C2 subspace. The iterate identity shows that fixed-sector C2 generators act trivially on the relative quotient. The resulting complex-linear map takes fixed quotient classes to endomorphisms of the relative quotient.

**Theorem 1.3 (Action on representatives).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The class of a fixed state acts on the class of a negative twisted state by taking the class of the corrected minus-one mode applied to those representatives.

**Theorem 1.4 (Compatibility with the fixed quotient product).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action of a fixed minus-one product equals the composition of the two actions in product order. In the Borcherds iterate, higher negative modes kill every term in the quotient except the composition of the two minus-one modes.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.fixed_odd_mode_mem_relativeOddC2`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_mk`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.relativeOddQuotientAction_product`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2](ActualLeechExtensionC2.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing](FixedSourceIsing.md)
