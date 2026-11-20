# Künneth equivalence for parity-odd differentials

## Abstract

The canonical cross product in cohomology for two complex-linear parity-odd differentials.

Let V and W be complex vector spaces, each with an endomorphism d satisfying d² = 0 and an involution σ satisfying dσ = −σd. The spaces and their differentials can be different and have arbitrary dimension. For each differential, cohomology is the quotient of its kernel by the image of the map into the kernel induced by d.

**Definition 1.1 (Signed tensor differential).**

Lean statement: `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential`

*Formalization.* `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On V ⊗ℂ W the differential K acts by K(x ⊗ y) = dV(x) ⊗ y + σV(x) ⊗ dW(y). On a parity eigenvector in V the second term carries the eigenvalue of σV.

**Theorem 1.2 (Square-zero law).**

Lean statement: `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential_square`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of input differentials, K² = 0. On pure tensors the two square terms vanish and the mixed terms cancel by dVσV = −σVdV. The total parity is σV ⊗ σW.

**Definition 1.3 (Cohomology of the signed tensor).**

Lean statement: `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv`

*Formalization.* `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cross product gives a complex-linear equivalence H(V,dV) ⊗ℂ H(W,dW) ≃ H(V ⊗ℂ W,K). The maps arise from sections of the image and cycle quotient, averaged against parity. On each factor this gives an odd homotopy h with dh + hd = 1 − ip for the inclusion i and projection p. With E = ip on the first factor, the tensor homotopy hV ⊗ 1 + (EVσV) ⊗ hW supplies the boundary for the composite on K-cycles. The other composite is the identity by pi = 1 in both factors.

**Theorem 1.4 (Value on cycle representatives).**

Lean statement: `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv_classOf_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv_classOf_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary x in ker dV and y in ker dW, the equivalence sends [x] ⊗ [y] to [x ⊗ y], where x ⊗ y is a genuine K-cycle and the brackets denote the corresponding quotient classes.

**Theorem 1.5 (Uniqueness of the cross product).**

Lean statement: `D5/S3/HomologicalAlgebra/ParityOddKunneth.crossProduct_unique`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/ParityOddKunneth.crossProduct_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex-linear map from H(V,dV) ⊗ℂ H(W,dW) to H(V ⊗ℂ W,K) with the value [x ⊗ y] on every [x] ⊗ [y] equals the cross product. Quotient surjectivity supplies such representatives and pure tensors determine the map.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential`
- Truth anchor: `D5/S3/HomologicalAlgebra/ParityOddKunneth.closedDifferential_square`
- Truth anchor: `D5/S3/HomologicalAlgebra/ParityOddKunneth.crossProduct_unique`
- Truth anchor: `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv`
- Truth anchor: `D5/S3/HomologicalAlgebra/ParityOddKunneth.kunnethEquiv_classOf_tmul`
- Dependency: [D5/S3/HomologicalAlgebra/FinitePerturbationCohomology](FinitePerturbationCohomology.md)
