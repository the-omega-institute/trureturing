# LocalResidues

## Abstract

Signed local residues for the complete middle Taylor equality

The imported collisionTaylor retains the original fractional coefficients. The original orderedResidueWeight data and finite forward Taylor convolution remain here with the complete source/source residue calculation. The signed kernel branches and the coefficient-field data are imported from the canonical binary evaluator.

The completeAB rational field is formed from the ordinary A/B residue before its z mode shift. The entire original ab_complete_remaining_orders conjunction is retained: the finite Laurent monomial representation, the genuine high-weight zero tail, and both remaining Hahn orders of that same field. Its pole bound is L+M+(K-w-1).toNat for arbitrary signed monomials and independent fractional cutoff I. No monomial locality is assumed.

**Theorem 1.1 (finite_forward_outer_taylor).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_forward_outer_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_forward_outer_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained.

**Theorem 1.2 (ab_complete_remaining_orders).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_remaining_orders`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_remaining_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained.

**Theorem 1.3 (ab_complete_pole_bound).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_pole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_pole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained.

**Theorem 1.4 (finite_collision_balance).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_collision_balance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_collision_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For arbitrary Laurent P, signed gamma,d,r and natural L,M,N,degree with degree=L+M+N-d-r-2, each finite Taylor coefficient satisfies the signed fused-versus-ordered residue balance. The proof uses the signed binomial kernel identity and treats both signs of d-L. This balance is consumed by the actual nested-Q iterate; it identifies no field without the three actual residue readouts.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_pole_bound`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_remaining_orders`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_collision_balance`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_forward_outer_taylor`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation](../BinaryLaurentEvaluation.md)
