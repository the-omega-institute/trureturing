# Forward Nested-Q Empty-Cutoff Branch

## Abstract

The actual forward nested-Q collision equality is closed on the empty inner-cutoff branch.

**Theorem 1.1 (The forward weighted identity when the inner cutoff is at most the signed lift).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For arbitrary lattice data, determinant-unit witness, current label, source states, signed gamma, delta, d, r, n, actual input x, linear functional phi, finite numerator P and independent outer cutoff function H₂, assume K ≤ r. The exact second component of the nested-Q telescope is proved: the actual outer sum over j is empty because its range is ((K:ℤ)-r).toNat.

The right-hand finite Taylor sum is also zero. If the total degree is negative its range is empty. Otherwise every u in the degree range satisfies 0 ≤ degree-u, and K ≤ r gives degree-u+r-K ≥ 0, so orderedResidueWeight is zero. The proof keeps the complete actual qField expression and arbitrary P; it does not transfer a cutoff to a Laurent monomial or assert the nondegenerate local-coordinate bridge.

The four-slot source-bound audit remains unfinished at issue #20163; this source bridge is not declared_validated.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation](LatticeHalfFockOuterTaylorEvaluation.md)
