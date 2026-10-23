# LatticeHalfFockABOuterTaylor

## Abstract

Complete binary Laurent evaluation and its actual nested-Q application.

**Theorem 1.1 (Actual complete binary Taylor readout with independent locality).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.actual_ab_binary_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.actual_ab_binary_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Fix arbitrary original states a,b, signed lifts gamma,delta,d,r,n, tensor input x, covector phi, supplied K and a Laurent numerator P satisfying the original actual homogeneous coefficient equation. Each H(j) is an independent genuine locality order for J and the complete finite field Q_(r+j)^gamma(A,B;K). Put B(j)=L+M+(K-r-j-1).toNat, where L=frequencyBound(a)+1 and M=frequencyBound(b)+1.

There is a finite Laurent numerator Q(j) of the same complete binary rational G=completeAB(gamma,r+j,K,P/Q_K), with G=Q(j)/(y-z)^B(j). The actual coefficient of Q_(d-j)^1(J,Q_(r+j)^gamma(A,B;K);H(j)) equals binaryTaylor(Q(j),B(j),1,d-j,n) for every j<(K-r).toNat. The actual finite inner cutoff K is retained.

The actual six-word identification first gives the two remaining Hahn orders of G. Genuine complete-field locality permits padding the outer supported readout from H(j) to max(H(j),B(j)). The generic binary evaluation applies there. It does not use caller-K global locality, monomial locality, ordered-half locality or a target coefficient assumption.

The further coefficient identity between binaryTaylor(Q(j),B(j),1,d-j,n) and the original collisionTaylor(P,gamma) convolution at nonnegative degree remains open. This theorem evaluates the complete binary residue at its own numerator; it does not assert the complete original middle equality.

The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted.

**Theorem 1.2 (The original middle equality at negative total Taylor degree).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

With the complete original state, covector, coefficient and independent locality telescopes, let degree=L+M+K-d-r-2<0. The original weighted actual middle sum equals the original sum of collisionTaylor(P,gamma,u,(degree-u).toNat) times orderedResidueWeight(d-L,degree-u+r-K). No replacement numerator appears in this conclusion.

For j<(K-r).toNat, the integer K-r-j-1 is nonnegative, so the signed binary Taylor order B(j)-(d-j)-1 equals degree exactly. Negative degree gives d-j>=B(j), annihilating every complete actual coefficient by actual_ab_binary_taylor. The original Taylor range is empty because (degree+1).toNat=0. This proves the exact negative-degree branch; the nonnegative-degree branch and the full collision bridge remain open.

The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.actual_ab_binary_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation](BinaryLaurentEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockNestedQForwardEdge](LatticeHalfFockNestedQForwardEdge.md)
