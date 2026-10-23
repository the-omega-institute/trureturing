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

The same-numerator coefficient calculation is supplied by forward_weighted_identity below. This intermediate theorem retains both the actual readout and its completeAB rational representation; the latter is needed to identify the genuine numerator in that calculation.

The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted.

**Theorem 1.2 (The original middle equality at negative total Taylor degree).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

With the complete original state, covector, coefficient and independent locality telescopes, let degree=L+M+K-d-r-2<0. The original weighted actual middle sum equals the original sum of collisionTaylor(P,gamma,u,(degree-u).toNat) times orderedResidueWeight(d-L,degree-u+r-K). No replacement numerator appears in this conclusion.

For j<(K-r).toNat, the integer K-r-j-1 is nonnegative, so the signed binary Taylor order B(j)-(d-j)-1 equals degree exactly. Negative degree gives d-j>=B(j), annihilating every complete actual coefficient by actual_ab_binary_taylor. The original Taylor range is empty because (degree+1).toNat=0. This exact negative-degree branch is consumed by the full middle equality below.

The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted.

**Theorem 1.3 (The full original actual weighted middle equality).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Retain every original state, covector, homogeneous six-word coefficient equation, signed lift, supplied inner cutoff K, and independent genuine whole-field locality order H(j). For degree=L+M+K-d-r-2, the original weighted sum over j<(K-r).toNat equals the original sum over u<(degree+1).toNat of collisionTaylor(P,gamma,u,(degree-u).toNat) times orderedResidueWeight(d-L,degree-u+r-K). The conclusion holds for all signed degrees and all cutoffs.

For K>r put t=(K-r-1).toNat. The genuine completeAB residue at w=r+j is cleared at B(j)=L+M+t-j. Expanding its original signed Laurent monomials produces a finite sum indexed by ell,u with ell+u<=t-j. Each term is the original remaining monomial with z exponent shifted by e(1)-ell-u, multiplied by (y-z)^(ell+u), the original fractional coefficient choose(-gamma/2,ell), choose(e(1),u), and chooseSign(-L,t-j-ell-u). This polynomial is derived from completeAB, and injectivity of the Laurent polynomial embedding identifies it with the actual Q(j).

A graded fractional Taylor functional keeps the exact total-exponent fiber. Multiplication by y-z shifts its Taylor order by one, with a zero boundary at order zero. Iteration gives the full ell+u boundary, and Vandermonde combines ell and u into v. The supplied actual coefficient equation supplies the required homogeneous fiber; no extra homogeneity or locality assumption is added. Thus binaryTaylor(Q(j),B(j),1,d-j,n) equals the sum over v<=t-j of collisionTaylor(P,gamma,(degree-v).toNat,v), cut off when v>degree, times chooseSign(-L,t-j-v).

The proof actually applies finite_forward_outer_taylor at t to this same-P coefficient identity. The K<=r empty branch and negative-degree branch are retained. All original signed numerator exponents, empty supports, zero degree and boundary fibers remain in scope. The fused and reverse components of sameNumeratorCollisionBridge are separate obligations; this result closes its complete middle conjunct.

The Reg mirror reconstructs the complete source telescope and proves its actual law. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status or independent admission is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.actual_ab_binary_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity_of_negative_degree`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation](BinaryLaurentEvaluation.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockNestedQForwardEdge](LatticeHalfFockNestedQForwardEdge.md)
