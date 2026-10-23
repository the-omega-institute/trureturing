# Actual A/B nested extraction

## Abstract

Actual finite source/source nested Q products at the original homogeneous numerator.

**Theorem 1.1 (Independent finite inner cutoff and the original rational numerator).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_nested_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_nested_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Keep the original labels y=J, v=A and z=B. For arbitrary actual states a,b, tensor x, linear covector phi and signed gamma,delta,d,r,n,j, let P satisfy the actual homogeneous numerator equation at the supplied cutoff K. The inner A/B cutoff I and outer cutoff H are independent natural numbers. The theorem identifies the actual coefficient of Q_(d-j)^1(J,Q_(r+j)^gamma(A,B;I);H) with the supported outer readout of completeAB(gamma,r+j,I,P/Q_K). In particular I=K retains the actual original finite field. Neither K nor I is assumed to be a locality order.

The actual finite Laurent supplier provides a numerator P0 at its own order K0. The homogeneous quotient comparison identifies P/Q_K with P0/Q_K0. Each nested summand has total mode degree (r+j)+(d-j)+n=d+r+n, so the supplier identifies all six words on exactly the required degree slice. The existing nested supported extraction applies with independent I; it does not compare actual fields at I and K0. The complete intermediate field supplies outer support, while the actual rightmost input supplies inner support.

The local A/B readouts in both spectator positions are the two remaining Hahn coefficients of the complete binary rational G. This gives the actual finite nested readout at the unchanged P,K, including K=0, empty supports and negative homogeneous degrees. The complete-field joint outer support and finite antidiagonal theorem below consumes this identification. Evaluation of its complete outer residues and the final middle Taylor equality remain further obligations.

The Reg source reconstructs the complete dependent telescope. Four-slot registration remains unfinished under issue #20163 because whole-family variation, sensitivity, observational dependence and the final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted.

**Theorem 1.2 (Complete joint outer support and a finite antidiagonal).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_joint_outer_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_joint_outer_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the original actual middle family, put N=((K:Z)-r).toNat and B(j)=((H(j):Z)-(d-j)).toNat. Each H(j) is an independent genuine locality order for the complete fields J and Q_(r+j)^gamma(A,B;K). The theorem bounds the support of the complete ordinary outer residue by ell<B(j), and every larger fractional cutoff computes the same complete outer readout. The original numerator P,K and actual finite inner cutoff K are retained.

The degree-preserving shift d to d+ell and n to n-ell identifies the complete residue with the same original homogeneous slice. Complete-field locality then annihilates the tail; neither individual ordered half is asserted to vanish. With T=N+sum_(j<N) B(j), the finite map (j,ell) to (j+ell,j) is a bijection onto the supported antidiagonal indices. Thus the weighted sum of actual nested coefficients equals the finite sum over t<T and j<=t,j<N of chooseSign(d,j) choose(-1/2,t-j) times the complete outer residue at ell=t-j. Zero and empty ranges remain in scope.

The complete outer residues in this antidiagonal still require evaluation in the binary Laurent rational G before finite_forward_outer_taylor gives the original middle Taylor equality. The theorem supplies actual identification, genuine joint support and finite reindexing; it does not assert that remaining evaluation or the full middle equality. The faithful Reg source reconstruction retains the entire independent locality family; the four-slot audit remains unfinished under issue #20163.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_joint_outer_support`
- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_nested_readout`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABLocalResidue](LatticeHalfFockABLocalResidue.md)
