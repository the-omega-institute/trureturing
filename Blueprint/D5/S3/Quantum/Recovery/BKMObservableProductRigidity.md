# Grouped modular observability and connected product rigidity

## Abstract

Grouped modular observability and connected product rigidity for the actual BKM gap.

**Theorem 1.1 (Commutation with whole retained modular ratio groups).**

Lean statement: `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_commute_ratioPieces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_commute_ratioPieces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the right partial trace of a positive definite joint matrix A on finite spaces with a nonempty environment. For each real v, collect the entries of the retained Hermitian observable K for which the row eigenvalue of S equals v times the column eigenvalue. The resulting matrix in the original basis is the v component of K. The ratio group includes all entries with that ratio, including those arising from repeated eigenvalues. The actual BKM gap vanishes if and only if the relative density, obtained by sandwiching A with the lifted inverse square root of S, commutes with the identity lift of every component. To prove the equivalence, apply the modular functional calculus to the indicator of each ratio on the fixed weighted observable. The joint modular eigen-equation becomes the commutation equation after removing the two marginal square roots. Conversely the component eigen-equations give functional intertwining on their sum.

**Theorem 1.2 (Exact product of the two marginals for a connected observable).**

Lean statement: `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_eq_marginals_kronecker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_eq_marginals_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose additionally that A has trace one, the eigenvalues of S are distinct, and the graph of nonzero off-diagonal entries of K in that eigenbasis is connected. The gap vanishes if and only if A is the Kronecker product of its two partial traces. In retained spectral coordinates every auxiliary slice of the relative density commutes with all ratio components. Each ratio component of a slice inherits these commutations. Its adjoint times itself is diagonal and constant along graph edges. A ratio different from one has a zero column at a spectral extremum, so its entire component vanishes. The remaining diagonal slice is scalar by connectivity. This gives a tensor product with the retained identity, and undoing the sandwich and taking the left partial trace yields the two actual marginals.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_commute_ratioPieces`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMObservableProductRigidity.bkmGap_eq_zero_iff_eq_marginals_kronecker`
- Dependency: [D5/S3/Quantum/Recovery/BKMObservableRigidity](BKMObservableRigidity.md)
