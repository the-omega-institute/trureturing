# Pairing defect algebra

## Abstract

The exact covariance and pairing-defect convolution algebra for every finite label set.

Let the label and index types be finite, let A be a commutative real algebra, and let ell be a real linear functional. The covariance identities assume ell(1)=1, ell(Y(d))=0, and Y(d)^2=a*Y(d)+b*1 for every index d. No positivity, independence, weight bound, or distinct-moment size bound is assumed. Pairing polynomials use unordered two-element label sets, so no orientation or symmetry hypothesis on an ordered array is needed.

**Definition 1.1 (Family moment on a label subset).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetFamilyMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetFamilyMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell, Y, original label weights f, and a finite label set U, subsetFamilyMoment is ell applied to the product over i in U of the weighted sum over d of f(i,d)*Y(d).

**Definition 1.2 (Distinct-index moment on a label subset).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetDistinctMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetDistinctMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell, Y, f, and U, subsetDistinctMoment is the existing distinctIndexMoment applied to the original weights f restricted to U and enumerated by the inverse of Fintype.equivFin(U). This fixes a canonical ordering without changing the signed sum.

**Definition 1.3 (Scalar product-weight sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetWeightSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetWeightSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For f and a finite label set U, subsetWeightSum is the existing indexSum of d mapped to the product over i in U of f(i,d).

**Definition 1.4 (Distinct-index pairing defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetPairingDefect`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetPairingDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell, Y, f, and U, subsetPairingDefect is subsetDistinctMoment on U minus finitePairingPolynomial on U with each two-label edge weighted by its subsetDistinctMoment.

**Theorem 1.5 (Exact partial-pairing defect convolution).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subset_pairing_defect_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subset_pairing_defect_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite label type and index type, ell, Y, real a,b, and weight family f satisfying the stated normalization, centering, and quadratic relation, and every finite label set U, sum over its partial pairings P the quantity b to the number of pairs, times the product of subsetWeightSum(f,E) over E in P, times subsetDistinctMoment on U minus pairingSupport(P). Subtract finitePairingPolynomial on U weighted by subsetFamilyMoment. The result is the same partial-pairing sum with subsetDistinctMoment replaced by subsetPairingDefect on the uncovered labels. For a two-label edge, reindex its weights to Fin 2 and directly apply the existing quadratic_second_moment_eq theorem. This gives V(E)=R(E)+b*T(E). Apply finitePairingPolynomial_add with edge weights b*T and R to obtain W_V(U)=sum over partial P of b to its size times the product of T over P times W_R on the uncovered labels. Subtract this identity term by term from the convolution of distinct moments. The statement includes all finite orders and places no upper bound on the top distinct-index moment.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetDistinctMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetFamilyMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetPairingDefect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subsetWeightSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra.subset_pairing_defect_convolution`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex](AssignmentMomentReindex.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial](PartialPairingPolynomial.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion](QuadraticCubicExpansion.md)
