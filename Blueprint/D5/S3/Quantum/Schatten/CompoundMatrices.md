# CompoundMatrices

## Abstract

Compound matrices and singular products.

The kth compound matrix has entries equal to kth order minors. Cauchy-Binet makes the compound construction multiplicative. Unitary diagonalization identifies its singular values with products over kth order subsets; sorting identifies the largest such product.

The source is Alex Meiburg's Apache-2.0 Physlib at revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the Schatten product Holder inequality. No mathematical originality is claimed.

Application to ordered Slater amplitudes. Fix natural numbers N and k with k at most N, and complex N by k matrices V and W. For each k-element subset S of Fin N, let d(S,V) be the determinant obtained by retaining the rows of V in increasing natural site order and leaving the column order unchanged. The rectangular cauchyBinet theorem, with the natural LinearOrder on Fin N and factors V adjoint and W, gives det(V adjoint W) = sum over S of conjugate(d(S,V)) times d(S,W). Thus V adjoint V = I gives sum over S of conjugate(d(S,V)) times d(S,V) = 1. The empty determinant is one, so this includes k = 0 without a factorial factor.

The ordering in this application needs an explicit comparison. The definition compoundMatrix fixes AllOrdered's classical order, whereas cauchyBinet accepts a supplied LinearOrder. For each S, let p(S) be the permutation of Fin k characterized by naturalEnum(S,i) = classicalEnum(S,p(S)(i)), and let epsilon(S) be its sign, cast to the complex numbers. For a complex N by N matrix U, let Cnat(U,k) use natural increasing rows and columns. Then Cnat(U,k)(S,T) = epsilon(S) epsilon(T) compoundMatrix(U,k)(S,T). Matrix.det_permute and Matrix.det_permute' give the two signs. They must be retained when using the frozen compound matrix in the ordered occupation basis.

For complex N by N matrices U and Q, applying cauchyBinet directly in natural order gives Cnat(U Q,k) = Cnat(U,k) Cnat(Q,k). Conjugate transpose commutes with this construction by Matrix.det_conjTranspose, and the compound of the identity is the identity. Consequently U adjoint U = I implies Cnat(U,k) adjoint Cnat(U,k) = I. For any complex N by N matrix B and N by k matrix V, the same rectangular formula gives d(S,B V) = sum over k-element T of Cnat(B,k)(S,T) d(T,V). This is the action on the actual determinant amplitudes, with no covariance or Gaussian-state premise.

Extend the natural compounds to the full Boolean occupation carrier. For words x and y on Fin m, define Gamma_m(B)(x,y) as the natural minor B[S(x),S(y)] when the two occupied subsets have the same cardinality, and as zero otherwise. This includes the vacuum sector, whose empty minor is one. Sectorwise cauchyBinet and the Boolean-word/subset bijection give Gamma(B C) = Gamma(B) Gamma(C), Gamma(B adjoint) = Gamma(B) adjoint, and Gamma(I) = I. The last identity uses a zero row when equal-size subsets differ and Matrix.submatrix_one when they agree. Thus U adjoint U = I gives Gamma(U) adjoint Gamma(U) = I on every occupation word.

Ordered-prefix locality holds for any complex ell by ell matrix U, without a unitarity hypothesis. Write B = U directSum I_n in Fin (ell + n) order and concatenate words literally with Fin.append. Then Gamma_(ell+n)(B)(ab,a'b') = Gamma_ell(U)(a,a') delta(b,b'). To see this in natural minor coordinates, the occupied subset of ab is S(a) mapped by Fin.castAdd n, union S(b) mapped by Fin.natAdd ell. These maps have disjoint images. Finset.orderEmbOfFin_unique identifies its increasing enumeration with the prefix enumeration followed by the tail enumeration. If b differs from b', a tail site missing from the other subset gives an identically zero row or column, so Matrix.det_eq_zero_of_row_eq_zero or its column version applies. If the tails agree, equal total particle count forces equal prefix particle count; reindexing by finSumFinEquiv gives a block matrix with the prefix minor and an identity tail block. Matrix.det_fromBlocks_zero₂₁ gives exactly the prefix determinant. Unequal total counts give zero by definition. No shuffle sign appears because every prefix site precedes every tail site.

These are applications of the existing determinant and compound results and introduce no new Lean declaration. Their occupation normalization and literal prefix marginal are described in PartialTraceMutualInformation, where the locality identity is consumed to derive covariance of that actual marginal. The two permutation signs above still apply whenever compoundMatrix in its fixed classical order is used. Locality does not supply the complete reduced spectrum or entropy.

## References

- Dependency: [D5/S3/Quantum/Schatten/MatrixSimilarity](MatrixSimilarity.md)
