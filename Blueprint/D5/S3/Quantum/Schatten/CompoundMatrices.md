# CompoundMatrices

## Abstract

Compound matrices and singular products.

The kth compound matrix has entries equal to kth order minors. Cauchy-Binet makes the compound construction multiplicative. Unitary diagonalization identifies its singular values with products over kth order subsets; sorting identifies the largest such product.

The source is Alex Meiburg's Apache-2.0 Physlib at revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the Schatten product Holder inequality. No mathematical originality is claimed.

Application to ordered Slater amplitudes. Fix natural numbers N and k with k at most N, and complex N by k matrices V and W. For each k-element subset S of Fin N, let d(S,V) be the determinant obtained by retaining the rows of V in increasing natural site order and leaving the column order unchanged. The rectangular cauchyBinet theorem, with the natural LinearOrder on Fin N and factors V adjoint and W, gives det(V adjoint W) = sum over S of conjugate(d(S,V)) times d(S,W). Thus V adjoint V = I gives sum over S of conjugate(d(S,V)) times d(S,V) = 1. The empty determinant is one, so this includes k = 0 without a factorial factor.

The ordering in this application needs an explicit comparison. The definition compoundMatrix fixes AllOrdered's classical order, whereas cauchyBinet accepts a supplied LinearOrder. For each S, let p(S) be the permutation of Fin k characterized by naturalEnum(S,i) = classicalEnum(S,p(S)(i)), and let epsilon(S) be its sign, cast to the complex numbers. For a complex N by N matrix U, let Cnat(U,k) use natural increasing rows and columns. Then Cnat(U,k)(S,T) = epsilon(S) epsilon(T) compoundMatrix(U,k)(S,T). Matrix.det_permute and Matrix.det_permute' give the two signs. They must be retained when using the frozen compound matrix in the ordered occupation basis.

For complex N by N matrices U and Q, applying cauchyBinet directly in natural order gives Cnat(U Q,k) = Cnat(U,k) Cnat(Q,k). Conjugate transpose commutes with this construction by Matrix.det_conjTranspose, and the compound of the identity is the identity. Consequently U adjoint U = I implies Cnat(U,k) adjoint Cnat(U,k) = I. For any complex N by N matrix B and N by k matrix V, the same rectangular formula gives d(S,B V) = sum over k-element T of Cnat(B,k)(S,T) d(T,V). This is the action on the actual determinant amplitudes, with no covariance or Gaussian-state premise.

These are applications of the existing determinant and compound results and introduce no new Lean declaration. Their occupation normalization and literal prefix marginal are described in PartialTraceMutualInformation. The global fixed-particle action alone does not establish that a prefix-supported one-particle unitary acts as an ordinary tensor product on the ordered Boolean site carrier. That locality correspondence and the resulting complete reduced spectrum remain separate obligations.

## References

- Dependency: [D5/S3/Quantum/Schatten/MatrixSimilarity](MatrixSimilarity.md)
