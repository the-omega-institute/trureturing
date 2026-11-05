# The Full Inverse at a Normal Hankel Index

## Abstract

Normal moment relations determine the complete supported Bezout formula for a Hankel inverse.

**Theorem 1.1 (Every inverse entry from the two normal polynomials).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials.hankel_inverse_bezout`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials.hankel_inverse_bezout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let mu be an integer moment sequence and N=n+1 be any positive size. Let c and d be integer coefficient sequences, extended by zero above degrees N and N-1 respectively, with c_N=1. Assume that c is orthogonal to moments at every shift t<N, and that the moment vector of d is minus the last basis vector: its moments vanish at t<N-1 and equal minus one at t=N-1. If H=(mu_(i+j)) has unit determinant, then its inverse entry at any i,j<N is minus the sum, over 0<=a<=j, of c_(i+j+1-a)d_a-d_(i+j+1-a)c_a. These are the coefficients of -(c(x)d(y)-d(x)c(y))/(x-y). The statement includes size one and imposes no condition on intervening principal minors.

Multiplication by x modulo the monic polynomial c gives a companion matrix T. The normal moment relations give HT=T-transpose H and fix the last inverse column as -d. Symmetry fixes the last row. The resulting entry recurrence, descending in the row and ascending in the column, determines every inverse entry. Zero support at the last row supplies the boundary case of the finite sum. Thus the argument obtains the complete inverse even for a gapped normal family.

For higher shifted metallic Hankel determinants, this identity supplies the inverse entries used in a fixed complementary minor of a larger normal matrix. MetallicHankelUnbounded.normal_family supplies these normal data at every prescribed period boundary. MetallicHankelComplementaryMinor consumes the inverse with exact ordered indices and signs, and MetallicHankelResiduePolynomials combines it with endpoint jets and backward integer-value propagation.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials.hankel_inverse_bezout`
