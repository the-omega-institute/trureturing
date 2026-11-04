# Exact Complementary Boundary of a Shifted Hankel Minor

## Abstract

Ordered complementary minors identify shifted Hankel determinants with fixed boundary Bezout determinants.

**Definition 1.1 (Ordered target-first columns).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.columnPerm`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.columnPerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For natural a,j,u, columnPerm permutes Fin(j+a+u) into the shifted interval a,...,a+j-1, followed by 0,...,a-1 and a+j,...,a+j+u-1, each in increasing order. Its inverse sends an index below a to j plus that index, an index from a to a+j-1 to that index minus a, and a later index to itself.

**Definition 1.2 (The increasing complementary boundary).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryIndex`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For i in Fin(a+u), boundaryIndex(a,j,u,i) is i when i<a and j+i otherwise. It indexes the increasing complement of the shifted interval in Fin(j+a+u), including empty intervals.

**Definition 1.3 (Zero-extended common-degree reversal).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.reverseCoeffs`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.reverseCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For natural N,h and c:N->Z, reverseCoeffs(N,c,h) equals c(N-h) when h<=N and zero otherwise. It uses the supplied common support degree, retaining leading zeros.

**Definition 1.4 (The fixed boundary Bezout matrix).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryMatrix`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Put t=a+u and N=j+t. For i,k<t with i<a, the entry is minus the sum over 0<=v<=i of reverseCoeffs(N,c,t+v-(k+i+1))*d(v)-reverseCoeffs(N,d,t+v-(k+i+1))*c(v), guarded by k+i+1<=t+v and zero otherwise. For i>=a, the entry is the sum over 0<=v<t-k of reverseCoeffs(N,c,(t-1-i)+(t-1-k)+1-v)*reverseCoeffs(N,d,v)-reverseCoeffs(N,d,(t-1-i)+(t-1-k)+1-v)*reverseCoeffs(N,c,v). All subtractions are natural and truncated; the low-row guard is part of the definition.

**Theorem 1.5 (Exact ordered indices, sign and common-degree reversal).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.shifted_hankel_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.shifted_hankel_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let Phi be any integer power series, base any natural shift, N=j+a+u>0, and mu_t=coeff(base+t,Phi). Let H have entries mu_(i+k), for i,k<N. The public statement uses the repository shiftedHankel definition directly: its target is shiftedHankel(Phi,base+a,j), and its enclosing determinant is shiftedHankel(Phi,base,N). The target consists of rows 0,...,j-1 and columns a,...,a+j-1, so its determinant is det(mu_(a+i+k)). Its inverse complementary minor has rows 0,...,a-1 followed by a+j,...,N-1, and columns j,...,N-1. In the increasing boundary coordinate b<a+u, the row map is b for b<a and j+b otherwise. The exact determinant factor is (-1)^(aj) det(H). Only det(H) is required to be a unit; neither the target nor any neighboring minor is assumed invertible. The formula includes j=0.

The proof directly consumes Matrix.det_submatrix_inl_eq_mul from Heights.Duality, retaining its original proof and exposing its private enumeration for this consumer. The column permutation lists the shifted interval first and then its increasing complement. Its inversions are precisely the aj pairs crossing the first two blocks. The inverse complement appears transposed in the duality interface; determinant invariance under transpose gives the stated row and column orientation.

Assume c_N=1, c is zero above N and d is zero at and above N. The normal moment relations for c and d are exactly those of hankel_inverse_bezout: the c moments vanish for t<N, and the d moments are minus the final basis vector. That existing inverse formula supplies every selected entry. Reverse both coefficient sequences at the same degree N, extending the reversals by zero. The high/high entries are the positive Bezout sum in those common reversals, with indices N-1-i and N-1-k. The sign is positive because common-degree reversal reverses the sign of the Bezout kernel. For a low boundary row b<a and tail column j+k, the summand at v<=b is zero unless k+b+1<=a+u+v. Under that guard its common high depth is a+u+v-(k+b+1). The support proof establishes zero in the complementary case before any natural subtraction is used. Thus a negative high depth never becomes a spurious coefficient at zero.

For the reversal identity, the complete antisymmetric convolution sums to zero by reflection. Split off its initial partial sum, then reflect the remaining indices at N. Terms outside the original support vanish before the natural-number indices are changed. This gives a finite boundary sum without an invertibility assumption on a smaller minor. Write t=a+u. Low-row common high depths are at most t-1 and use low c,d coefficients only up to a-1. High-row common high depths are at most 2t-1. For t<=N these depths satisfy the strict endpoint-jet range h<2N, including N=t and the empty target.

For the metallic application take mu_t=coeff(n+1+t,Phi), a=ell-(n+1), and choose a normal size N with j+a<=N. Taking N=K rho and fixing j modulo rho makes a+u=N-j fixed. The same normal_family c and d feed the formula. At s(p)=N, they are the specified-degree reversals of Q(p) and Q(p-1), respectively. The existing endpoint theorem gives s(p)=s(p-1)+(n+1), so their reversals at the common degree N are Q(p) and X^(n+1)Q(p-1). These are exactly the high coefficients P_2 and P_3; the original c and d coefficients are P_0 and P_1. The predecessor shift stays inside the coefficient extraction. An application must use the supplied support and common-degree identities, rather than substituting an actual polynomial degree or silently truncating a negative depth. This theorem supplies the exact complementary-minor and common-reversal bridge. MetallicHankelResiduePolynomials consumes it with the four endpoint jets to obtain all residues from their first terms; backward integer-value propagation then supplies all integer inputs.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryIndex`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.boundaryMatrix`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.columnPerm`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.reverseCoeffs`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelComplementaryMinor.shifted_hankel_boundary`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Duality](../../Arith/AbsoluteValues/Heights/Duality.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials](MetallicHankelBoundaryPolynomials.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
