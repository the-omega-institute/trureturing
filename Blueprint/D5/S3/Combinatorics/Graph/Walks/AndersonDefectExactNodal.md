# Common roots and periodic trace constraints

## Abstract

Common roots at the designated defect site satisfy the periodic Chebyshev equations and vanish on the strict trace product.

Let K be a field with an algebra over the real numbers. Let r and m be natural numbers at least three, and let t and mu belong to K, with t transcendental over the real numbers. On Fin(rm), set q=(m-1)r+1 and U(i)=-1 exactly when i modulo r is zero or i=q, and U(i)=1 otherwise. The Hamiltonian H is the ordinary cycle graph Laplacian plus t diag(U). The matrix H^(q) is its actual principal submatrix deleting q; the remaining diagonal entries retain the value 2+tU(i).

Put T(d)=[[d,-1],[1,0]], a=2+t-mu, b=2-t-mu and sigma=trace(T(a)^(r-1)T(b)). The polynomials S_n satisfy S_0=1, S_1=X and S_(n+2)=X S_(n+1)-S_n. Let traceFactors be the product of sigma_r(lambda,t)-2cos(2 pi k/m) over 0<k and 2k<m. The hypotheses say that mu is a common root of the characteristic polynomials of H and H^(q).

**Theorem 1.1 (The two Chebyshev equations).**

$$\forall (K : Type), \operatorname{Field}\left(K\right) \Rightarrow \left(\operatorname{Algebra}\left(\mathbb{R}, K\right) \Rightarrow \forall (r : \mathbb{N}), \forall (m : \mathbb{N}), 3 \le r \Rightarrow \left(3 \le m \Rightarrow \forall (t : K), \forall (mu : K), \operatorname{Transcendental}\left(\mathbb{R}, t\right) \Rightarrow \left(\operatorname{IsRoot}\left(\operatorname{charpoly}\left(\operatorname{H}\left(r, m, t\right)\right), mu\right) \Rightarrow \left(\operatorname{IsRoot}\left(\operatorname{charpoly}\left(\operatorname{principalMinor}\left(r, m, t, \operatorname{q}\left(r, m\right)\right)\right), mu\right) \Rightarrow \left(\left(\operatorname{eval}\left(\operatorname{S}\left(K, m-1\right), \operatorname{trace}\left(\operatorname{periodicBlock}\left(r, t, mu\right)\right)\right) = 0 \land \operatorname{eval}\left(\operatorname{S}\left(K, m-2\right), \operatorname{trace}\left(\operatorname{periodicBlock}\left(r, t, mu\right)\right)\right)+1 = 0\right) \land \operatorname{IsRoot}\left(\operatorname{traceFactors}\left(r, m, t\right), mu\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal.common_root_trace_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric matrix and a singular principal minor, a nonzero kernel vector vanishing at the deleted coordinate is obtained by zero extension and the symmetry of the bilinear pairing. Applied to mu I-H, this gives an actual nodal eigenvector at q.

The cycle equation transports this vector through the rotated block C=T(a)T(b)T(a)^(r-2). Two consecutive zero coordinates would force the vector to vanish throughout the cycle. Hence its initial nonzero coordinate can be divided out, giving C^m(1,0)=(1,0). The trace of C is sigma.

Write s=S_(r-2)(a), v=S_(r-3)(a) and h=bs-v. The first column of C is (ah-s,h). If h=0, then (-s)^m=1. Since r is at least three, this makes a algebraic over the real numbers; s and v are then algebraic, and b=v/s is algebraic. The equality t=(a-b)/2 contradicts transcendence. Thus h is nonzero. The two coordinates of the determinant-one Chebyshev power formula now give the displayed equations.

The first Chebyshev equation places sigma/2 among the real roots of U_(m-1), even when the common root lies in an extension field. The second equation and T_m=X U_(m-1)-U_(m-2) give T_m(sigma/2)=1. The real extremum classification forces an even angular index, while the roots of U_(m-1) exclude both endpoints. Thus sigma=2cos(2 pi k/m) for an index with 0<k and 2k<m, and the strict trace product vanishes at mu.

The conclusion concerns common-root containment. It does not assert equality of the monic gcd with the periodic trace product, its exact degree, or squarefreeness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal.common_root_trace_constraints`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily](AndersonDefectFamily.md)
