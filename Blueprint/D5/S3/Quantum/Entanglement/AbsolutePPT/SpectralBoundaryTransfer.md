# Boundary-preserving spectral insertion and deletion

## Abstract

Rank-three spectral bounds transfer across arbitrary middle multiplicities.

**Definition 1.1 (Extremal positions).**

$$\forall (n:\mathbb{N}),(\forall (q:Fin\left(9\right)),(boundaryIndex\left(n, q\right)=if\left(q<3, q, n + q\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vector of length n+9 has boundary positions q for q<3 and n+q for q>=3. These are its top three and bottom six entries, including ties. The parameter n counts middle coordinates. The displayed indices denote their natural values in Fin (n+9).

**Definition 1.2 (Boundary observation).**

$$\forall (n:\mathbb{N}),(\forall (l:Fin\left(n + 9\right)\to \mathbb{R}),(\forall (q:Fin\left(9\right)),(boundaryValues\left(n, l, q\right)=l\left(boundaryIndex\left(n, q\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation retains the three largest and six smallest coordinates. It does not observe the middle coordinates separately. K1 and K2 are the existing real symmetric three-by-three boundary pencils of QutritSpectralReduction.

**Definition 1.3 (Dimension-dependent purity value).**

$$\forall (N:\mathbb{N}),(purityBound\left(N\right)=\frac{N + 8}{(N + 2)^{2}})$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.purityBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural dimensions are cast to the reals before division. The candidate value is f(N)=(N+8)/(N+2)^2.

**Definition 1.4 (A bound for the rank-three relaxation).**

$$\forall (n:\mathbb{N}),(SpectralBound\left(n\right)\iff \forall (l:Fin\left(n + 9\right)\to \mathbb{R}),(((Antitone\left(l\right))\land (\forall (i:Fin\left(n + 9\right)),(0\leq l\left(i\right)))\land (\sum_{i:Fin\left(n + 9\right)}(l\left(i\right))=1)\land (PosSemidef\left(K1\left(boundaryValues\left(n, l\right)\right)\right))\land (PosSemidef\left(K2\left(boundaryValues\left(n, l\right)\right)\right)))\Rightarrow (\sum_{i:Fin\left(n + 9\right)}((l\left(i\right))^{2})\leq purityBound\left(n + 9\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.SpectralBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SpectralBound n is the universal square-sum upper bound for all antitone nonnegative mass-one vectors of length n+9 whose two boundary pencils are positive semidefinite. This is a spectral relaxation; no sufficiency assertion for literal APPT is included.

**Theorem 1.5 (Transfer from two endpoint dimensions).**

$$\forall (n:\mathbb{N}),(\forall (a:\mathbb{N}),((1\leq a)\Rightarrow ((SpectralBound\left(n\right))\Rightarrow ((SpectralBound\left(n + 1 + a\right))\Rightarrow (SpectralBound\left(n + 1\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.spectral_bound_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put N=n+10 and let t be the actual last middle entry. Evaluating K1 at the all-ones vector bounds the bottom-six mass below by the top-three mass, giving (N-3)t<=1. When t<=1/(N+2), insert a copies of t. The ordered tuple retains its boundary and has mass 1+a*t and squared mass P+a*t^2. When t>=1/(N+2), remove only t, retaining the boundary and obtaining mass 1-t>0 and squared mass P-t^2. Positive normalization lets the endpoint bounds apply. The insertion quadratic lies below f(N) on the first interval; the deletion quadratic lies below f(N) between its roots 1/(N+2) and (N^2+15N+20)/((N^2+3N+8)(N+2)). For a cap (N-kappa)*t<=1 with N-kappa>0, the same scalar factorization places the cap below the second root when (10-kappa)*N^2+(6-15*kappa)*N-20*kappa-16>=0. Here kappa=3, and the guard is 7N^2-39N-76>=0 for N>=10. Zero values and ties are included. No preservation hypothesis is assumed. Application at length twenty: let F be the set of real p for which there exists l:Fin 20→R with l antitone, every l_i nonnegative, sum l_i=1, K1(boundaryValues 11 l) and K2(boundaryValues 11 l) positive semidefinite, and sum l_i^2=p. The retained DimensionTwentySpectralPurityBound.spectral_purity_bound, using the baseline lengths 18 and 21 and this same-delivery transfer through length 19, gives p<=7/121 for every p in F. Define e_i=3/22 when i=0 and e_i=1/22 otherwise. If i<=j and j=0, both indices are zero; if j is nonzero, its value is 1/22 and either possible value of e_i is at least that. Thus e is antitone, nonnegative, and its mass is (3+19)/22=1. Its observed nine-tuple is (3,1,1,1,1,1,1,1,1)/22. Both K1 and K2 are the matrix [[1,-1,0],[-1,1,0],[0,0,1]]/11. They are symmetric, and their quadratic form on every real x in R^3 is ((x0-x1)^2+x2^2)/11>=0, establishing positive semidefiniteness. Its square sum is (9+19)/22^2=7/121. Consequently 7/121 belongs to F and bounds F above: IsGreatest F (7/121), so its real supremum is also 7/121. This is the full attained-maximum application of the structural inequality, without a separate finite equality certificate or theorem. Feasibility of these two necessary boundary matrices alone does not assert literal APPT; physical realization and its universal-unitary proof are supplied separately in QuadbitQuintitMaximumPurity.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.SpectralBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.purityBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.spectral_bound_transfer`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
