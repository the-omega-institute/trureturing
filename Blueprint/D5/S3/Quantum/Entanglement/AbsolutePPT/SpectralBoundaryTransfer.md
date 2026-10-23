# Boundary-preserving spectral insertion and deletion

## Abstract

Rank-three and rank-four necessary spectral bounds transfer across actual middle multiplicities.

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

Natural dimensions are cast to the reals before division. The value is f(N)=(N+8)/(N+2)^2. The inner-polytope formula and the attaining spectrum (3,1,...,1)/(N+2) are due to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2. Only the unrestricted upper-bound inference is a candidate addition here.

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

**Definition 1.6 (Six heads and ten tails).**

$$\forall (n:\mathbb{N}),(\forall (q:Fin\left(16\right)),(rankFourBoundaryIndex\left(n, q\right)=if\left(q<6, q, n + q\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rankFourBoundaryIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In dimension n+16, the sixteen observed coordinates are the actual first six followed by the actual last ten. The remaining n coordinates form the middle. This observation includes boundary coincidences and zero coordinates.

**Definition 1.7 (Rank-four boundary observation).**

$$\forall (n:\mathbb{N}),(\forall (l:Fin\left(n + 16\right)\to \mathbb{R}),(\forall (q:Fin\left(16\right)),(rankFourBoundaryValues\left(n, l, q\right)=l\left(rankFourBoundaryIndex\left(n, q\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rankFourBoundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing nine-coordinate qutrit observation is recovered by retaining slots 0,1,2,10,11,12,13,14,15. Thus both existing K1 and K2 act on exactly the same top three and bottom six coordinates as before. The rank-four mass condition compares the sum of slots 0 through 5 with that of slots 6 through 15.

**Definition 1.8 (Bound under the rank-four necessary conditions).**

$$\forall (n:\mathbb{N}),(RankFourSpectralBound\left(n\right)\iff \forall (l:Fin\left(n + 16\right)\to \mathbb{R}),((((Antitone\left(l\right))\land (\forall (i:Fin\left(n + 7 + 9\right)),(0\leq l\left(i\right)))\land (\sum_{i:Fin\left(n + 7 + 9\right)}(l\left(i\right))=1)\land (PosSemidef\left(K1\left(boundaryValues\left(n + 7, l\right)\right)\right))\land (PosSemidef\left(K2\left(boundaryValues\left(n + 7, l\right)\right)\right)))\land (sumFirst\left(6, l\right)\leq sumLast\left(10, l\right)))\Rightarrow (\sum_{i:Fin\left(n + 16\right)}((l\left(i\right))^{2})\leq purityBound\left(n + 16\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.RankFourSpectralBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate universally quantifies all antitone nonnegative mass-one spectra of length n+16. It assumes both actual qutrit pencils are positive semidefinite and sumFirst 6 l <= sumLast 10 l. These are necessary spectral conditions. No APPT sufficiency, physical maximum, or uniqueness statement follows from the definition alone.

**Theorem 1.9 (Rank-four dimension transfer).**

$$\forall (n:\mathbb{N}),(\forall (a:\mathbb{N}),(((8\leq n)\land (1\leq a)\land (RankFourSpectralBound\left(n\right))\land (RankFourSpectralBound\left(n + 1 + a\right)))\Rightarrow (RankFourSpectralBound\left(n + 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rank_four_spectral_bound_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put N=n+17>=25 and t=l_(N-11), the actual coordinate immediately before the last ten. Inserting any positive number a of copies of t and deleting t preserve the first six and last ten coordinates, hence both actual qutrit pencils and the rank-four mass inequality. Order and nonnegativity are preserved even at ties and zeros. Ordering gives prefix mass at least (N-10)t and first-six mass at least 6t. The rank-four inequality therefore gives 1>=(N-4)t. In particular t<1, so deletion has positive mass. If t<=1/(N+2), insertion yields mass 1+at>0 and square sum P+at^2; the endpoint bound and the existing insertion factorization give P<=f(N+a)(1+at)^2-at^2<=f(N). If t>=1/(N+2), deletion yields mass 1-t and square sum P-t^2. The existing deletion factorization with kappa=4 gives f(N-1)(1-t)^2+t^2<=f(N). Its guard is 6(N^2-9N-16)>=0, which holds for N>=25; the cap is derived rather than postulated. Positive rescaling preserves the two pencils and the mass inequality. The theorem proves a new upper-bound implication between spectra in different dimensions; it does not assert that the necessary conditions characterize APPT.

The four-slot audit of rank_four_spectral_bound_transfer remains declared_unresolved with source.selection_missing: the parameterized endpoint predicates require a shared dimension-indexed readout reconstruction that the current source selector does not supply. The concrete gap is recorded at https://github.com/the-omega-institute/trureturing/issues/19257. The audit of rank_four_endpoint_interval is declared_validated; the linked issue does not complete the local-transfer audit.

**Theorem 1.10 (An upper endpoint fills the finite interval).**

$$\forall (M:\mathbb{N}),(((8\leq M)\land (RankFourSpectralBound\left(M\right)))\Rightarrow (\forall (n:\mathbb{N}),(((8\leq n)\land (n\leq M))\Rightarrow (RankFourSpectralBound\left(n\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rank_four_endpoint_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The length-24 base is obtained directly from QutritN8PurityBound.certificate_bound, which needs only the two qutrit pencils. Induction on n uses the rank-four dimension transfer with deletion endpoint n-1 and insertion count M-n. The top endpoint itself uses the supplied endpoint premise. Taking M=36 yields all actual dimensions 24<=N<=52 from the length-52 RankFourSpectralBound premise; N=n+16. The premise remains explicit. Physical application additionally requires the existing reduction from a literal unitary-quantified complex APPT density to one sorted spectrum satisfying these same necessary conditions. The published inner-polytope value and attainer remain attributed to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2. No global uniqueness or literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.RankFourSpectralBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.SpectralBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.purityBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rankFourBoundaryIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rankFourBoundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rank_four_endpoint_interval`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.rank_four_spectral_bound_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.spectral_bound_transfer`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound](QutritN8PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary](UniformRankFourNecessary.md)
