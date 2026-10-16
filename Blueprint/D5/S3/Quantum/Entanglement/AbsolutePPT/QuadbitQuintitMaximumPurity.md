# Four-by-five APPT maximum purity

## Abstract

The maximum purity of a literal four-by-five APPT density matrix is 7/121.

**Definition 1.1 (Nine extremal spectral coordinates).**

$$\forall (N:Nat), (9\leq N)\Rightarrow \forall (l:Fin\left(N\right)\to \mathbb{R}), \forall (q:Fin\left(9\right)), cornerBoundaryValues\left(N, l, q\right)=l\left((if val\left(q\right)<3 then val\left(q\right) else N-9+val\left(q\right):Fin\left(N\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.cornerBoundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For every total dimension N at least nine, the selector observes the top three and bottom six ordered coordinates. Its proof argument 9<=N is omitted from this display. At N=20 it is the same observation as SpectralBoundaryTransfer.boundaryValues 11.

**Theorem 1.2 (Necessary spectral matrices in arbitrary finite local dimensions).**

$$\forall (m:Nat), \forall (n:Nat), ((3\leq m)\land (3\leq n))\Rightarrow \forall (rho:Matrix\left((Fin\left(m\right)\times Fin\left(n\right)), (Fin\left(m\right)\times Fin\left(n\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow \exists (l:Fin\left(m\cdot n\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(m\cdot n\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(m\cdot n\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(cornerBoundaryValues\left(m\cdot n, l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(cornerBoundaryValues\left(m\cdot n, l\right)\right)\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\sum_{i:Fin\left(m\cdot n\right)} (l\left(i\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.spectral_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For all natural m,n at least three, every positive semidefinite trace-one complex matrix on Fin m × Fin n satisfying literal APPT has an antitone nonnegative spectrum l of length mn and mass one. The proof argument 9≤mn is suppressed in the displayed cornerBoundaryValues selector. Both existing real matrices K1 and K2 evaluated on the nine extremal spectral coordinates are positive semidefinite, and Re trace(rho*rho) equals the sum of all mn spectral squares. Repeated and zero eigenvalues are included. Embed Fin 3 into each local factor. Their product c has a finite complement, identified with Fin(mn−9) by cardinality. Extend the Bell unitary and its swapped partner by identity on this complement. Partial transpose commutes with compression along this product: both entries at (i,j),(k,l) equal rho(c(i,l),c(k,j)). The existing Bell principal identity then gives the two necessary matrices. Ordered spectral diagonalization uses an arbitrary global packing only as a unitary conjugation; it assumes no partial-transpose covariance of that packing. These conditions are necessary and do not assert APPT sufficiency. At mn=24 the boundary equals QutritSpectralReduction.boundaryValues 5 and permits direct use of the existing dimension-24 sharp certificate. Hildebrand Theorem 2, PDF page 5 of quant-ph/0502170, already gives APPT 4×6→3×8 at fixed total dimension 24, so the qutrit maximum and established attaining ray imply the 4×6 scalar value. At total dimension twenty, the selector is SpectralBoundaryTransfer.boundaryValues 11. The length-twenty bound follows by the full rank-three insertion/deletion theorem from endpoint lengths eighteen and twenty-one, first reaching nineteen and then twenty. For the four-by-five product, the normalized coordinate ray (I+2|00><00|)/22 is exactly diagonal (3,1^19)/22. Its trace is one and its trace-square is (20+8)/22^2=7/121. For any global unitary U, the unit vector U|00> yields a separable numerator by LowRankRays.separableCone_one_add_two_rankOne; positive normalization and separableCone_partialTranspose_posSemidef imply APPT. At total dimension twenty-four, the same argument combined directly with QutritN8PurityBound.certificate_bound gives Re trace(rho^2)<=8/169 for every literal four-by-six APPT density. The coordinate ray (I+2|00><00|)/26 has diagonal (3,1^23)/26, is positive semidefinite with trace one, remains PPT after every global unitary, and has purity (24+8)/26^2=8/169. Thus the four-by-six real purity supremum is attained at 8/169. This known application uses the baseline-frozen qutrit bound at fixed total dimension and requires no extra spectral certificate. It is an application exposition, not an independently new four-by-six result. The varying-total-dimension inference for length twenty is the separate insertion/deletion argument. Neither application describes all maximizers or establishes an unrestricted APPT theorem. The finite-corner construction belongs to this physical host because density_bound consumes spectral_reduction directly. Every construction lemma is a consumed bind-only helper; the host obtains its escape witness from the same-delivery new structural insertion/deletion transfer on its live upper-bound path, not from the corner packaging.

**Definition 1.3 (Normalized rank-one ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (v:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}),(normalizedRay\left(v\right)=\frac{1}{m\cdot n + 2}\cdot (1 + 2\cdot vecMulVec\left(v, star\left(v\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalizedRay` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For arbitrary natural local dimensions m,n and a complex vector v on their product, normalizedRay is (I+2|v><v|)/(mn+2). Scalar multiplication uses the real reciprocal embedded into the complex numbers.

**Theorem 1.4 (Density normalization and universal APPT of the ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (v:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}),((dotProduct\left(star\left(v\right), v\right)=1)\Rightarrow (((PosSemidef\left(normalizedRay\left(v\right)\right))\land (trace\left(normalizedRay\left(v\right)\right)=1))\land (APPT\left(normalizedRay\left(v\right)\right))\land (re\left(trace\left(normalizedRay\left(v\right)\cdot normalizedRay\left(v\right)\right)\right)=\frac{m\cdot n + 8}{(m\cdot n + 2)^{2}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The sole vector hypothesis is star(v) dot v=1. The normalized matrix is positive semidefinite, has complex trace exactly one, is APPT, and has real trace-square (mn+8)/(mn+2)^2. APPT quantifies over every global unitary on the full product space, with partial transpose on the second factor. A unitary sends v to another unit vector. LowRankRays.separableCone_one_add_two_rankOne makes I+2|Uv><Uv| separable; positive scaling and separableCone_partialTranspose_posSemidef give positivity after partial transpose. The rank-one square identity gives the trace-square formula. Dimensions with no unit vector are included conditionally, without an existence assumption.

**Theorem 1.5 (Diagonal representative of the ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (a:(Fin\left(m\right)\times Fin\left(n\right))),(normalizedRay\left(Pi.single\left(a, 1\right)\right)=diagonal\left((fun(i:(Fin\left(m\right)\times Fin\left(n\right)))\mapsto if(i=a)then\frac{3}{m\cdot n + 2}else\frac{1}{m\cdot n + 2})\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_basis_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For every coordinate a the normalized ray of its coordinate vector is diagonal, with one entry 3/(mn+2) at a and all other entries 1/(mn+2). This follows entrywise, including every off-diagonal entry.

**Definition 1.6 (Literal density-matrix extremum).**

$$claim\iff ((\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{7}{121})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{7}{121})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(5\right)))\mapsto if(i=(0,0))then\frac{3}{22}else\frac{1}{22})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{7}{121})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The three clauses assert the universal upper bound, the real supremum of the attainable purity set, and existence of the prescribed diagonal density. Every matrix is complex and indexed by Fin 4 times Fin 5. Positivity, trace one and APPT are actual matrix properties.

**Theorem 1.7 (Sharp literal four-by-five maximum).**

$$(\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{7}{121})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{7}{121})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(5\right)))\mapsto if(i=(0,0))then\frac{3}{22}else\frac{1}{22})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{7}{121}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For every positive semidefinite trace-one complex four-by-five matrix that remains PPT after every global unitary, Re trace(rho*rho) is at most 7/121. spectral_reduction supplies a single antitone nonnegative spectrum of length twenty, with mass one, both rank-three boundary matrices positive semidefinite, and exactly the same purity. Its boundary selector agrees with SpectralBoundaryTransfer.boundaryValues 11. DimensionTwentySpectralPurityBound applies the same-delivery new full insertion/deletion transfer from lengths eighteen and twenty-one through length nineteen. The normalized coordinate ray at (0,0) is the literal diagonal (3,1^19)/22; its trace is one, its purity is (20+8)/22^2=7/121, and the generic ray argument proves APPT after every global unitary. The attained upper bound gives the real supremum. Zero and repeated eigenvalues are permitted in the upper bound. No characterization of all maximizers, other dimensions, or unrestricted APPT purity theorem follows.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.cornerBoundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalizedRay`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_basis_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_ray`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.spectral_reduction`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound](DimensionTwentySpectralPurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency](QutritHildebrandSufficiency.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
