# Four-by-five APPT maximum purity

## Abstract

The maximum purity of a literal four-by-five APPT density matrix is 7/121.

**Definition 1.1 (Normalized rank-one ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (v:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}),(normalizedRay\left(v\right)=\frac{1}{m\cdot n + 2}\cdot (1 + 2\cdot vecMulVec\left(v, star\left(v\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalizedRay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural local dimensions m,n and a complex vector v on their product, normalizedRay is (I+2|v><v|)/(mn+2). Scalar multiplication uses the real reciprocal embedded into the complex numbers.

**Theorem 1.2 (Density normalization and universal APPT of the ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (v:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}),((dotProduct\left(star\left(v\right), v\right)=1)\Rightarrow (((PosSemidef\left(normalizedRay\left(v\right)\right))\land (trace\left(normalizedRay\left(v\right)\right)=1))\land (APPT\left(normalizedRay\left(v\right)\right))\land (re\left(trace\left(normalizedRay\left(v\right)\cdot normalizedRay\left(v\right)\right)\right)=\frac{m\cdot n + 8}{(m\cdot n + 2)^{2}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole vector hypothesis is star(v) dot v=1. The normalized matrix is positive semidefinite, has complex trace exactly one, is APPT, and has real trace-square (mn+8)/(mn+2)^2. APPT quantifies over every global unitary on the full product space, with partial transpose on the second factor. A unitary sends v to another unit vector. LowRankRays.separableCone_one_add_two_rankOne makes I+2|Uv><Uv| separable; positive scaling and separableCone_partialTranspose_posSemidef give positivity after partial transpose. The rank-one square identity gives the trace-square formula. Dimensions with no unit vector are included conditionally, without an existence assumption.

**Theorem 1.3 (Diagonal representative of the ray).**

$$\forall (m:Nat),(\forall (n:Nat),(\forall (a:(Fin\left(m\right)\times Fin\left(n\right))),(normalizedRay\left(Pi.single\left(a, 1\right)\right)=diagonal\left((fun(i:(Fin\left(m\right)\times Fin\left(n\right)))\mapsto if(i=a)then\frac{3}{m\cdot n + 2}else\frac{1}{m\cdot n + 2})\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_basis_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate a the normalized ray of its coordinate vector is diagonal, with one entry 3/(mn+2) at a and all other entries 1/(mn+2). This follows entrywise, including every off-diagonal entry.

**Definition 1.4 (Literal density-matrix extremum).**

$$claim\iff ((\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{7}{121})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{7}{121})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(5\right)))\mapsto if(i=(0,0))then\frac{3}{22}else\frac{1}{22})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{7}{121})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three clauses assert the universal upper bound, the real supremum of the attainable purity set, and existence of the prescribed diagonal density. Every matrix is complex and indexed by Fin 4 times Fin 5. Positivity, trace one and APPT are actual matrix properties.

**Theorem 1.5 (Sharp literal four-by-five maximum).**

$$(\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{7}{121})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{7}{121})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(5\right)), (Fin\left(4\right)\times Fin\left(5\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(5\right)))\mapsto if(i=(0,0))then\frac{3}{22}else\frac{1}{22})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{7}{121}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive semidefinite trace-one complex four-by-five matrix that remains PPT after every global unitary, Re trace(rho*rho) is at most 7/121. FiniteBellCorner.spectral_reduction supplies a single antitone nonnegative spectrum of length twenty, with mass one, both rank-three boundary matrices positive semidefinite, and exactly the same purity. Its boundary selector agrees with SpectralBoundaryTransfer.boundaryValues 11. DimensionTwentySpectralPurityBound applies the full insertion/deletion transfer from lengths eighteen and twenty-one through length nineteen. The normalized coordinate ray at (0,0) is the literal diagonal (3,1^19)/22; its trace is one, its purity is (20+8)/22^2=7/121, and the generic ray argument proves APPT after every global unitary. The attained upper bound gives the real supremum. Zero and repeated eigenvalues are permitted in the upper bound. No characterization of all maximizers, other dimensions, or unrestricted APPT purity theorem follows.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalizedRay`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_basis_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.normalized_ray`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound](DimensionTwentySpectralPurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner](FiniteBellCorner.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
