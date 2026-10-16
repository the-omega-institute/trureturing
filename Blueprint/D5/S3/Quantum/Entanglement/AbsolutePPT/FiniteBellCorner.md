# Finite product Bell-corner spectral reduction

## Abstract

All finite bipartite APPT density matrices with local dimensions at least three satisfy both qutrit Bell-corner constraints on the largest three and smallest six eigenvalues.

**Definition 1.1 (Nine extremal spectral coordinates).**

$$\forall (N:Nat), (9\leq N)\Rightarrow \forall (l:Fin\left(N\right)\to \mathbb{R}), \forall (q:Fin\left(9\right)), boundaryValues\left(N, l, q\right)=l\left((if val\left(q\right)<3 then val\left(q\right) else N-9+val\left(q\right):Fin\left(N\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner.boundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The total dimension N is at least nine, and the proof argument for that inequality is suppressed in the display. Indices are zero-based. The selector takes entries 0, 1, 2, N−6, N−5, N−4, N−3, N−2, N−1. The middle N−9 entries remain in the full packing, so trace and purity are preserved.

**Theorem 1.2 (Necessary spectral matrices in arbitrary finite local dimensions).**

$$\forall (m:Nat), \forall (n:Nat), ((3\leq m)\land (3\leq n))\Rightarrow \forall (rho:Matrix\left((Fin\left(m\right)\times Fin\left(n\right)), (Fin\left(m\right)\times Fin\left(n\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow \exists (l:Fin\left(m\cdot n\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(m\cdot n\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(m\cdot n\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(boundaryValues\left(m\cdot n, l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(boundaryValues\left(m\cdot n, l\right)\right)\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\sum_{i:Fin\left(m\cdot n\right)} (l\left(i\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner.spectral_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For all natural m,n at least three, every positive semidefinite trace-one complex matrix on Fin m × Fin n satisfying literal APPT has an antitone nonnegative spectrum l of length mn and mass one. The proof argument 9≤mn is suppressed in the displayed boundary selector. Both existing real matrices K1 and K2 evaluated on the nine extremal spectral coordinates are positive semidefinite, and Re trace(rho*rho) equals the sum of all mn spectral squares. Repeated and zero eigenvalues are included. Embed Fin 3 into each local factor. Their product c has a finite complement, identified with Fin(mn−9) by cardinality. Extend the Bell unitary and its swapped partner by identity on this complement. Partial transpose commutes with compression along this product: both entries at (i,j),(k,l) equal rho(c(i,l),c(k,j)). The existing Bell principal identity then gives the two necessary matrices. Ordered spectral diagonalization uses an arbitrary global packing only as a unitary conjugation; it assumes no partial-transpose covariance of that packing. These conditions are necessary and do not assert APPT sufficiency. At mn=24 the boundary equals QutritSpectralReduction.boundaryValues 5 and permits direct use of the existing dimension-24 sharp certificate. Hildebrand Theorem 2, PDF page 5 of quant-ph/0502170, already gives APPT 4×6→3×8 at fixed total dimension 24, so the qutrit maximum and established attaining ray imply the 4×6 scalar value. At total dimension twenty, the selector is SpectralBoundaryTransfer.boundaryValues 11. The length-twenty bound follows by the full rank-three insertion/deletion theorem from endpoint lengths eighteen and twenty-one, first reaching nineteen and then twenty. For the four-by-five product, the normalized coordinate ray (I+2|00><00|)/22 is exactly diagonal (3,1^19)/22. Its trace is one and its trace-square is (20+8)/22^2=7/121. For any global unitary U, the unit vector U|00> yields a separable numerator by LowRankRays.separableCone_one_add_two_rankOne; positive normalization and separableCone_partialTranspose_posSemidef imply APPT. At total dimension twenty-four, the same argument combined directly with QutritN8PurityBound.certificate_bound gives Re trace(rho^2)<=8/169 for every literal four-by-six APPT density. The coordinate ray (I+2|00><00|)/26 has diagonal (3,1^23)/26, is positive semidefinite with trace one, remains PPT after every global unitary, and has purity (24+8)/26^2=8/169. Thus the four-by-six real purity supremum is attained at 8/169. This application uses the existing qutrit bound at fixed total dimension and requires no extra spectral certificate. The varying-total-dimension inference for length twenty is the separate insertion/deletion argument. Neither application describes all maximizers or establishes an unrestricted APPT theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner.boundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner.spectral_reduction`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency](QutritHildebrandSufficiency.md)
