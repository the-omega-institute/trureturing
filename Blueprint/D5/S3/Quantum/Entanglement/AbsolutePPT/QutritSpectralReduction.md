# Qutrit spectral reduction

## Abstract

Literal qutrit APPT states yield ordered nonnegative spectral certificate coordinates constrained by both boundary LMIs.

**Definition 1.1 (Rational matrix cast).**

$$\forall (I:Type), \forall (J:Type), \forall (A:Matrix\left(I, J, \mathbb{Q}\right)), \forall (i:I), \forall (j:J), castMat\left(A, i, j\right)=(Rat.cast\left(A\left(i, j\right)\right):\mathbb{R})$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entrywise rational-to-real map preserves the row and column types.

**Definition 1.2 (Integer matrix cast).**

$$\forall (I:Type), \forall (J:Type), \forall (A:Matrix\left(I, J, \mathbb{Z}\right)), \forall (i:I), \forall (j:J), castIntMat\left(A, i, j\right)=(Int.cast\left(A\left(i, j\right)\right):\mathbb{R})$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entrywise integer-to-real map preserves the row and column types.

**Theorem 1.3 (Rational casts preserve matrix products).**

$$\forall (I:Type), \forall (J:Type), \forall (K:Type), [Fintype\left(J\right)] \forall (A:Matrix\left(I, J, \mathbb{Q}\right)), \forall (B:Matrix\left(J, K, \mathbb{Q}\right)), castMat\left(A\cdot B\right)=castMat\left(A\right)\cdot castMat\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite inner index permits entrywise casting of the finite product sum.

**Theorem 1.4 (Rational transpose cast).**

$$\forall (I:Type), \forall (J:Type), \forall (A:Matrix\left(I, J, \mathbb{Q}\right)), castMat\left(Matrix.transpose\left(A\right)\right)=(castMat\left(A\right))^{H}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real conjugation is trivial, so the cast transpose is the conjugate transpose.

**Theorem 1.5 (Rational diagonal cast).**

$$\forall (I:Type), [DecidableEq\left(I\right)] \forall (d:I\to \mathbb{Q}), castMat\left(Matrix.diagonal\left(d\right)\right)=Matrix.diagonal\left((fun (i:I) \mapsto (Rat.cast\left(d\left(i\right)\right):\mathbb{R}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting preserves each diagonal entry and the zero off-diagonal entries.

**Theorem 1.6 (Integer casts preserve matrix products).**

$$\forall (I:Type), \forall (J:Type), \forall (K:Type), [Fintype\left(J\right)] \forall (A:Matrix\left(I, J, \mathbb{Z}\right)), \forall (B:Matrix\left(J, K, \mathbb{Z}\right)), castIntMat\left(A\cdot B\right)=castIntMat\left(A\right)\cdot castIntMat\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite inner index permits entrywise casting of the finite product sum.

**Theorem 1.7 (Integer transpose cast).**

$$\forall (I:Type), \forall (J:Type), \forall (A:Matrix\left(I, J, \mathbb{Z}\right)), castIntMat\left(Matrix.transpose\left(A\right)\right)=(castIntMat\left(A\right))^{H}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real conjugation is trivial, so the cast transpose is the conjugate transpose.

**Theorem 1.8 (Integer diagonal cast).**

$$\forall (I:Type), [DecidableEq\left(I\right)] \forall (d:I\to \mathbb{Z}), castIntMat\left(Matrix.diagonal\left(d\right)\right)=Matrix.diagonal\left((fun (i:I) \mapsto (Int.cast\left(d\left(i\right)\right):\mathbb{R}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting preserves each diagonal entry and the zero off-diagonal entries.

**Theorem 1.9 (Positive rational LDL factorization).**

$$\forall (I:Type), \forall (J:Type), [Fintype\left(J\right)] [DecidableEq\left(J\right)] [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (A:Matrix\left(I, I, \mathbb{Q}\right)), \forall (L:Matrix\left(I, J, \mathbb{Q}\right)), \forall (d:J\to \mathbb{Q}), ((A=L\cdot Matrix.diagonal\left(d\right)\cdot Matrix.transpose\left(L\right))\land (\forall (j:J), 0\leq d\left(j\right)))\Rightarrow Matrix.PosSemidef\left(castMat\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_rat_ldl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative rational diagonal entries give a positive semidefinite real diagonal matrix. Conjugation by the cast rectangular factor preserves positivity. The finite-sector bounds apply this criterion to their rational matrices.

**Theorem 1.10 (Positive scaled integer LDL factorization).**

$$\forall (I:Type), \forall (J:Type), [Fintype\left(J\right)] [DecidableEq\left(J\right)] [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (A:Matrix\left(I, I, \mathbb{Q}\right)), \forall (AI:Matrix\left(I, I, \mathbb{Z}\right)), \forall (L:Matrix\left(I, J, \mathbb{Z}\right)), \forall (d:J\to \mathbb{Z}), \forall (s:\mathbb{Z}), ((\forall (i:I), \forall (j:I), A\left(i, j\right)=\frac{(Int.cast\left(AI\left(i, j\right)\right):\mathbb{Q})}{(Int.cast\left(s\right):\mathbb{Q})})\land (AI=L\cdot Matrix.diagonal\left(d\right)\cdot Matrix.transpose\left(L\right))\land (\forall (j:J), 0\leq d\left(j\right))\land (0<s))\Rightarrow Matrix.PosSemidef\left(castMat\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_int_scaled_ldl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer LDL factorization with nonnegative diagonal entries is positive semidefinite after casting. Division by a positive integer scale preserves positivity. The finite-sector bounds apply this criterion to their scaled integer Gram matrices.

**Theorem 1.11 (Cast of a vector constructor).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{Q}), \forall (v:Fin\left(n\right)\to \mathbb{Q}), (fun (i:Fin\left(n+1\right)) \mapsto (Rat.cast\left(Matrix.vecCons\left(x, v\right)\left(i\right)\right):\mathbb{R}))=Matrix.vecCons\left((Rat.cast\left(x\right):\mathbb{R}), (fun (i:Fin\left(n\right)) \mapsto (Rat.cast\left(v\left(i\right)\right):\mathbb{R}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.cast_vec_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting a rational vector with an initial coordinate gives the real vector constructor with both pieces cast.

**Theorem 1.12 (Cast of the empty vector).**

$$(fun (i:Fin\left(0\right)) \mapsto (Rat.cast\left((Matrix.vecEmpty:Fin\left(0\right)\to \mathbb{Q})\left(i\right)\right):\mathbb{R}))=(Matrix.vecEmpty:Fin\left(0\right)\to \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.cast_vec_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cast empty rational vector equals the empty real vector.

**Definition 1.13 (First qutrit boundary matrix).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), K1\left(l\right)=!![2\cdot l\left(8\right),l\left(7\right)-l\left(0\right),l\left(5\right)-l\left(1\right);l\left(7\right)-l\left(0\right),2\cdot l\left(6\right),l\left(4\right)-l\left(2\right);l\left(5\right)-l\left(1\right),l\left(4\right)-l\left(2\right),2\cdot l\left(3\right)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K1` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The argument l has nine boundary values, in descending spectral order: the largest three and the smallest six. Indices are zero-based. This is the first real symmetric qutrit LMI in Hildebrand's spectral criterion (Equation (5), pages 5–6).

**Definition 1.14 (Second qutrit boundary matrix).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), K2\left(l\right)=!![2\cdot l\left(8\right),l\left(7\right)-l\left(0\right),l\left(6\right)-l\left(1\right);l\left(7\right)-l\left(0\right),2\cdot l\left(5\right),l\left(4\right)-l\left(2\right);l\left(6\right)-l\left(1\right),l\left(4\right)-l\left(2\right),2\cdot l\left(3\right)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K2` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The second qutrit LMI interchanges boundary indices 5 and 6 relative to K1. All matrix entries are real.

**Definition 1.15 (Boundary spectral coordinates).**

$$\forall (k:\mathbb{N}), \forall (l:Fin\left(3\cdot (3+k)\right)\to \mathbb{R}), \forall (q:Fin\left(9\right)), boundaryValues\left(k, l, q\right)=l\left((if val\left(q\right)<3 then val\left(q\right) else 3\cdot k+val\left(q\right):Fin\left(3\cdot (3+k)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.boundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent Fin constructor carries the displayed natural-number index and its bound proof. The first three coordinates are unchanged; the remaining six have index 3k+q. Here n=3+k, and the full dimension is 3(3+k).

**Theorem 1.16 (Density-to-spectral-certificate reduction).**

$$\forall (k:\mathbb{N}), \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3+k\right)), (Fin\left(3\right)\times Fin\left(3+k\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow \exists (l:Fin\left(3\cdot (3+k)\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(3\cdot (3+k)\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(3\cdot (3+k)\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(boundaryValues\left(k, l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(boundaryValues\left(k, l\right)\right)\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\sum_{i:Fin\left(3\cdot (3+k)\right)} (l\left(i\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.spectral_reduction` (`✓ std3`). ∎

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For every k and every positive semidefinite trace-one Matrix on Fin 3 × Fin (3+k), literal APPT yields antitone nonnegative real certificate coordinates with mass one, both positive boundary matrices, and the same real trace-square. The public conclusion does not identify these coordinates with rho's eigenvalues; the proof chooses sorted eigenvalues. The proof constructs Bell and permutation unitaries, compresses their partial transposes, and sorts the eigenvalues. This is the necessary direction of Hildebrand, Corollary 4, pages 5–6, together with the standard trace identities.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.boundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_mul`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castIntMat_transpose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_mul`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.castMat_transpose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.cast_vec_cons`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.cast_vec_empty`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_int_scaled_ldl`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_rat_ldl`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.spectral_reduction`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](QutritPerturbationAttainment.md)
