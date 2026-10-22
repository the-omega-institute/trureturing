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

**Definition 1.16 (Bell change of basis).**

$$\forall (i:Fin\left(3\right)), \forall (j:Fin\left(3\right)), \forall (k:Fin\left(3\right)), \forall (l:Fin\left(3\right)), bell\left((i,j), (k,l)\right)=if i=j then if (i,j)=(k,l) then 1 else 0 else if (i,j)=(k,l) then if i<j then (Real.sqrt\left(2\right):\mathbb{C})^{-1} else -(Real.sqrt\left(2\right):\mathbb{C})^{-1} else if (i,j)=(l,k) then (Real.sqrt\left(2\right):\mathbb{C})^{-1} else 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Diagonal tensor coordinates are fixed. Each pair of off-diagonal tensor coordinates is changed to its symmetric and antisymmetric combinations with coefficient one over the square root of two.

**Theorem 1.17 (The Bell basis matrix is unitary).**

$$bell\in unitaryGroup\left((Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell_mem_unitaryGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bell basis matrix is unitary. Its diagonal entries fix the diagonal basis vectors, while each off-diagonal pair is rotated by the reciprocal square root of two. Spectral reduction and the diagonalization of a pure state's partial transpose use this change of basis.

**Definition 1.18 (Packing nine spectral coordinates).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), \forall (i:Fin\left(3\right)), \forall (j:Fin\left(3\right)), pack\left(l, (i,j)\right)=(if i=0 then if j=0 then l\left(8\right) else if j=1 then l\left(7\right) else l\left(5\right) else if i=1 then if j=0 then l\left(0\right) else if j=1 then l\left(6\right) else l\left(4\right) else if j=0 then l\left(1\right) else if j=1 then l\left(2\right) else l\left(3\right):\mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nine real values are packed into the local product corner with rows (l8,l7,l5), (l0,l6,l4), (l1,l2,l3), and then cast to complex numbers. This arrangement is chosen for its Bell partial transpose.

**Definition 1.19 (Complex first boundary matrix).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), KC1\left(l\right)=Matrix.map\left(Complex.ofReal, K1\left(l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex matrix is the entrywise real-to-complex cast of K1. Its concrete entries are also used by the Bell computation; KC1_map proves the displayed identification.

**Theorem 1.20 (Bell partial-transpose compression).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), Matrix.submatrix\left(partialTranspose\left(bell\cdot Matrix.diagonal\left(pack\left(l\right)\right)\cdot (bell)^{H}\right), (fun i \mapsto (i,i)), (fun i \mapsto (i,i))\right)=(\frac{1}{2}:\mathbb{C})\cdot KC1\left(l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell_pt_principal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The principal submatrix on the three diagonal product coordinates of the Bell-conjugated packed diagonal is one half of KC1. The four-by-four bridge reuses this exact calculation on a genuine local product corner.

**Definition 1.21 (The two middle corner positions are swapped).**

$$swap56=Equiv.swap\left((1,1), (0,2)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.swap56` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corner permutation exchanges product positions (1,1) and (0,2), fixing every other position. Its permutation unitary implements the swap needed for the second spectral matrix.

**Definition 1.22 (Swapping spectral values five and six).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), \forall (q:Fin\left(9\right)), flip56\left(l, q\right)=l\left(Equiv.swap\left(5, 6, q\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.flip56` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function precomposes the nine-coordinate spectrum with the transposition of indices 5 and 6. All other boundary coordinates remain fixed.

**Theorem 1.23 (The corner permutation realizes the spectral swap).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), permutationU\left(swap56\right)\cdot Matrix.diagonal\left(pack\left(l\right)\right)\cdot (permutationU\left(swap56\right))^{H}=Matrix.diagonal\left(pack\left(flip56\left(l\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.swap_pack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the packed diagonal by the specified corner permutation unitary gives the packed diagonal for flip56. This is the common computation used to derive the second boundary constraint.

**Definition 1.24 (Complex second boundary matrix).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), KC2\left(l\right)=KC1\left(flip56\left(l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second complex boundary matrix is KC1 after exchanging spectral indices 5 and 6. KC2_map identifies it with the complex cast of K2.

**Theorem 1.25 (The first complex-to-real identification).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), KC1\left(l\right)=Matrix.map\left(Complex.ofReal, K1\left(l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC1_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first concrete complex Bell matrix is the entrywise cast of the real first boundary matrix. This allows positive semidefiniteness to descend to the certificate coordinates.

**Theorem 1.26 (The second complex-to-real identification).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), KC2\left(l\right)=Matrix.map\left(Complex.ofReal, K2\left(l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC2_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The swapped complex Bell matrix is the entrywise cast of the real second boundary matrix. The identity is checked on all three-by-three entries.

**Theorem 1.27 (APPT descends through unitary conjugation).**

$$\forall (A:Type), [Fintype\left(A\right)] [DecidableEq\left(A\right)] \forall (B:Type), [Fintype\left(B\right)] [DecidableEq\left(B\right)] \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), \forall (V:unitaryGroup\left((A\times B), \mathbb{C}\right)), (APPT\left((V:Matrix\left((A\times B), (A\times B), \mathbb{C}\right))\cdot M\cdot ((V:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)))^{H}\right))\Rightarrow APPT\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.appt_unconjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a unitary conjugate is APPT, the original matrix is APPT. The inverse unitary cancels the conjugation and the already proved conjugation invariance applies.

**Theorem 1.28 (Unitary conjugation preserves trace-square).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (M:Matrix\left(I, I, \mathbb{C}\right)), \forall (V:unitaryGroup\left(I, \mathbb{C}\right)), Matrix.trace\left((V:Matrix\left(I, I, \mathbb{C}\right))\cdot M\cdot ((V:Matrix\left(I, I, \mathbb{C}\right)))^{H}\cdot (V:Matrix\left(I, I, \mathbb{C}\right))\cdot M\cdot ((V:Matrix\left(I, I, \mathbb{C}\right)))^{H}\right)=Matrix.trace\left(M\cdot M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.unitary_purity_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of the square is unchanged by unitary conjugation over any finite index type. This is an algebraic statement; no positivity or trace normalization is assumed.

**Theorem 1.29 (Unitary conjugation preserves trace).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (M:Matrix\left(I, I, \mathbb{C}\right)), \forall (V:unitaryGroup\left(I, \mathbb{C}\right)), Matrix.trace\left((V:Matrix\left(I, I, \mathbb{C}\right))\cdot M\cdot ((V:Matrix\left(I, I, \mathbb{C}\right)))^{H}\right)=Matrix.trace\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.unitary_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace is unchanged by unitary conjugation over any finite index type. The cyclic trace identity and the unitary inverse establish the equality.

**Definition 1.30 (The corner packing index map).**

$$\forall (i:Fin\left(3\right)), \forall (j:Fin\left(3\right)), packIndex\left((i,j)\right)=if i=0 then if j=0 then 8 else if j=1 then 7 else 5 else if i=1 then if j=0 then 0 else if j=1 then 6 else 4 else if j=0 then 1 else if j=1 then 2 else 3$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.packIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite index map has rows (8,7,5), (0,6,4), (1,2,3). It specifies which of the nine boundary coordinates occupies each product position.

**Definition 1.31 (The corner packing equivalence).**

$$\forall (p:(Fin\left(3\right)\times Fin\left(3\right))), packEquiv\left(p\right)=packIndex\left(p\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.packEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The packing index map is a bijection from the three-by-three corner to the nine boundary indices. Its underlying map is packIndex, so it can be composed with the complement packing for the complete ordered spectrum.

**Theorem 1.32 (Density-to-spectral-certificate reduction).**

$$\forall (k:\mathbb{N}), \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3+k\right)), (Fin\left(3\right)\times Fin\left(3+k\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow \exists (l:Fin\left(3\cdot (3+k)\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(3\cdot (3+k)\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(3\cdot (3+k)\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(boundaryValues\left(k, l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(boundaryValues\left(k, l\right)\right)\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\sum_{i:Fin\left(3\cdot (3+k)\right)} (l\left(i\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.spectral_reduction` (`✓ std3`). ∎

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For every k and every positive semidefinite trace-one Matrix on Fin 3 × Fin (3+k), literal APPT yields antitone nonnegative real certificate coordinates with mass one, both positive boundary matrices, and the same real trace-square. The public conclusion does not identify these coordinates with rho's eigenvalues; the proof chooses sorted eigenvalues. The proof constructs Bell and permutation unitaries, compresses their partial transposes, and sorts the eigenvalues. This is the necessary direction of Hildebrand, Corollary 4, pages 5–6, together with the standard trace identities.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.K2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC1_map`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.KC2_map`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.appt_unconjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell_mem_unitaryGroup`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell_pt_principal`
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
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.flip56`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.pack`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.packEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.packIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_int_scaled_ldl`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.psd_of_rat_ldl`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.spectral_reduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.swap56`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.swap_pack`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.unitary_purity_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.unitary_trace`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT](GenericAPPT.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](QutritPerturbationAttainment.md)
