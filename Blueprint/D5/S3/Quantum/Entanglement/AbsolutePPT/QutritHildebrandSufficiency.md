# Hildebrand sufficiency on two qutrits

## Abstract

The two Hildebrand pencils characterize absolutely PPT density matrices on two qutrits.

**Theorem 1.1 (Ordered spectral necessity).**

$$\forall (k:\mathbb{N}), \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3+k\right)), (Fin\left(3\right)\times Fin\left(3+k\right)), \mathbb{C}\right)), \forall (hrho:(rho).PosSemidef), (((rho).trace=1)\land (APPT\left(rho\right)))\Rightarrow (\exists (l:Fin\left(3\cdot (3+k)\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(3\cdot (3+k)\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(3\cdot (3+k)\right)} l\left(i\right)=1)\land ((K1\left(boundaryValues\left(k, l\right)\right)).PosSemidef)\land ((K2\left(boundaryValues\left(k, l\right)\right)).PosSemidef)\land (((rho\cdot rho).trace).re=\sum_{i:Fin\left(3\cdot (3+k)\right)} (l\left(i\right))^{2})\land (l=(fun (i:Fin\left(3\cdot (3+k)\right)) \mapsto hrho.isHermitian.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.spectral_reduction_ordered` (`✓ std3`). ∎

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The eigenvalues are the sorted eigenvalues chosen in the spectral reduction. The proof argument of Fin.cast is omitted; it is the cardinality equality for Fin 3 × Fin (3+k).

**Theorem 1.2 (Spectrum as an ordered range).**

$$\forall (k:\mathbb{N}), \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3+k\right)), (Fin\left(3\right)\times Fin\left(3+k\right)), \mathbb{C}\right)), \forall (H:Matrix.IsHermitian\left(rho\right)), spectrum\left(\mathbb{C}, rho\right)=Set.image\left(Complex.ofReal, Set.range\left((fun (i:Fin\left(3\cdot (3+k)\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.spectrum_eq_ordered_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex spectrum is the real embedding of the range of the sorted eigenvalues. The proof argument of Fin.cast is omitted; it is the cardinality equality for Fin 3 × Fin (3+k).

**Theorem 1.3 (Trace and squared unitary entries).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (w:I\to \mathbb{R}), \forall (l:I\to \mathbb{R}), \forall (U:unitaryGroup\left(I, \mathbb{C}\right)), ((Matrix.diagonal\left((fun (i:I) \mapsto (w\left(i\right):\mathbb{C}))\right)\cdot (U:Matrix\left(I, I, \mathbb{C}\right))\cdot Matrix.diagonal\left((fun (i:I) \mapsto (l\left(i\right):\mathbb{C}))\right)\cdot Matrix.conjTranspose\left((U:Matrix\left(I, I, \mathbb{C}\right))\right)).trace).re=\sum_{i:I} \sum_{j:I} w\left(i\right)\cdot RHLinalg.normSqMatrix\left((U:Matrix\left(I, I, \mathbb{C}\right)), i, j\right)\cdot l\left(j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.trace_diagonal_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion of the trace gives the finite sum with squared moduli of the unitary entries.

**Theorem 1.4 (Trace lower bound).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (w:I\to \mathbb{R}), \forall (l:I\to \mathbb{R}), \forall (U:unitaryGroup\left(I, \mathbb{C}\right)), (Monovary\left((fun (i:I) \mapsto -w\left(i\right)), l\right))\Rightarrow (\sum_{i:I} w\left(i\right)\cdot l\left(i\right)\leq ((Matrix.diagonal\left((fun (i:I) \mapsto (w\left(i\right):\mathbb{C}))\right)\cdot (U:Matrix\left(I, I, \mathbb{C}\right))\cdot Matrix.diagonal\left((fun (i:I) \mapsto (l\left(i\right):\mathbb{C}))\right)\cdot Matrix.conjTranspose\left((U:Matrix\left(I, I, \mathbb{C}\right))\right)).trace).re)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.trace_lower_of_monovary_diagonalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Oppositely ordered weights give a lower bound for the trace of the conjugated diagonal operator.

**Theorem 1.5 (Sorted diagonalization).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (n:\mathbb{N}), \forall (hc:Fintype.card\left(I\right)=n), \forall (A:Matrix\left(I, I, \mathbb{C}\right)), \forall (H:Matrix.IsHermitian\left(A\right)), \forall (e:Equiv\left(I, Fin\left(n\right)\right)), \exists (U:unitaryGroup\left(I, \mathbb{C}\right)), A=(U:Matrix\left(I, I, \mathbb{C}\right))\cdot Matrix.diagonal\left((fun (i:I) \mapsto ((fun (i:Fin\left(n\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(hc.symm, i\right)\right))\left(e\left(i\right)\right):\mathbb{C}))\right)\cdot Matrix.conjTranspose\left((U:Matrix\left(I, I, \mathbb{C}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_diagonalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unitary conjugates the diagonal matrix indexed by the chosen equivalence to the Hermitian matrix.

**Theorem 1.6 (Descending eigenvalues).**

$$\forall (J:Type), [Fintype\left(J\right)] [DecidableEq\left(J\right)] \forall (n:\mathbb{N}), \forall (hc:Fintype.card\left(J\right)=n), \forall (A:Matrix\left(J, J, \mathbb{C}\right)), \forall (H:Matrix.IsHermitian\left(A\right)), Antitone\left((fun (i:Fin\left(n\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(hc.symm, i\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_eigenvalues_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing by the cardinality equality preserves descending order.

**Theorem 1.7 (Hildebrand sufficiency).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), \forall (H:Matrix.IsHermitian\left(rho\right)), (((K1\left((fun (i:Fin\left(9\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))\right)).PosSemidef)\land ((K2\left((fun (i:Fin\left(9\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))\right)).PosSemidef))\Rightarrow (APPT\left(rho\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.hildebrand_sufficiency` (`✓ std3`). ∎

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

Positivity of both real pencils implies positivity of every partial transpose after unitary conjugation. Hildebrand, Corollary 4, pages 5–6. Fin.cast omits the proof of the carrier cardinality equality.

**Theorem 1.8 (Two-qutrit boundary coordinates).**

$$\forall (l:Fin\left(9\right)\to \mathbb{R}), boundaryValues\left(0, l\right)=l$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.boundary_values_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both local dimensions are three, all nine boundary coordinates are unchanged.

**Theorem 1.9 (Hildebrand equivalence).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), \forall (hp:(rho).PosSemidef), ((rho).trace=1)\Rightarrow (APPT\left(rho\right)\iff ((K1\left((fun (i:Fin\left(9\right)) \mapsto hp.isHermitian.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))\right)).PosSemidef)\land ((K2\left((fun (i:Fin\left(9\right)) \mapsto hp.isHermitian.eigenvalues_{0}\left(Fin.cast\left(i\right)\right))\right)).PosSemidef))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.hildebrand_criterion` (`✓ std3`). ∎

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For a positive trace-one matrix, absolute PPT is equivalent to positivity of both Hildebrand pencils. Hildebrand, Corollary 4, pages 5–6. Fin.cast omits the proof of the carrier cardinality equality.

**Theorem 1.10 (Identification of sorted diagonal entries).**

$$\forall (J:Type), [Fintype\left(J\right)] [DecidableEq\left(J\right)] \forall (n:\mathbb{N}), \forall (hc:Fintype.card\left(J\right)=n), \forall (A:Matrix\left(J, J, \mathbb{C}\right)), \forall (H:Matrix.IsHermitian\left(A\right)), \forall (l:Fin\left(n\right)\to \mathbb{R}), \forall (e:Equiv\left(J, Fin\left(n\right)\right)), \forall (U:unitaryGroup\left(J, \mathbb{C}\right)), ((Antitone\left(l\right))\land (A=(U:Matrix\left(J, J, \mathbb{C}\right))\cdot Matrix.diagonal\left((fun (i:J) \mapsto (l\left(e\left(i\right)\right):\mathbb{C}))\right)\cdot Matrix.conjTranspose\left((U:Matrix\left(J, J, \mathbb{C}\right))\right)))\Rightarrow ((fun (i:Fin\left(n\right)) \mapsto H.eigenvalues_{0}\left(Fin.cast\left(hc.symm, i\right)\right))=l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_eigenvalues_of_diagonalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An antitone diagonal list in a unitary diagonalization equals the sorted eigenvalues.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.boundary_values_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.hildebrand_criterion`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.hildebrand_sufficiency`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_diagonalization`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_eigenvalues_antitone`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.sorted_eigenvalues_of_diagonalization`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.spectral_reduction_ordered`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.spectrum_eq_ordered_range`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.trace_diagonal_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency.trace_lower_of_monovary_diagonalization`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
