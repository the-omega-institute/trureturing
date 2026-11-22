# Weighted label records with a finite pure environment

## Abstract

The exact weighted readout optimum with a prescribed pure environment.

**Theorem 1.1 (Exact optimum and a product-cell realization).**

$$\begin{aligned}\forall B,J \in \operatorname{FiniteTypes},d,e \in \mathbb{N},c \in \operatorname{Map}\left(B, J\right),p \in \operatorname{Map}\left(B, \mathbb{R}\right),\\\operatorname{Nonempty}\left(J\right) \land 0 < e \land \operatorname{card}\left(B\right) \leq d \cdot e \land \operatorname{prior}\left(p\right) \Rightarrow\\(\forall V \in \operatorname{EncoderMatrices}\left(B, \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)\right),E \in \operatorname{EffectFamilies}\left(J, \operatorname{Fin}\left(d\right)\right),\operatorname{isometry}\left(V\right) \land \operatorname{POVM}\left(E, J\right) \Rightarrow \operatorname{S}\left(c, p, V, E\right) \leq \operatorname{O}\left(c, p, d, e\right)) \land\\(\exists g \in \operatorname{Embedding}\left(B, \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)\right),r \in \operatorname{Map}\left(\operatorname{Fin}\left(d\right), J\right),\operatorname{isometry}\left(V_{g}\right) \land \operatorname{PVM}\left(E_{r}, J\right) \land \operatorname{S}\left(c, p, V_{g}, E_{r}\right) = \operatorname{O}\left(c, p, d, e\right)) \land\\(\operatorname{O}\left(c, p, d, e\right) = 1 \iff \operatorname{memorySlots}\left(c, p, e\right) \leq d)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.weightedLabelRecord_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Noam Elron and Yonina C. Eldar (2007). *Optimal encoding of classical information in a quantum medium*. DOI: [10.1109/TIT.2006.894686](https://doi.org/10.1109/TIT.2006.894686). URL: <https://arxiv.org/abs/quant-ph/0601010v2>.

*Acknowledgement.* Péter E. Frenkel (2022). *Classical simulations of communication channels*. DOI: [10.22331/q-2022-06-29-751](https://doi.org/10.22331/q-2022-06-29-751). URL: <https://arxiv.org/abs/2101.10985v4>.

*Acknowledgement.* Fabien Clivaz, Ralph Silva, Géraldine Haack, Jonatan Bohr Brask, Nicolas Brunner and Marcus Huber (2019). *Unifying paradigms of quantum refrigeration: A universal and attainable bound on cooling*. DOI: [10.1103/PhysRevLett.123.170605](https://doi.org/10.1103/PhysRevLett.123.170605). URL: <https://arxiv.org/abs/1903.04970v2>.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Acknowledgement.* Anna Jenčová and Dénes Petz (2006). *Sufficiency in Quantum Statistical Inference*. DOI: [10.1007/s00220-005-1510-7](https://doi.org/10.1007/s00220-005-1510-7). URL: <https://arxiv.org/abs/math-ph/0412093v1>.

*Commentary.*

Let B be a finite input basis, J a nonempty finite label set, c a label map, and p a nonnegative prior of total mass one. The memory and pure environment have dimensions d and e, with e positive and the entire input basis fitting in d times e product cells. The score S is the prior-weighted trace pairing of the effect for c(b) with the environment-reduced column at each b.

For each label, sort the priors of that label in decreasing order and pad with zeros to length d times e. Sum each consecutive block of e entries. The value O is the sum of the d largest block masses across all labels. Every isometric encoder V and every positive semidefinite effect family E summing to the memory identity has score at most O.

For each label, rectangular characteristic polynomial commutation gives the spectrum of the encoded prior diagonal with zero padding. Tensoring an effect with the environment identity repeats each of its eigenvalues e times. Von Neumann's trace inequality bounds each label's score by the scalar product of its block masses and decreasing effect eigenvalues. The effect eigenvalues lie in the unit interval and sum to d across the POVM.

Assign the chosen blocks distinct memory rows, and pack each selected input into the environment coordinate of its block. Extend this injection to all basis vectors, including those with prior zero. The encoder Vg has the single unit entry at g(b) in column b. The effect Er(j) is the diagonal projector onto rows whose readout label r is j. These effects are positive semidefinite, sum to the identity, square to themselves, and have zero pairwise products for distinct labels.

The endpoint uses the existing perfect label record criterion on the positive-prior support. The slot cost is the sum of the class sizes on that support divided by e and rounded up separately for each label.

Elron and Eldar Theorem 2 optimizes independently selectable code states. Frenkel Theorem 2.4 supplies the classical simulation under separate spectral constraints. Clivaz et al. Appendix Lemma 4 and Eq. (43) give the environment-sized spectral blocks. The attaining construction here packs the chosen blocks into one isometry on the original basis. Kato, Koashi and Imoto, and Jencova and Petz provide the exact compression and sufficiency context of the perfect-readout criterion.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.weightedLabelRecord_optimum`
- Dependency: [D5/S3/Quantum/Measurements/FiniteLabelRecordDilation](FiniteLabelRecordDilation.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordSpectralMemory](../PureState/PhaseRecordSpectralMemory.md)
