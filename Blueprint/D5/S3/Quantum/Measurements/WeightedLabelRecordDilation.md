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

**Theorem 1.2 (Exact uniform success from full blocks and remainders).**

$$\begin{aligned}\operatorname{FiniteTypes}\left(B, J\right) \land \operatorname{Nonempty}\left(B\right) \land c \in \operatorname{Map}\left(B, J\right) \land 0 < e \land N \leq d \cdot e \Rightarrow\\N \cdot \operatorname{O}\left(c, u, d, e\right) = e \cdot \operatorname{K}\left(c, e\right) + \operatorname{R}\left(c, e, d - \operatorname{K}\left(c, e\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.uniform_optimalSuccess_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Noam Elron and Yonina C. Eldar (2007). *Optimal encoding of classical information in a quantum medium*. DOI: [10.1109/TIT.2006.894686](https://doi.org/10.1109/TIT.2006.894686). URL: <https://arxiv.org/abs/quant-ph/0601010v2>.

*Acknowledgement.* Ryo Nomura and Te Sun Han (2012). *Second-Order Resolvability, Intrinsic Randomness, and Fixed-Length Source Coding for Mixed Sources: Information Spectrum Approach*. DOI: [10.1109/TIT.2012.2215836](https://doi.org/10.1109/TIT.2012.2215836). URL: <https://arxiv.org/abs/1106.1879v4>.

*Commentary.*

Let B be a nonempty finite input basis and J a finite set of labels, with c from B to J. Write N for the basis cardinality and m_j for the size of the fibre over j, which may be zero. The prior u assigns 1/N to every basis word. Take positive e and N at most d times e. The optimum O is the same common-isometry, arbitrary-POVM optimum above.

Write K for the sum of the integer quotients m_j divided by e. R(c,e,k) sums the largest k residues m_j modulo e, padding with zeros. The positive uniform weights form a prefix of each sorted padded list. Every full block strictly outweighs each remainder and K is at most d. After the full blocks, at most one positive block from each class competes for the remaining slots.

The weighted block theorem above supplies the operational optimum. Elron and Eldar Theorem 2 treats separately prepared code states. Nomura and Han Section VII gives classical fixed-length information-spectrum bounds. Publication priority for the combination of full-input isometry, fixed environment, and classwise remainder allocation is open.

**Theorem 1.3 (Necessary and sufficient memory bounds from a minimum class cover).**

$$\begin{aligned}\operatorname{FiniteTypes}\left(B, J\right) \land \operatorname{Nonempty}\left(B\right) \land c \in \operatorname{Map}\left(B, J\right) \land 0 < e \land N \leq d \cdot e \Rightarrow\\\operatorname{MinimumCover}\left(c, \alpha, M\right) \Rightarrow\\(\operatorname{Reaches}\left(\alpha, d, e, c\right) \Rightarrow \max\left(\operatorname{ceil}\left(N/e\right), \operatorname{K}\left(c, e\right) + M - \operatorname{FullLabels}\left(c, e\right)\right) \leq d)\\\land (\max\left(\operatorname{ceil}\left(N/e\right), \operatorname{K}\left(c, e\right) + M\right) \leq d \Rightarrow \operatorname{Reaches}\left(\alpha, d, e, c\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.uniform_record_memory_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ryo Nomura and Te Sun Han (2012). *Second-Order Resolvability, Intrinsic Randomness, and Fixed-Length Source Coding for Mixed Sources: Information Spectrum Approach*. DOI: [10.1109/TIT.2012.2215836](https://doi.org/10.1109/TIT.2012.2215836). URL: <https://arxiv.org/abs/1106.1879v4>.

*Commentary.*

Use the same finite model and feasibility assumptions. Class mass is the sum of the fibre sizes divided by N. Suppose M is the least cardinality of a label set with class mass at least alpha. Put C equal to the ceiling of N/e and J_full equal to the number of fibres of size at least e. Reaches(alpha,d,e,c) means there exist a full-input isometric encoder and a memory POVM with average success at least alpha under u.

The K full blocks represent J_full classes and the remaining d minus K slots can represent at most that many additional classes. Conversely, a minimum cover fits using at most K full blocks and M remainder blocks. For alpha strictly between zero and one, the least feasible d reaching alpha therefore lies between the two displayed dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.uniform_optimalSuccess_eq`
- Truth anchor: `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.uniform_record_memory_bounds`
- Truth anchor: `D5/S3/Quantum/Measurements/WeightedLabelRecordDilation.weightedLabelRecord_optimum`
- Dependency: [D5/S3/Quantum/Measurements/FiniteLabelRecordDilation](FiniteLabelRecordDilation.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordSpectralMemory](../PureState/PhaseRecordSpectralMemory.md)
