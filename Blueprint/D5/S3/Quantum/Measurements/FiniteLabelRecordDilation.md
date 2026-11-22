# Perfect label records with a finite pure environment

## Abstract

Exact finite memory and pure-environment dimensions for perfect label records.

**Theorem 1.1 (Sharp joint dimension criterion).**

$$\begin{aligned}0 < e \Rightarrow\\\operatorname{HasPerfectLabelRecord}\left(l, d, e\right) \iff (\operatorname{card}\left(B\right) \leq d \cdot e \land \sum_{j \in J} \operatorname{ceil}\left(n_{j}/e\right) \leq d)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/FiniteLabelRecordDilation.perfectLabelRecord_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Acknowledgement.* Anna Jenčová and Dénes Petz (2006). *Sufficiency in Quantum Statistical Inference*. DOI: [10.1007/s00220-005-1510-7](https://doi.org/10.1007/s00220-005-1510-7). URL: <https://arxiv.org/abs/math-ph/0412093v1>.

*Commentary.*

Let B be a finite input basis, P a subset of supported coordinates, and l a map from P to a finite label type J. In a diagonal experiment P consists of the positive-reference coordinates. The class size n_j counts the b in P with l(b) = j. The encoder is a complex matrix V from B to Fin d times Fin e with adjoint times itself equal to the identity. Here d is the memory dimension and e is the dimension of the pure Stinespring ancilla. The dimensions are static Hilbert-space counts.

The predicate requires one POVM on the memory whose effects are positive semidefinite and sum to the identity. For each b in P the effect for l(b) has trace pairing one with the partial trace of the outer product of the column at b. The partial trace sums the outer products of that column's environment slices. The POVM includes a spare outcome, so an empty support can be handled even when J is empty.

For each class j, the miss probability is a sum of nonnegative slice terms. Each term vanishes, putting every slice in the one-eigenspace of the effect for j. Those eigenspaces are mutually orthogonal. Linear independence of the isometric columns bounds each class size by e times the eigenspace dimension. The sum of these dimensions is at most d.

For the converse, allocate ceil(n_j/e) disjoint memory coordinates to class j and inject its n_j input coordinates into the product of that block and the environment. Extend the injection to the rest of B using the free joint coordinates. The resulting basis-column matrix is an isometry and diagonal block projectors give the perfect measurement.

With two labels of sizes three and one and d = e = 2, the input fits into four joint dimensions and there are two labels. The rounded block sizes are two and one, so three memory dimensions are necessary.

Kato Section VI.A gives the unrestricted dimension for exact classical local compression. Koashi and Imoto Theorem 3 describes operations fixing a family of states and Theorem 4 gives the product decomposition for independent choices. Jencova and Petz Section 4, Theorem 5 and Corollary 1 describe sufficient channels through block structure. The finite theorem here applies to perfect reading of a specified basis label.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/FiniteLabelRecordDilation.perfectLabelRecord_iff`
