# Metrotropy can exceed half the ergotropy

## Abstract

A non-stationary pure state in dimension four has metrotropy strictly greater than half its ergotropy.

**Definition 1.1 (A nonselective rank-one measurement).**

$$\forall (d: \mathbb{N}), (\forall (u: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.measured}\left(u, \rho\right) = \operatorname{D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation.krausApply}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(u\right), \rho\right))))$$

*Formalization.* `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.measured` (`✓ std3`).

*Citation.* Andrea Solfanelli; Lorenzo Buffoni; Alessandro Cuccoli; Michele Campisi (2019). *Maximal energy extraction via quantum measurement*. DOI: [10.1088/1742-5468/ab3721](https://doi.org/10.1088/1742-5468/ab3721). URL: <https://arxiv.org/abs/1905.10262v2>.

*Commentary.*

The columns of a unitary u form an orthonormal basis. For each column, take its rank-one orthogonal projector. The measured matrix is the sum of the products of each projector, the input matrix, and the same projector. This is the nonselective measurement of Metrotropy02.tex, lines 164–175. The definition applies to every complex input matrix and every natural dimension, without a density assumption.

**Definition 1.2 (Energy extractable by a rank-one measurement).**

$$\forall (d: \mathbb{N}), (\forall (h: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.metrotropy}\left(h, \rho\right) = \operatorname{D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.expect}\left(\rho, h\right) - \operatorname{sInf}\left(\{e: \mathbb{R} \mid \exists (u: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)), (e = \operatorname{D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.expect}\left(\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.measured}\left(u, \rho\right), h\right))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.metrotropy` (`✓ std3`).

*Citation.* Andrea Solfanelli; Lorenzo Buffoni; Alessandro Cuccoli; Michele Campisi (2019). *Maximal energy extraction via quantum measurement*. DOI: [10.1088/1742-5468/ab3721](https://doi.org/10.1088/1742-5468/ab3721). URL: <https://arxiv.org/abs/1905.10262v2>.

*Commentary.*

Subtract the infimum of the energies after rank-one projective measurements from the initial energy. The real energy expect of a matrix and a Hamiltonian is the real part of the trace of their product, with the Hamiltonian on the left. Every orthonormal measurement basis is represented by the columns of a unitary. Metrotropy02.tex, line 272, defines metrotropy as initial energy minus minimum final energy; lines 298–304 give the non-stationary measurement setting. The displayed definition uses the real infimum and is defined even for matrices that are not states or Hamiltonians.

**Definition 1.3 (Energy extractable by a unitary).**

$$\forall (d: \mathbb{N}), (\forall (h: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.ergotropy}\left(h, \rho\right) = \operatorname{D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.expect}\left(\rho, h\right) - \operatorname{sInf}\left(\{e: \mathbb{R} \mid \exists (v: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)), (e = \operatorname{D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.expect}\left(\operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution}\left((\operatorname{Subtype.val}\left(v\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \rho\right), h\right))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.ergotropy` (`✓ std3`).

*Citation.* Andrea Solfanelli; Lorenzo Buffoni; Alessandro Cuccoli; Michele Campisi (2019). *Maximal energy extraction via quantum measurement*. DOI: [10.1088/1742-5468/ab3721](https://doi.org/10.1088/1742-5468/ab3721). URL: <https://arxiv.org/abs/1905.10262v2>.

*Commentary.*

Subtract the infimum of the energies of all unitary conjugates of the input matrix from its initial energy. Subtype.val explicitly extracts the complex matrix underlying v, and unitaryEvolution sends the input to that matrix times the input times its conjugate transpose. This is the unitary optimization of Metrotropy02.tex, lines 130–153 and 291–296, expressed with a real infimum. The definition itself imposes neither Hermiticity nor positivity nor trace normalization.

**Definition 1.4 (The proposed inequality for non-stationary states).**

$$(\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (\forall (h: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{Matrix.IsHermitian}\left(h\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \Rightarrow (((h) \cdot (\rho) \ne (\rho) \cdot (h)) \Rightarrow (\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.metrotropy}\left(h, \rho\right) \le \frac{\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.ergotropy}\left(h, \rho\right)}{(2: \mathbb{R})})))))))$$

*Formalization.* `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrea Solfanelli; Lorenzo Buffoni; Alessandro Cuccoli; Michele Campisi (2019). *Maximal energy extraction via quantum measurement*. DOI: [10.1088/1742-5468/ab3721](https://doi.org/10.1088/1742-5468/ab3721). URL: <https://arxiv.org/abs/1905.10262v2>.

*Commentary.*

For every natural dimension d, Hermitian matrix h, and density matrix ρ that does not commute with h, the proposed inequality bounds the metrotropy by one half of the ergotropy. A density matrix here is positive semidefinite with complex trace one. Metrotropy02.tex, line 308, asks whether this inequality holds when the initial state is not stationary. The universal proposition displayed here gives that question precise matrix domains and quantifiers; measurements have rank-one projectors.

**Theorem 1.5 (A four-dimensional counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/solfanelli-buffoni-cuccoli-campisi-2019-metrotropy-half-ergotropy` (refuted) by `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"solfanelli-buffoni-cuccoli-campisi-2019-metrotropy-half-ergotropy","declaration_gid":"D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrea Solfanelli; Lorenzo Buffoni; Alessandro Cuccoli; Michele Campisi (2019). *Maximal energy extraction via quantum measurement*. DOI: [10.1088/1742-5468/ab3721](https://doi.org/10.1088/1742-5468/ab3721). URL: <https://arxiv.org/abs/1905.10262v2>.

*Commentary.*

Take the Hamiltonian H = diag(0, 1, 2, 10), the vector ψ = (0, 0, 3i/5, 4/5), and the pure state ρ = ψψ†. Let U be one half of the real matrix with successive rows (1, 1, 1, 1), (1, −1, 1, −1), (1, 1, −1, −1), and (1, −1, −1, 1). The trace of ρ is 9/25 + 16/25 = 1, and ρ is positive semidefinite as an outer product. The real diagonal H is Hermitian. With coordinates numbered from zero, the (2, 3) entry of Hρ − ρH is −96i/25, so H and ρ do not commute. Multiplying U by its conjugate transpose gives the identity, so U is unitary.

For an arbitrary unitary u, write the nonselective measurement as the sum of its rank-one projectors multiplied on both sides of the input. For a pure input ψψ†, multiplication of outer products expresses each summand as the projector onto column k multiplied by the product of the inner product of that column with ψ and its complex conjugate. For the chosen U and ψ, this product is 1/4 for each of the four columns. The column projectors sum to the identity, so the measured state is I/4. Direct evaluation gives initial energy 2(9/25) + 10(16/25) = 178/25 and measured energy (0 + 1 + 2 + 10)/4 = 13/4.

If a diagonal Hamiltonian has nonnegative real diagonal entries and a matrix σ is positive semidefinite, then the energy of σ is nonnegative. Indeed, the diagonal entries of σ are real and nonnegative, and the real part of the trace of the product is the sum of their products with the Hamiltonian entries. Every measured output of ρ is positive semidefinite, since it is a sum of Kraus products of a positive semidefinite matrix. Thus the set of measurement energies is bounded below by zero. Its infimum is at most the energy 13/4 attained by U. Subtracting from 178/25 gives metrotropy at least 387/100.

The set of unitary output energies is nonempty because it contains the output of the identity unitary. Unitary conjugation preserves positive semidefiniteness, so the same diagonal-energy argument makes every element of this set nonnegative. Its infimum is therefore nonnegative, giving ergotropy at most 178/25. Half the ergotropy is consequently at most 89/25 = 356/100, strictly below the metrotropy lower bound 387/100. Applying the universal inequality to dimension four, H, and ρ would contradict these bounds; hence the proposition is false.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.ergotropy`
- Truth anchor: `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.measured`
- Truth anchor: `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.metrotropy`
- Truth anchor: `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation](../Measurement/ErrorDisturbanceEndpointRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation](../QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.md)
