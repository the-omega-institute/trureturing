# Symmetric qudit states with an absolutely PPT spectrum

## Abstract

The conjectured symmetric qudit spectrum is SAPPT at and above its threshold.

**Definition 1.1 (Symmetric operators).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator}\left(rho\right)) \Leftrightarrow (\forall y \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(\operatorname{fun} (x: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \mapsto rho\left(x, y\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The source states on p. 1: “They satisfy ρ = πρπ′ with π and π′ any pair of permutation operators.” For a Hermitian matrix, the column condition expresses support in the symmetric subspace.

**Definition 1.2 (Symmetric unitaries).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSymmetricUnitary}\left(U\right)) \Leftrightarrow ((U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (\forall v \in \left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(v\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(\operatorname{Matrix.mulVec}\left(U, v\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSymmetricUnitary` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The source states on p. 2: “A symmetric state ρ is said to be symmetric absolutely PPT (SAPPT) [20] if UρU† is PPT for any U ∈ SU(N + 1) [24].” The full tensor-space unitary restricts to a unitary on the symmetric subspace; the indices here allow d local levels.

**Definition 1.3 (Every partial transpose is positive).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsFullyPPT}\left(rho\right)) \Leftrightarrow (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, rho\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsFullyPPT` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The source states on p. 1: “In this work, we are interested in states that are PPT for any bipartition, and we will call them just as PPT states.” Partial transposition is tested on every subset of sites, including the empty and full subsets.

**Definition 1.4 (Symmetric absolute PPT).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSAPPT}\left(rho\right)) \Leftrightarrow (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSymmetricUnitary}\left(U\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsFullyPPT}\left(U \cdot rho \cdot \operatorname{Matrix.conjTranspose}\left(U\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSAPPT` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The source states on p. 2: “A symmetric state ρ is said to be symmetric absolutely PPT (SAPPT) [20] if UρU† is PPT for any U ∈ SU(N + 1) [24].” Positivity is required for every subset of tensor sites; scalar phases cancel in unitary conjugation.

**Definition 1.5 (Symmetric-space dimension).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right) = \operatorname{Nat.choose}\left(N + d - 1, d - 1\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.D` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Conjecture 1 (p. 3): “Any symmetric N-qudit state ρ with a spectrum composed of D = binom(N+d−1, d−1) non-zero eigenvalues of the form (1 − (D−1)p/D, p/D, …, p/D), with p ∈ [p_min, 1] where p_min = 1/(1 + 2[D binom(N, ⌊N/2⌋)]^{−1}), is SAPPT.” The dimension uses natural subtraction on both arguments.

**Definition 1.6 (Threshold).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.pmin}\left(N, d\right) = \frac{1}{1 + 2 \cdot ((\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R}) \cdot (\operatorname{Nat.choose}\left(N, \operatorname{Nat.div}\left(N, 2\right)\right): \mathbb{R}))^{-1}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.pmin` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Conjecture 1 (p. 3): “Any symmetric N-qudit state ρ with a spectrum composed of D = binom(N+d−1, d−1) non-zero eigenvalues of the form (1 − (D−1)p/D, p/D, …, p/D), with p ∈ [p_min, 1] where p_min = 1/(1 + 2[D binom(N, ⌊N/2⌋)]^{−1}), is SAPPT.” Nat.div N 2 is the floor of N/2.

**Definition 1.7 (Conjecture 1).**

$$(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.claim}\left(\right)) \Leftrightarrow (\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le N) \Rightarrow ((2 \le d) \Rightarrow (\forall p \in \mathbb{R},\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.pmin}\left(N, d\right) \le p) \Rightarrow ((p \le 1) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.charpoly}\left(rho\right) = (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((1 - \frac{\left((\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R}) - 1\right) \cdot p}{(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R})}: \mathbb{C})\right)) \cdot ((\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((\frac{p}{(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R})}: \mathbb{C})\right)))^{\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right) - 1} \cdot (\operatorname{Polynomial.X})^{(d)^{N} - \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right)}) \Rightarrow (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSAPPT}\left(rho\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.claim` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Conjecture 1 (p. 3): “Any symmetric N-qudit state ρ with a spectrum composed of D = binom(N+d−1, d−1) non-zero eigenvalues of the form (1 − (D−1)p/D, p/D, …, p/D), with p ∈ [p_min, 1] where p_min = 1/(1 + 2[D binom(N, ⌊N/2⌋)]^{−1}), is SAPPT.” The indices are all functions from Fin N to Fin d. The full-space characteristic polynomial includes d^N − D zero eigenvalues. N and d are at least two. Natural-number division in the threshold is Nat.div.

**Theorem 1.8 (Conjecture 1 holds).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le N) \Rightarrow ((2 \le d) \Rightarrow (\forall p \in \mathbb{R},\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.pmin}\left(N, d\right) \le p) \Rightarrow ((p \le 1) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.charpoly}\left(rho\right) = (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((1 - \frac{\left((\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R}) - 1\right) \cdot p}{(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R})}: \mathbb{C})\right)) \cdot ((\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((\frac{p}{(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right): \mathbb{R})}: \mathbb{C})\right)))^{\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right) - 1} \cdot (\operatorname{Polynomial.X})^{(d)^{N} - \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.D}\left(N, d\right)}) \Rightarrow (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.IsSAPPT}\left(rho\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result` (`✓ std3`). ∎

*Resolves.* `Problems/louvet-2025-symmetric-absolutely-ppt` (proved) by `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"louvet-2025-symmetric-absolutely-ppt","declaration_gid":"D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The permutation symmetrizer retains a positive floor after partial transposition. A positive residual contributes at least minus half its trace on the local symmetric subspace. The spectral parameters and the central binomial coefficient make their sum positive for every bipartition.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.D`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsFullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSAPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.IsSymmetricUnitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.pmin`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor](SymmetricAbsolutePPTPermutationFloor.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound](SymmetricAbsolutePPTPureBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
