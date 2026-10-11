# Subadditivity of quantum states over time

## Abstract

The Werner–Holevo channel on the maximally mixed five-level state gives a two-time pseudo-density matrix whose signed entropy exceeds the sum of its marginal entropies.

**Definition 1.1 (Input-first Jamiołkowski matrix).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall E \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right),\; \operatorname{jamio}\left(E\right) = \sum_{i:\operatorname{Fin}\left(n\right)} (\sum_{j:\operatorname{Fin}\left(n\right)} (\operatorname{kronecker}\left(\operatorname{single}\left(i, j, 1\right), E\left(\operatorname{single}\left(j, i, 1\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.jamio` (`✓ std3`).

*Citation.* James Fullwood and Arthur J. Parzygnat (2025). *On Dynamical Measures of Quantum Information*. DOI: [10.3390/e27040331](https://doi.org/10.3390/e27040331). URL: <https://doi.org/10.3390/e27040331>.

*Commentary.*

The input factor precedes the output factor. The matrix unit inside the channel has its indices reversed: this is the Jamiołkowski convention of Fullwood and Parzygnat, rather than the Choi convention. The carrier is Fin n times Fin m, matching the factor order in rho tensor the output identity.

**Definition 1.2 (Two-time pseudo-density matrix).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall E \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right),\; \operatorname{pdm}\left(rho, E\right) = \operatorname{smul}\left(\frac{1}{2}, \operatorname{kronecker}\left(rho, (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))\right) \cdot \operatorname{jamio}\left(E\right) + \operatorname{jamio}\left(E\right) \cdot \operatorname{kronecker}\left(rho, (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.pdm` (`✓ std3`).

*Citation.* James Fullwood and Arthur J. Parzygnat (2025). *On Dynamical Measures of Quantum Information*. DOI: [10.3390/e27040331](https://doi.org/10.3390/e27040331). URL: <https://doi.org/10.3390/e27040331>.

*Commentary.*

Equation (15) defines a quantum state over time by half the anticommutator of rho tensor the output identity with the Jamiołkowski matrix. The channel is a complex-linear map between full matrix algebras.

**Definition 1.3 (Fullwood–Parzygnat subadditivity conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; (1 \le n) \Rightarrow ((1 \le m) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{trace}\left(rho\right) = 1) \Rightarrow (\forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\sum_{k:iota} (\operatorname{conjTranspose}\left(K\left(k\right)\right) \cdot K\left(k\right)) = 1) \Rightarrow (\operatorname{entropy}\left(\operatorname{pdm}\left(rho, \operatorname{ofKraus}\left(K, K\right)\right)\right) \le \operatorname{entropy}\left(rho\right) + \operatorname{entropy}\left(\operatorname{ofKraus}\left(K, K\right)\left(rho\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim` (`✓ std3`).

*Citation.* James Fullwood and Arthur J. Parzygnat (2025). *On Dynamical Measures of Quantum Information*. DOI: [10.3390/e27040331](https://doi.org/10.3390/e27040331). URL: <https://doi.org/10.3390/e27040331>.

*Commentary.*

Remark 1 of On Dynamical Measures of Quantum Information conjectures subadditivity on quantum states over time. Both dimensions are positive. The input is positive semidefinite with trace one, and the arbitrary finite Kraus family satisfies the completeness equation. ofKraus(K,K) is FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus, whose action is the sum of K_k X K_k adjoint. Thus the hypothesis gives a completely positive trace-preserving map. The bound uses ChenKatoBrandaoCMIRefutation.entropy: on Hermitian matrices it is PartialTraceMutualInformation.spectralEntropy, the sum of -lambda log |lambda| over the eigenvalues with multiplicity, including zero contributions at zero; its value on other matrices is zero. The bound compares this signed entropy of the two-time matrix with the entropies of the input and output states. Fullwood and Yang, arXiv:2608.28946v1, Section 6, also state the higher-dimensional question as open.

**Theorem 1.4 (A five-level Werner–Holevo counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fullwood-parzygnat-2025-states-over-time-subadditivity` (refuted) by `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fullwood-parzygnat-2025-states-over-time-subadditivity","declaration_gid":"D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* James Fullwood and Arthur J. Parzygnat (2025). *On Dynamical Measures of Quantum Information*. DOI: [10.3390/e27040331](https://doi.org/10.3390/e27040331). URL: <https://doi.org/10.3390/e27040331>.

*Commentary.*

Let rho be the identity divided by five and use the ten Kraus operators (E_ij - E_ji)/2, one for each i < j. Their adjoint products sum to the identity. Their channel action is (trace(X) I - transpose(X))/4 and fixes rho. Use ProductUnitaryChoiSpectrum.omega 5, whose entries are one exactly on equal input and output indices, and let P be its outer product divided by five. ProductUnitaryChoiSpectrum.omega_dot_omega gives squared norm five; complex conjugation fixes this vector. P is a Hermitian idempotent of trace one. The Jamiołkowski matrix is (I - 5P)/4, and the two-time matrix is (I - 5P)/20. Its eigenvalues are -1/5 once and 1/20 twenty-four times. Apply CumulantRenyiDataProcessingRefutation.two_point_cfc to the self-adjoint involution H = 2P - I with a = -3/40 and b = -1/8. This evaluates the signed entropy ChenKatoBrandaoCMIRefutation.entropy through PartialTraceMutualInformation.re_trace_cfc and gives log 5 + (6/5) log 4. Each marginal entropy is log 5. The excess is (1/5) log(4096/3125), which is strictly positive because 4096 > 3125. This contradicts the universal subadditivity bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.jamio`
- Truth anchor: `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.pdm`
- Truth anchor: `D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum](../QuantumChannels/ProductUnitaryChoiSpectrum.md)
- Dependency: [D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation](../../QuantumChannels/CumulantRenyiDataProcessingRefutation.md)
