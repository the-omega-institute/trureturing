# Three-weight Pauli channels have Bayesian inverses only at the maximally mixed state

## Abstract

Ting, Fullwood and Wu (arXiv:2605.10375) characterize when a unital qubit channel has a Bayesian inverse with respect to a state, and for Pauli channels with exactly three non-zero weights leave open whether the maximally mixed state is the only such state. It is: for every Pauli channel whose probability vector has exactly three non-zero entries, a completely positive trace-preserving Bayesian inverse with respect to a qubit state exists if and only if the state is the maximally mixed state.

**Definition 1.1 (The Pauli matrices).**

$$sigma = (\operatorname{pauliMatrix}\left(I\right), \operatorname{pauliMatrix}\left(X\right), \operatorname{pauliMatrix}\left(Y\right), \operatorname{pauliMatrix}\left(Z\right))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

sigma lists the identity and the Pauli matrices X, Y = i X Z and Z of the frozen pauliMatrix, indexed by Fin 4.

**Definition 1.2 (The Pauli channel).**

$$\forall p : \operatorname{Fin}\left(4\right) \to \mathbb{R}, \forall A : \mathbb{C}^{2\times 2}, \operatorname{pauliChannel}\left(p\right)\left(A\right) = \sum_{\mu} p\left(\mu\right) \cdot \operatorname{sigma}\left(\mu\right) \cdot A \cdot \operatorname{sigma}\left(\mu\right)$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.pauliChannel` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

The Pauli channel with probability vector p acts by A -> sum over mu of p_mu sigma_mu A sigma_mu, as a complex-linear map on 2 x 2 matrices.

**Definition 1.3 (The Jamiolkowski matrix).**

$$\forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{jam}\left(N\right) = \sum_{i} \sum_{j} \operatorname{kronecker}\left(\operatorname{single}\left(i, j, 1\right), N\left(\operatorname{single}\left(j, i, 1\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.jam` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

J[N] = (id tensor N)(SWAP) with SWAP = sum over i, j of |i><j| tensor |j><i|, written with the matrix units single(i, j, 1) and the Kronecker product.

**Definition 1.4 (Bayesian inverse).**

$$\forall E : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall Eadj : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall \rho : \mathbb{C}^{2\times 2}, \operatorname{IsBayesianInverse}\left(E, Eadj, F, \rho\right) \Leftrightarrow ((\operatorname{IsCPTP}\left(F\right)) \land (\operatorname{kronecker}\left(E\left(\rho\right), 1\right) \cdot \operatorname{jam}\left(F\right) + \operatorname{jam}\left(F\right) \cdot \operatorname{kronecker}\left(E\left(\rho\right), 1\right) = \operatorname{kronecker}\left(1, \rho\right) \cdot \operatorname{jam}\left(Eadj\right) + \operatorname{jam}\left(Eadj\right) \cdot \operatorname{kronecker}\left(1, \rho\right)))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.IsBayesianInverse` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

F is a Bayesian inverse of E with respect to rho when F is completely positive and trace preserving and the quantum Bayes rule {E(rho) tensor 1, J[F]} = {1 tensor rho, J[E^dagger]} holds, written with the anticommutators expanded; Eadj is the channel standing for the Hilbert-Schmidt adjoint E^dagger.

**Definition 1.5 (Uniqueness of the maximally mixed state).**

$$claim \Leftrightarrow (\forall p : \operatorname{Fin}\left(4\right) \to \mathbb{R}, (\forall \mu : \operatorname{Fin}\left(4\right), 0 \le p\left(\mu\right)) \Rightarrow ((\sum_{\mu} p\left(\mu\right) = 1) \Rightarrow ((\operatorname{card}\left(\operatorname{filter}\left(\mu \mapsto p\left(\mu\right) \ne 0, \operatorname{univ}\left(\operatorname{Fin}\left(4\right)\right)\right)\right) = 3) \Rightarrow ((\forall A : \mathbb{C}^{2\times 2}, \forall B : \mathbb{C}^{2\times 2}, \operatorname{trace}\left(A^{H} \cdot \operatorname{pauliChannel}\left(p\right)\left(B\right)\right) = \operatorname{trace}\left((\operatorname{pauliChannel}\left(p\right)\left(A\right))^{H} \cdot B\right)) \land (\forall \rho : \mathbb{C}^{2\times 2}, (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\exists F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{IsBayesianInverse}\left(\operatorname{pauliChannel}\left(p\right), \operatorname{pauliChannel}\left(p\right), F, \rho\right)) \Leftrightarrow (\rho = \frac{1}{2} \cdot 1)))))))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.claim` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

For every probability vector p with exactly three non-zero entries: the Pauli channel equals its own Hilbert-Schmidt adjoint, which justifies using it in the place of E^dagger, and for every density matrix rho (pure states included) a Bayesian inverse with respect to rho exists if and only if rho is the maximally mixed state 1/2.

**Theorem 1.6 (Bayesian inverses of three-weight Pauli channels).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/ting-fullwood-wu-2026-three-weight-bayesian-inverse` (proved) by `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ting-fullwood-wu-2026-three-weight-bayesian-inverse","declaration_gid":"D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

At the maximally mixed state the channel itself is a Bayesian inverse: it is completely positive with Kraus operators sqrt(p_mu) sigma_mu, trace preserving, and both sides of the Bayes rule equal J of the channel because the channel fixes 1/2. Conversely, write rho = (1 + r . sigma)/2 with r != 0. The Bayes rule determines the image of 1 and of each sigma_j under any candidate inverse, so the candidate's Choi matrix is fixed by p and r. With h_i = (1 - p_i) r_i for the three active weights (the zero weight in any of the four positions is handled by relabelling the Pauli indices), the vector w = (1 tensor (1 - h . sigma)) applied to the unnormalized maximally entangled vector gives w* C w = -4[(1 - |h|^2) B + K A]/D with A, B, K >= 0, B > 0 and |h| < 1, which is negative. A completely positive map has a positive semidefinite Choi matrix, so no Bayesian inverse exists away from 1/2.

## References

- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.IsBayesianInverse`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.claim`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.jam`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.pauliChannel`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Quantum/Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Quantum/Information/StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
