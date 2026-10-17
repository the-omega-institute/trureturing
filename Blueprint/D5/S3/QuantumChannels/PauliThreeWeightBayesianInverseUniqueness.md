# Three-weight Pauli channels have Bayesian inverses only at the maximally mixed state

## Abstract

Ting, Fullwood and Wu (arXiv:2605.10375) characterize when a unital qubit channel has a Bayesian inverse with respect to a state, and for Pauli channels with exactly three non-zero weights leave open whether the maximally mixed state is the only such state. It is: for every Pauli channel whose probability vector has exactly three non-zero entries, a completely positive trace-preserving Bayesian inverse with respect to a qubit state exists if and only if the state is the maximally mixed state.

**Definition 1.1 (The Pauli matrices).**

$$sigma = (\operatorname{pauliMatrix}\left(I\right), \operatorname{pauliMatrix}\left(X\right), \operatorname{pauliMatrix}\left(Y\right), \operatorname{pauliMatrix}\left(Z\right))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

sigma lists the identity and the Pauli matrices X, Y = i X Z and Z of pauliMatrix, indexed by Fin 4.

**Theorem 1.2 (Self-adjoint Pauli involutions).**

$$\forall \mu : \operatorname{Fin}\left(4\right), ((\operatorname{sigma}\left(\mu\right))^{H} = \operatorname{sigma}\left(\mu\right)) \land (\operatorname{sigma}\left(\mu\right) \cdot \operatorname{sigma}\left(\mu\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the four Pauli matrices is self-adjoint and its square is the identity. The superscript H denotes conjugate transpose, and the product is matrix multiplication.

**Definition 1.3 (Spin observables).**

$$\forall r : \operatorname{Fin}\left(3\right) \to \mathbb{R}, \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(r\right) = \sum_{i: \operatorname{Fin}\left(3\right)} (\operatorname{Complex}.\operatorname{ofReal}\left(r\left(i\right)\right) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{sigma}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.spin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

For every real three-vector r, spin r is the sum of the complex embeddings of its coordinates times the three Pauli matrices. The index i.succ in Fin 4 selects X, Y and Z, leaving out the identity.

**Definition 1.4 (The Pauli channel).**

$$\forall p : \operatorname{Fin}\left(4\right) \to \mathbb{R}, \forall A : \mathbb{C}^{2\times 2}, \operatorname{pauliChannel}\left(p\right)\left(A\right) = \sum_{\mu} p\left(\mu\right) \cdot \operatorname{sigma}\left(\mu\right) \cdot A \cdot \operatorname{sigma}\left(\mu\right)$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.pauliChannel` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

The Pauli channel with probability vector p acts by A -> sum over mu of p_mu sigma_mu A sigma_mu, as a complex-linear map on 2 x 2 matrices.

**Theorem 1.5 (Complete positivity and trace preservation).**

$$\forall p : \operatorname{Fin}\left(4\right) \to \mathbb{R}, (\forall \mu : \operatorname{Fin}\left(4\right), 0 \le p\left(\mu\right)) \Rightarrow ((\sum_{\mu} p\left(\mu\right) = 1) \Rightarrow (\operatorname{IsCPTP}\left(\operatorname{pauliChannel}\left(p\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.channel_cptp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative normalized vector of four Pauli weights gives a completely positive trace-preserving map.

**Definition 1.6 (The Jamiolkowski matrix).**

$$\forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{jam}\left(N\right) = \sum_{i} \sum_{j} \operatorname{kronecker}\left(\operatorname{single}\left(i, j, 1\right), N\left(\operatorname{single}\left(j, i, 1\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.jam` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

J[N] = (id tensor N)(SWAP) with SWAP = sum over i, j of |i><j| tensor |j><i|, written with the matrix units single(i, j, 1) and the Kronecker product.

**Definition 1.7 (Bayesian inverse).**

$$\forall E : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall Eadj : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall \rho : \mathbb{C}^{2\times 2}, \operatorname{IsBayesianInverse}\left(E, Eadj, F, \rho\right) \Leftrightarrow ((\operatorname{IsCPTP}\left(F\right)) \land (\operatorname{kronecker}\left(E\left(\rho\right), 1\right) \cdot \operatorname{jam}\left(F\right) + \operatorname{jam}\left(F\right) \cdot \operatorname{kronecker}\left(E\left(\rho\right), 1\right) = \operatorname{kronecker}\left(1, \rho\right) \cdot \operatorname{jam}\left(Eadj\right) + \operatorname{jam}\left(Eadj\right) \cdot \operatorname{kronecker}\left(1, \rho\right)))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.IsBayesianInverse` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

F is a Bayesian inverse of E with respect to rho when F is completely positive and trace preserving and the quantum Bayes rule {E(rho) tensor 1, J[F]} = {1 tensor rho, J[E^dagger]} holds, written with the anticommutators expanded; Eadj is the channel standing for the Hilbert-Schmidt adjoint E^dagger.

**Definition 1.8 (Uniqueness of the maximally mixed state).**

$$claim \Leftrightarrow (\forall p : \operatorname{Fin}\left(4\right) \to \mathbb{R}, (\forall \mu : \operatorname{Fin}\left(4\right), 0 \le p\left(\mu\right)) \Rightarrow ((\sum_{\mu} p\left(\mu\right) = 1) \Rightarrow ((\operatorname{card}\left(\operatorname{filter}\left(\mu \mapsto p\left(\mu\right) \ne 0, \operatorname{univ}\left(\operatorname{Fin}\left(4\right)\right)\right)\right) = 3) \Rightarrow ((\forall A : \mathbb{C}^{2\times 2}, \forall B : \mathbb{C}^{2\times 2}, \operatorname{trace}\left(A^{H} \cdot \operatorname{pauliChannel}\left(p\right)\left(B\right)\right) = \operatorname{trace}\left((\operatorname{pauliChannel}\left(p\right)\left(A\right))^{H} \cdot B\right)) \land (\forall \rho : \mathbb{C}^{2\times 2}, (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\exists F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{IsBayesianInverse}\left(\operatorname{pauliChannel}\left(p\right), \operatorname{pauliChannel}\left(p\right), F, \rho\right)) \Leftrightarrow (\rho = \frac{1}{2} \cdot 1)))))))$$

*Formalization.* `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.claim` (`✓ std3`).

*Citation.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

For every probability vector p with exactly three non-zero entries: the Pauli channel equals its own Hilbert-Schmidt adjoint, which justifies using it in the place of E^dagger, and for every density matrix rho (pure states included) a Bayesian inverse with respect to rho exists if and only if rho is the maximally mixed state 1/2.

**Theorem 1.9 (Bayesian inverses of three-weight Pauli channels).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/ting-fullwood-wu-2026-three-weight-bayesian-inverse` (proved) by `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ting-fullwood-wu-2026-three-weight-bayesian-inverse","declaration_gid":"D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* O. Ting; J. Fullwood; Z. Wu (2026). *Operational time-reversal symmetry for unital qubit channels*. DOI: [10.48550/arXiv.2605.10375](https://doi.org/10.48550/arXiv.2605.10375). URL: <https://arxiv.org/abs/2605.10375v1>.

*Commentary.*

At the maximally mixed state the channel itself is a Bayesian inverse: it is completely positive with Kraus operators sqrt(p_mu) sigma_mu, trace preserving, and both sides of the Bayes rule equal J of the channel because the channel fixes 1/2. Conversely, write rho = (1 + r . sigma)/2 with sum r_i^2 <= 1 and r ≠ 0. The exact Bayes rule becomes a Sylvester equation for the canonical output-input Choi matrix C = MatrixMap.choi_matrix F. With s_i = lambda_i r_i, V = 1 tensor (s . sigma)^T and R = {rho tensor 1, MatrixMap.choi_matrix E}, one has V^2 = |s|^2 1 and C + (VC + CV)/2 = R. Therefore D C = (1 - |s|^2/2) R - (VR + RV)/2 + VRV/2, where D = 1 - |s|^2 >= 0. If p_k is the zero weight, let a_1, a_2, a_3 be the other three weights, listed through the Pauli product table, and h_i = (1 - a_i) r_i. The vector w(j, i) = ((1 - h . sigma) sigma_k)_{j i}, indexed by output j and input i, gives w* (D C) w = -4[(1 - |h|^2) B + K A], with A = sum a_i h_i^2, B = sum a_i^2 (1 - a_i) r_i^2 and K = sum a_i^2 r_i^2. Here B > 0 and |h| < 1, so the value is negative for every nonzero r, including pure states and every missing-weight position. The owning Choi theorem MatrixMap.choi_PSD_iff_CP_map makes C positive semidefinite under complete positivity, and multiplication by D >= 0 preserves this property, giving a contradiction. No division by D is used. The strict estimate |lambda_i| < 1 available for three positive weights also gives D > 0, uniqueness of the Sylvester candidate, and the equivalent divided expression w* C w = -4[(1 - |h|^2) B + K A]/D; those strict-denominator consequences are explanatory algebra, while the Lean obstruction uses only D >= 0.

Proposition 1 of the cited source transports Bayesian inverses under N = U composed with E composed with V: the state becomes V^dagger(rho) and the inverse becomes V^dagger composed with F composed with U^dagger. Unitary conjugation fixes 1/2 in both directions, so the Pauli conclusion applies to a unital qubit channel whose associated Pauli channel has three nonzero weights. This application uses the published proposition; unitary transport is not part of the Lean result. Operational reversal concerns the sequential measurement correlations in the exact Bayes rule. It asserts neither physical inversion of noise on arbitrary states nor a bound on resources for realizing the inverse.

For one nonzero weight the channel is unitary and every state has a Bayesian inverse; for two weights the source gives a coordinate axis of such states. Four positive weights permit a neighbourhood of 1/2 by positivity of the channel Choi matrix and continuity of the candidate, whereas at three weights the missing Pauli gives a zero Bell eigenvalue and the explicit quadratic form excludes every nonzero Bloch vector. The general four-weight inequalities and the continuity argument are outside the Lean result, as are exhaustive novelty and experimental implementation claims.

## References

- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.IsBayesianInverse`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.channel_cptp`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.claim`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.jam`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.pauliChannel`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma_properties`
- Truth anchor: `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.spin`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Quantum/Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Quantum/Information/StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
