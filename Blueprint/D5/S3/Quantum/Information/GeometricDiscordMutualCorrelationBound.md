# Geometric discord and maximal mutual correlation

## Abstract

For every two-qubit density matrix, maximal mutual correlation is at least the square root of normalized geometric discord measured on the first qubit.

The two qubits are ordered A, B, with matrix indices in Fin(2) × Fin(2). Fin(2) indexes 0, 1 and Fin(3) indexes the three Pauli matrices. The symbol 1 denotes the identity matrix of the indicated size, kronecker(a,b) denotes a ⊗ b, and a star denotes conjugate transpose. Matrix norms are operator norms for the Euclidean norm on vectors; the norm of a complex scalar is its modulus. Re denotes real part. The symbols inf and sup denote the infimum and supremum of sets of real numbers.

**Definition 1.1 (Measurement on the first qubit).**

$$\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{measuredState}\left(U, \rho\right) = \sum_{(k: \operatorname{Fin}\left(2\right))} ((\operatorname{kronecker}\left((U \cdot \operatorname{single}\left(k, k, 1\right) \cdot U^{*}), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)) \cdot \rho \cdot (\operatorname{kronecker}\left((U \cdot \operatorname{single}\left(k, k, 1\right) \cdot U^{*}), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.measuredState` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

For unitary U, let P_k = U single(k,k,1) U*, where single(k,k,1) has one in entry (k,k) and zero elsewhere. Thus P_k is the projector onto column k of U, and the displayed sum is Σ_k (P_k ⊗ I) ρ (P_k ⊗ I). It is the nonselective rank-one projective measurement on A. The matrix expression itself is defined for every U and every ρ.

**Definition 1.2 (Squared Hilbert–Schmidt norm).**

$$\forall (m: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{hsNormSq}\left(m\right) = \operatorname{Re}\left(\operatorname{tr}\left(m \cdot m^{*}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.hsNormSq` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

For every complex two-qubit matrix m, hsNormSq(m) is Re tr(m m*). The trace is real and nonnegative, so this is the squared Hilbert–Schmidt norm used in the source.

**Definition 1.3 (Normalized geometric discord).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{geometricDiscord}\left(\rho\right) = 2 \cdot \operatorname{inf}\left(\left\{\operatorname{hsNormSq}\left(\rho - \operatorname{measuredState}\left(U, \rho\right)\right) \mid U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right\}\right))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.geometricDiscord` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

The infimum ranges over all unitary 2 by 2 matrices U, hence all orthonormal measurement bases on A. The factor two is the source's normalization d/(d − 1) for d = 2. For a density matrix this is the normalized one-sided geometric discord D_G; the definition also applies to arbitrary complex two-qubit matrices.

**Definition 1.4 (Covariance between the local algebras).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{localCovariance}\left(\rho, a, b\right) = \operatorname{tr}\left(\rho \cdot (\operatorname{kronecker}\left(a, b\right))\right) - \operatorname{tr}\left(\rho \cdot (\operatorname{kronecker}\left(a, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right))\right) \cdot \operatorname{tr}\left(\rho \cdot (\operatorname{kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), b\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.localCovariance` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

The local matrices a and b act as a ⊗ I and I ⊗ b. Their covariance is the expectation of a ⊗ b minus the product of their separate expectations. The displayed expression is complex valued and requires no positivity or normalization assumption on ρ.

**Definition 1.5 (Maximal mutual correlation).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{maximalMutualCorrelation}\left(\rho\right) = \operatorname{sup}\left(\{ (r: \mathbb{R}) \mid \exists (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\left\lVert a \right\rVert = 1) \land ((\left\lVert b \right\rVert = 1) \land (r = \left\lVert \operatorname{localCovariance}\left(\rho, a, b\right) \right\rVert)))) \}\right))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.maximalMutualCorrelation` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

Take the supremum of the moduli of local covariances over all complex 2 by 2 matrices a and b of operator norm one. These matrices need not be Hermitian. For density matrices this is the source's maximal mutual correlation C_M between the two local algebras.

**Definition 1.6 (Connected Pauli correlations).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\operatorname{connectedCorrelation}\left(\rho, i, j\right) = \operatorname{corr}\left(\rho, i, j\right) - \operatorname{blochA}\left(\rho, i\right) \cdot \operatorname{blochB}\left(\rho, j\right))))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.connectedCorrelation` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

Write x_i = blochA(ρ,i), y_j = blochB(ρ,j), and T_ij = corr(ρ,i,j). These are the real parts of tr(ρ(σ_i ⊗ I)), tr(ρ(I ⊗ σ_j)), and tr(ρ(σ_i ⊗ σ_j)), respectively. The connected correlation matrix has entries Q_ij = T_ij − x_i y_j, as in the source's Pauli description of covariance.

**Definition 1.7 (The two-qubit correlation bound).**

$$\operatorname{claim} \Leftrightarrow (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{tr}\left(\rho\right) = 1) \Rightarrow (\sqrt{\operatorname{geometricDiscord}\left(\rho\right)} \le \operatorname{maximalMutualCorrelation}\left(\rho\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.claim` (`✓ std3`).

*Citation.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

The proposition is the first inequality in Eq. (II.23): √D_G(ρ) ≤ C_M(ρ) for every positive semidefinite two-qubit matrix of trace one. It includes pure and mixed states. The source establishes the Bell-diagonal case and proposes the general mixed-state inequality on numerical evidence.

**Theorem 1.8 (Maximal mutual correlation bounds geometric discord).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/gwozdz-jakobczyk-2013-geometric-discord-mutual-correlation-bound` (proved) by `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gwozdz-jakobczyk-2013-geometric-discord-mutual-correlation-bound","declaration_gid":"D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marek Gwóźdź; Lech Jakóbczyk (2014). *Spontaneous emission can locally create quantum discord out of classical correlations*. DOI: [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0). URL: <https://arxiv.org/abs/1306.0130v2>.

*Commentary.*

Let ρ be positive semidefinite with trace one. Its real Bloch vectors x and y and correlation tensor T give the expansion ρ = (I ⊗ I + Σ_i x_i σ_i ⊗ I + Σ_j y_j I ⊗ σ_j + Σ_ij T_ij σ_i ⊗ σ_j)/4. Put Q = T − x yᵀ.

Choose a unit vector u parallel to x when x ≠ 0, and any unit vector u when x = 0. Measure A in the eigenbasis of u·σ and set P = I − u uᵀ. Since Px = 0, the disturbance is δ = Σ_ij (PT)_ij σ_i ⊗ σ_j/4 and PT = PQ. Orthogonality of the Pauli tensors gives ‖δ‖₂² = ‖PQ‖_F²/4. For an orthonormal completion u, v, w, the discord therefore obeys D_G(ρ) ≤ ‖PQ‖_F²/2 = (‖Qᵀv‖² + ‖Qᵀw‖²)/2.

For unit real vectors c and d, the spin observables c·σ and d·σ have operator norm one and covariance cᵀQd. If Qᵀv ≠ 0, choose c = v and d = Qᵀv/‖Qᵀv‖ to obtain C_M(ρ) ≥ ‖Qᵀv‖. If Qᵀv = 0, the same inequality follows from nonnegativity. Applying this also to w gives D_G(ρ) ≤ C_M(ρ)².

Both quantities are nonnegative. The density-matrix estimate |tr(ρX)| ≤ ‖X‖ and compactness of the local unit spheres bound the covariance values, so their supremum is finite. Taking square roots proves √D_G(ρ) ≤ C_M(ρ).

## References

- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.connectedCorrelation`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.geometricDiscord`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.hsNormSq`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.localCovariance`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.maximalMutualCorrelation`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.measuredState`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.result`
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH](../Entanglement/SteeringEllipsoidCHSH.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
