# Trace-norm discord and maximal mutual correlation

## Abstract

For every two-qubit density matrix, one-sided trace-norm geometric discord is at most maximal mutual correlation.

The qubits are ordered A, B, with matrix indices in Fin(2) × Fin(2). Fin(2) indexes 0, 1, and U(2) is the group of unitary complex 2 by 2 matrices. A dagger denotes conjugate transpose, I denotes the identity, and vector lengths are Euclidean. The trace norm ‖m‖₁ is `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm`, namely Re tr(√(m†m)). Write 𝒫_U(ρ) = measuredState(U,ρ) for `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.measuredState`, the unread measurement Σ_k (P_k ⊗ I)ρ(P_k ⊗ I) on A, where P_k projects onto column k of U. Write C_M(ρ) for `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.maximalMutualCorrelation`, the supremum of the absolute local covariances over complex 2 by 2 matrices of operator norm one, without a Hermitian restriction.

**Definition 1.1 (One-sided trace-norm geometric discord).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{traceNormDiscord}\left(\rho\right) = \operatorname{inf}\left(\left\{\left\lVert (\rho - \operatorname{measuredState}\left(U, \rho\right)) \right\rVert_{1} \mid U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right\}\right))$$

*Formalization.* `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.traceNormDiscord` (`✓ std3`).

*Citation.* Lech Jakóbczyk (2016). *Maximal mutual correlation: an algebraic measure of correlations in bipartite quantum systems*. URL: <https://arxiv.org/abs/1607.06585v1>.

*Commentary.*

The infimum ranges over all orthonormal measurement bases on A. For a density matrix this is the source's D₁, with no factor of one half. The definition also applies to every complex two-qubit matrix, without positivity or normalization assumptions.

**Definition 1.2 (The two-qubit trace-norm bound).**

$$\operatorname{claim} \Leftrightarrow (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{tr}\left(\rho\right) = 1) \Rightarrow (\operatorname{traceNormDiscord}\left(\rho\right) \le \left(C_{M}\right)\left(\rho\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.claim` (`✓ std3`).

*Citation.* Lech Jakóbczyk (2016). *Maximal mutual correlation: an algebraic measure of correlations in bipartite quantum systems*. URL: <https://arxiv.org/abs/1607.06585v1>.

*Commentary.*

The proposition states D₁(ρ) ≤ C_M(ρ) for every positive semidefinite two-qubit matrix of trace one, including pure and mixed states. The source proves the Bell-diagonal case and conjectures the inequality for general two-qubit states.

**Theorem 1.3 (The square of a real Pauli combination).**

Lean statement: `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.spin_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.spin_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real three-vector c, the Pauli combination c·σ squares to the squared Euclidean length of c times the identity. This follows by applying the Pauli anticommutator to c twice.

**Theorem 1.4 (Maximal mutual correlation bounds trace-norm discord).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/jakobczyk-2016-trace-norm-discord-mutual-correlation-bound` (proved) by `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jakobczyk-2016-trace-norm-discord-mutual-correlation-bound","declaration_gid":"D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lech Jakóbczyk (2016). *Maximal mutual correlation: an algebraic measure of correlations in bipartite quantum systems*. URL: <https://arxiv.org/abs/1607.06585v1>.

*Commentary.*

Let ρ be positive semidefinite with trace one, and let x be its Bloch vector on A. Choose a unit u parallel to x when x ≠ 0, and any unit u when x = 0. Measure A in the eigenbasis of u·σ. The existence of such a basis is expressed by `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.marginal_basis`. Work in that basis, using `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.rotateState`, so the first two coordinates of x vanish and u is the third coordinate vector. Unitary conjugation preserves the trace norm of the disturbance.

Write R for the state in this basis, x and y for its Bloch vectors, T for its Pauli correlation tensor, and Q = T − xyᵀ for `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.connectedCorrelation`. Put P = I − uuᵀ. Since Px = 0, the disturbance δ = R − 𝒫_I(R) is Σ_ij (PQ)_ij σ_i ⊗ σ_j/4. Diagonalizing the 2 by 2 Gram matrix of Qᵀ restricted to the plane perpendicular to u gives a rotated orthonormal pair v′, w′ with a = Qᵀv′ perpendicular to b = Qᵀw′.

The disturbance is δ = (A₁ + A₂)/4, where A₁ = (v′·σ) ⊗ (a·σ) and A₂ = (w′·σ) ⊗ (b·σ). These are Hermitian Pauli products. Anticommutation in each tensor factor makes A₁ and A₂ commute. With α = |a| and β = |b|, they satisfy A₁² = α²I, A₂² = β²I and tr(A₁A₂) = 0.

Interchange the two terms if necessary so α ≥ β. If α = 0, both products vanish. Otherwise the positive square root is √(δ†δ) = (αI + α⁻¹A₁A₂)/4. Its positivity follows from the equal expression ((A₁ + A₂)†(A₁ + A₂) + (α² − β²)I)/(8α), and squaring gives δ†δ. Since tr(I) = 4 and tr(A₁A₂) = 0, taking the trace gives ‖δ‖₁ = α = max(|a|, |b|).

For a ≠ 0, choose unit spin directions c = v′ and d = a/|a|. Their covariance in R is cᵀQd = |a|. Conjugate c·σ back to the original basis on A; its operator norm is still one. The bound `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.rotated_spin_witness` therefore gives C_M(ρ) ≥ |a|. The zero case follows from nonnegativity, and the same argument with w′ and b gives C_M(ρ) ≥ |b|. The infimum defining discord is at most this measurement's disturbance, so D₁(ρ) ≤ ‖δ‖₁ = max(|a|, |b|) ≤ C_M(ρ).

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.connectedCorrelation`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.marginal_basis`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.maximalMutualCorrelation`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.measuredState`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.rotateState`
- Truth anchor: `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.rotated_spin_witness`
- Truth anchor: `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.result`
- Truth anchor: `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.spin_square`
- Truth anchor: `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.traceNormDiscord`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound](GeometricDiscordMutualCorrelationBound.md)
