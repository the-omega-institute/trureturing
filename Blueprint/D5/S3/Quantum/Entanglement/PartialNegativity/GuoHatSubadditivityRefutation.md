# Failure of partial-negativity subadditivity

## Abstract

An equal mixture of two orthogonal maximally entangled states on a 5 × 5 system has reduced function 1/2, whereas both marginals have reduced function 1/5. Thus the subadditivity conjecture (24) for the reduced function of the partial negativity is false.

**Definition 1.1 (The reduced function of the partial negativity).**

$$\forall n: Type, [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall X: \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \forall hX: X.\operatorname{IsHermitian}, \operatorname{hHat}\left(X, hX\right) = \operatorname{if} 2 \leq Fintype.\operatorname{card}(n) \operatorname{then} Real.\operatorname{sqrt}((hX.\operatorname{eigenvalues}_{0}(0) \cdot hX.\operatorname{eigenvalues}_{0}(1))) \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.hHat` (`✓ std3`).

*Citation.* Y. Guo (2024). *Complete Genuine Multipartite Entanglement Monotone*. DOI: [10.1016/j.rinp.2024.107430](https://doi.org/10.1016/j.rinp.2024.107430). URL: <https://arxiv.org/abs/2301.00334v3>.

*Commentary.*

Guo, arXiv:2301.00334v3, pp. 4–5: “ĥ(ρ) = √(δ1 δ2), … and δ1, δ2 are the two largest eigenvalues of ρ.” The two entries of Matrix.IsHermitian.eigenvalues₀ are in non-increasing order and counted with multiplicity. The entries at positions 0 and 1 represent δ1 and δ2. If the carrier has fewer than two elements, the value is zero. The condition in the formula supplies the bounds for the two Fin indices.

**Definition 1.2 (Guo's subadditivity conjecture (24)).**

$$claim \Leftrightarrow (\forall dA: \mathbb{N}, \forall dB: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right), GHZMeasureBiseparableBound.\operatorname{IsDensity}(\rho) \Rightarrow \operatorname{hHat}\left(\rho\right) \leq \operatorname{hHat}\left(\rho.\operatorname{traceRight}\right) + \operatorname{hHat}\left(LocalObservationPartialTraceEquivalence.\operatorname{partialTraceFirst}(\rho)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.claim` (`✓ std3`).

*Citation.* Y. Guo (2024). *Complete Genuine Multipartite Entanglement Monotone*. DOI: [10.1016/j.rinp.2024.107430](https://doi.org/10.1016/j.rinp.2024.107430). URL: <https://arxiv.org/abs/2301.00334v3>.

*Commentary.*

Guo, arXiv:2301.00334v3, p. 5: “We conjecture that ĥ is subadditive, i.e., ĥ(ρAB) ⩽ ĥ(ρA) + ĥ(ρB) (24) holds for any ρAB ∈ S^{AB}. In what follows, we always assume that hF′, hAF, and ĥ are subadditive, and that ĥ is concave.” The carrier Fin dA × Fin dB represents the tensor-product basis. GHZMeasureBiseparableBound.IsDensity means positive semidefinite with trace one. Matrix.traceRight traces out the second factor, and LocalObservationPartialTraceEquivalence.partialTraceFirst traces out the first. Hermitian proof arguments of hHat in the inequality are suppressed: positivity supplies the global proof, Matrix.IsHermitian.traceRight supplies the first marginal proof, and summing the Hermitian entry identities supplies the other.

**Theorem 1.3 (The conjectured inequality fails).**

$$\neg (\forall dA: \mathbb{N}, \forall dB: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right), GHZMeasureBiseparableBound.\operatorname{IsDensity}(\rho) \Rightarrow \operatorname{hHat}\left(\rho\right) \leq \operatorname{hHat}\left(\rho.\operatorname{traceRight}\right) + \operatorname{hHat}\left(LocalObservationPartialTraceEquivalence.\operatorname{partialTraceFirst}(\rho)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Y. Guo (2024). *Complete Genuine Multipartite Entanglement Monotone*. DOI: [10.1016/j.rinp.2024.107430](https://doi.org/10.1016/j.rinp.2024.107430). URL: <https://arxiv.org/abs/2301.00334v3>.

*Commentary.*

For r = 0, 1, let uᵣ(i,j) be 1 when j = i + r in Fin 5 and 0 otherwise. Put R = (1/10) • (Matrix.vecMulVec u₀ (star u₀) + Matrix.vecMulVec u₁ (star u₁)). Each summand is positive semidefinite. The squared norms of u₀ and u₁ are 5 and their cross dot products vanish. Consequently R has trace one and R² = (1/2) • R. Unitary spectral decomposition makes each eigenvalue either zero or 1/2; trace one and the decreasing eigenvalue order force its first two entries to be 1/2. Both partial traces are (1/5) • 1, so each of their eigenvalues is 1/5. Therefore hHat R = 1/2 while the two marginal values sum to 2/5; the gap is 1/10. All dimensions and all density matrices remain quantified in the negated proposition.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.hHat`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](../LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../../Foundation/FiniteDensityPurification.md)
