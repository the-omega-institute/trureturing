# Modified separable Wasserstein transport can exceed quantum transport

## Abstract

For two mixed states in dimension four, the modified separable transport cost is at least 15/16, whereas the modified De Palma–Trevisan cost is at most 9/16.

**Definition 1.1 (Separable couplings).**

$$\forall d: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{separableCouplings}\left(\rho, \sigma\right) = \{\gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right)| ((\operatorname{PosSemidef}\left(\gamma\right)) \land (\operatorname{trace}\left(\gamma\right) = 1)) \land ((\operatorname{IsSeparable}\left(\gamma\right)) \land ((\operatorname{partialTraceLeft}\left(\gamma\right) = \rho) \land (\operatorname{partialTraceRight}\left(\gamma\right) = \sigma)))\}$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCouplings` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

The coupling set uses the marginal convention of Tóth–Pitrik, Section III, equation (GMPC_distance_sep). Here partialTraceLeft is Tr₁, tracing out the first tensor factor, and partialTraceRight is Tr₂, tracing out the second. Thus Tr₁ γ = ρ and Tr₂ γ = σ. IsSeparable means a finite convex mixture γ = Σⱼ pⱼ Aⱼ ⊗ Bⱼ, where pⱼ are nonnegative real numbers summing to one and every Aⱼ and Bⱼ is positive semidefinite with trace one. The additional positivity and trace conditions in the displayed set are retained explicitly.

**Definition 1.2 (The quantum cost operator).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{quantumCostOperator}\left(H\right) = \frac{1}{2} \cdot (\sum_{n\in \operatorname{Fin}\left(N\right)} (\operatorname{kronecker}\left((H\left(n\right))^{T}, 1\right) - \operatorname{kronecker}\left(1, H\left(n\right)\right))^{2})$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumCostOperator` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section II, equation (DPT): the transpose is the ordinary matrix transpose in the chosen basis, rather than the conjugate transpose. The function kronecker denotes the tensor product of matrices, and 1 is the identity matrix of the indicated dimension. The factor 1/2 is included in the operator. The index n ranges over Fin N; the definition itself imposes no Hermitian hypothesis.

**Definition 1.3 (The separable cost operator).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{separableCostOperator}\left(H\right) = \frac{1}{2} \cdot (\sum_{n\in \operatorname{Fin}\left(N\right)} (\operatorname{kronecker}\left(H\left(n\right), 1\right) - \operatorname{kronecker}\left(1, H\left(n\right)\right))^{2})$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCostOperator` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section III, equation (GMPC_distance_sep): the separable transport cost has no transpose on H n. As in the quantum cost, the factor 1/2 multiplies the sum of squared matrix differences. This operator is defined for every finite complex matrix family.

**Definition 1.4 (The quantum coupling cost).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{quantumCost}\left(H, \gamma\right) = \operatorname{re}\left(\operatorname{trace}\left((\operatorname{quantumCostOperator}\left(H\right)) \cdot (\gamma)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumCost` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

The real cost is the real part of the trace of the quantum cost operator times γ. For Hermitian H and a density matrix γ this agrees with the trace objective in equation (DPT); taking the real part makes the definition real valued for arbitrary matrix arguments as well.

**Definition 1.5 (The separable coupling cost).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{separableCost}\left(H, \gamma\right) = \operatorname{re}\left(\operatorname{trace}\left((\operatorname{separableCostOperator}\left(H\right)) \cdot (\gamma)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCost` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

The real cost is the real part of the trace of the separable cost operator times γ, with the same factor 1/2 as equation (GMPC_distance_sep). Membership in the coupling set is a separate condition, rather than a hypothesis of this cost function.

**Definition 1.6 (The squared De Palma–Trevisan distance).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{quantumSquared}\left(H, \rho, \sigma\right) = \operatorname{sInf}\left(\{r: \mathbb{R}| \exists \gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right), (\gamma \in \{\gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right)| ((\operatorname{PosSemidef}\left(\gamma\right)) \land (\operatorname{trace}\left(\gamma\right) = 1)) \land ((\operatorname{partialTraceRight}\left(\gamma\right) = \sigma) \land (\operatorname{partialTraceLeft}\left(\gamma\right) = (\rho)^{T}))\}) \land (r = \operatorname{quantumCost}\left(H, \gamma\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumSquared` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section II, equation (DPT). The displayed coupling set is exactly couplings(ρ,σ): γ is positive semidefinite with trace one, Tr₂ γ = σ, and Tr₁ γ = ρᵀ. The real infimum sInf of the cost image expresses the source's minimization. Here sInf uses the total real-infimum convention, with value zero on empty sets and on sets unbounded below; the infimum estimates below concern nonempty sets bounded below. No square root is taken.

**Definition 1.7 (The squared separable distance).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{separableSquared}\left(H, \rho, \sigma\right) = \operatorname{sInf}\left(\{r: \mathbb{R}| \exists \gamma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right), (\gamma \in \operatorname{separableCouplings}\left(\rho, \sigma\right)) \land (r = \operatorname{separableCost}\left(H, \gamma\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableSquared` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section III, equation (GMPC_distance_sep). The real infimum is over separableCouplings(ρ,σ), so its marginals are Tr₁ γ = ρ and Tr₂ γ = σ without a transpose. It uses separableCost, rather than quantumCost. The definition is a real infimum of a cost image, with the same total-infimum convention as quantumSquared.

**Definition 1.8 (The modified quantum squared distance).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{modifiedQuantumSquared}\left(H, \rho, \sigma\right) = \operatorname{quantumSquared}\left(H, \rho, \sigma\right) - \frac{\operatorname{quantumSquared}\left(H, \rho, \rho\right) + \operatorname{quantumSquared}\left(H, \sigma, \sigma\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.modifiedQuantumSquared` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section II, equation (Dmod): subtract half the sum of the two quantum self-cost infima from the quantum cross-cost infimum. The notation for a modified squared distance names this real expression; it does not square a separately defined function.

**Definition 1.9 (The modified separable squared distance).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{modifiedSeparableSquared}\left(H, \rho, \sigma\right) = \operatorname{separableSquared}\left(H, \rho, \sigma\right) - \frac{\operatorname{separableSquared}\left(H, \rho, \rho\right) + \operatorname{separableSquared}\left(H, \sigma, \sigma\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.modifiedSeparableSquared` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Section III, equation (tildeDPTsep): subtract half the sum of the two separable self-cost infima from the separable cross-cost infimum. Every term uses the separable cost and the untransposed marginal convention.

**Definition 1.10 (The universal comparison in Conjecture 1).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall H: (\operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{IsHermitian}\left(H\left(n\right)\right)) \Rightarrow (\forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow (\operatorname{modifiedSeparableSquared}\left(H, \rho, \sigma\right) \le \operatorname{modifiedQuantumSquared}\left(H, \rho, \sigma\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim` (`✓ std3`).

*Citation.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Tóth–Pitrik, Conjecture 1, asserts that the modified separable squared distance is at most the modified De Palma–Trevisan squared distance for arbitrary mixed states. Here the assertion ranges over all natural dimensions d and family sizes N, all Hermitian complex matrix families H, and all density matrices ρ and σ. IsDensity means positive semidefinite with trace one. Pure states are included, and no invertibility or strict mixedness assumption is imposed. The literal d = 0 and N = 0 cases are retained in these quantifiers.

**Theorem 1.11 (A four-dimensional counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/toth-pitrik-2026-separable-wasserstein-comparison-refutation` (refuted) by `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"toth-pitrik-2026-separable-wasserstein-comparison-refutation","declaration_gid":"D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Géza Tóth; József Pitrik (2026). *Quantum Wasserstein distance and its relation to several types of fidelities*. URL: <https://arxiv.org/abs/2506.14523v6>.

*Commentary.*

Take d = 4 and N = 3 in the ordered basis e₀,e₁,e₂,e₃. Set ρ = diag(3,3,1,1)/8 and σ = diag(1,1,3,3)/8. Both are strictly positive density matrices. Let H₁ have rows (0,2,0,0), (2,0,0,0), (0,0,0,1), (0,0,1,0); let H₂ = diag(1,−1,2,−2); and let H₃ = T/4, where T interchanges e₀ with e₂ and e₁ with e₃. These three matrices are real symmetric, so the two cost operators coincide with C = C₀ + (I − T ⊗ T)/16, where C₀ = 5I − H₁ ⊗ H₁ − H₂ ⊗ H₂.

For v in the tensor product write P(v) = |v⟩⟨v|, without normalizing v. Let E be the diagonal projection onto |ij⟩ with i and j in different blocks {0,1} and {2,3}. Put a = |00⟩ − |11⟩, b₀ = |01⟩ − |10⟩, b₁ = |03⟩ − |12⟩, b₂ = |21⟩ − |30⟩, and b₃ = |23⟩ − |32⟩. The decomposable identity C₀ − I − 2E = A + Γ(B) holds with A = 3P(a) + 4P(b₀) + 2P(b₁) + 2P(b₂) + 6P(|23⟩) + 6P(|32⟩) + P(b₃) and B = P(b₀) + 2P(b₁) + 2P(b₂) + P(b₃). Here Γ transposes the second tensor factor. Both A and B are positive semidefinite. Every separable γ has positive partial transpose, so Re Tr((A + Γ(B))γ) ≥ 0. Its marginals give Re Tr(Eγ) = 1/2 + 2 Σᵢ∈{0,1},ⱼ∈{2,3} Re γᵢⱼ,ᵢⱼ ≥ 1/2. The remaining operator (I − T ⊗ T)/16 is positive semidefinite. Consequently every separable cross coupling has cost at least 1 + 2·(1/2) = 2.

For explicit separable self-couplings, take the unit vectors u₀ = (e₀ + e₁)/√2, u₁ = (e₀ − e₁)/√2, u₂ = e₂, and u₃ = e₃. The mixtures Σⱼ wⱼ P(uⱼ) ⊗ P(uⱼ), with weights (3,3,1,1)/8 and (1,1,3,3)/8, have both marginals ρ and both marginals σ, respectively. Each has cost 17/16, hence both separable self-cost infima are at most 17/16.

An explicit quantum cross coupling is P(|00⟩ + |11⟩)/8 + P(|20⟩ + |31⟩)/4 + P(|22⟩ + |33⟩)/8. It has trace one, Tr₁ γ = ρᵀ = ρ, Tr₂ γ = σ, and cost 9/16. The quantum cost operator is positive semidefinite: each Hermitian difference Hₙᵀ ⊗ I − I ⊗ Hₙ has a positive semidefinite square. Thus quantum costs on density matrices, and in particular both quantum self-cost infima, are nonnegative. It follows that the modified separable squared distance is at least 2 − 17/16 = 15/16, while the modified quantum squared distance is at most 9/16. Since 15/16 > 9/16, this pair contradicts Conjecture 1 of Tóth–Pitrik. The matrices, couplings and decomposable bound are the construction here; the distance definitions and conjectured comparison are from the cited source.

## References

- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.modifiedQuantumSquared`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.modifiedSeparableSquared`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumCost`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumCostOperator`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.quantumSquared`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCost`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCostOperator`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableCouplings`
- Truth anchor: `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.separableSquared`
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../Matrix/PartialTransposeTrace.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence](../QuantumChannels/LogNegativityCapacityResourceDependence.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
- Dependency: [D5/S3/QuantumContext/RankOfContextualityNonPowerTwo](../../QuantumContext/RankOfContextualityNonPowerTwo.md)
