# Collective dephasing can preserve negativity while changing the state

## Abstract

A nonstationary two-qutrit density matrix has constant positive negativity under Ali's collective dephasing.

The computational basis is ordered (0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2). Each local index belongs to Fin 3. All matrices below act on ℂ³ ⊗ ℂ³, and H denotes the conjugate transpose. Write γ(Γ,t) for gammaFactor(Γ,t), D₁ for kraus1, D₂ for kraus2, D₃ for kraus3, Φ for evolve, and N for negativity. Real diagonal entries are embedded in ℂ. The definitions allow all real Γ and t; the dephasing claim imposes Γ > 0 and t ≥ 0. The real square root is nonnegative on nonnegative inputs and is zero on nonpositive inputs.

**Definition 1.1 (The damping factor).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\operatorname{gammaFactor}\left(\Gamma, t\right) = \operatorname{exp}\left(-\frac{\Gamma \cdot t}{2}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.gammaFactor` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Section II defines γ = exp(−Γt/2).

**Definition 1.2 (The first auxiliary coefficient).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\operatorname{omega1}\left(\Gamma, t\right) = \sqrt{1 - \operatorname{gammaFactor}\left(\Gamma, t\right)^{2}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega1` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Section II defines ω₁ = √(1−γ²), using the nonnegative real square root.

**Definition 1.3 (The second auxiliary coefficient).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\operatorname{omega2}\left(\Gamma, t\right) = -\operatorname{gammaFactor}\left(\Gamma, t\right)^{2} \cdot \sqrt{1 - \operatorname{gammaFactor}\left(\Gamma, t\right)^{2}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega2` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Section II defines ω₂ = −γ²√(1−γ²).

**Definition 1.4 (The third auxiliary coefficient).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\operatorname{omega3}\left(\Gamma, t\right) = \left(1 - \operatorname{gammaFactor}\left(\Gamma, t\right)^{2}\right) \cdot \sqrt{1 + \operatorname{gammaFactor}\left(\Gamma, t\right)^{2}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega3` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Section II defines ω₃ = (1−γ²)√(1+γ²).

**Definition 1.5 (The first diagonal Kraus operator).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\left(\operatorname{kraus1}\left(\Gamma, t\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right) = \operatorname{diag}\left(\operatorname{gammaFactor}\left(\Gamma, t\right), 1, 1, 1, \operatorname{gammaFactor}\left(\Gamma, t\right), 1, 1, 1, \operatorname{gammaFactor}\left(\Gamma, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus1` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

The entries of D₁ follow the stated computational basis order. The factor γ occurs exactly at (0,0), (1,1), and (2,2).

**Definition 1.6 (The second diagonal Kraus operator).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\left(\operatorname{kraus2}\left(\Gamma, t\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right) = \operatorname{diag}\left(\operatorname{omega1}\left(\Gamma, t\right), 0, 0, 0, \operatorname{omega2}\left(\Gamma, t\right), 0, 0, 0, \operatorname{omega2}\left(\Gamma, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus2` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

In the same basis order, D₂ has entries ω₁ at (0,0), ω₂ at (1,1) and (2,2), and zero elsewhere.

**Definition 1.7 (The third diagonal Kraus operator).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\left(\operatorname{kraus3}\left(\Gamma, t\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right) = \operatorname{diag}\left(0, 0, 0, 0, \operatorname{omega3}\left(\Gamma, t\right), 0, 0, 0, \operatorname{omega3}\left(\Gamma, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus3` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

In the same basis order, D₃ has entries ω₃ at (1,1) and (2,2), and zero elsewhere.

**Definition 1.8 (Collective dephasing evolution).**

$$\forall \left(\Gamma: \mathbb{R}\right), \left(\forall \left(t: \mathbb{R}\right), \left(\forall \left(r: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\operatorname{evolve}\left(\Gamma, t, r\right) = \sum_{k=1}^{3} \left(\left(D_{k}\right)\left(\Gamma, t\right)\right)^{H} \cdot r \cdot \left(D_{k}\right)\left(\Gamma, t\right) = \left(\operatorname{kraus1}\left(\Gamma, t\right)\right)^{H} \cdot r \cdot \operatorname{kraus1}\left(\Gamma, t\right) + \left(\operatorname{kraus2}\left(\Gamma, t\right)\right)^{H} \cdot r \cdot \operatorname{kraus2}\left(\Gamma, t\right) + \left(\operatorname{kraus3}\left(\Gamma, t\right)\right)^{H} \cdot r \cdot \operatorname{kraus3}\left(\Gamma, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.evolve` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Equation (3) gives ΦΓ,t(ρ) = Σₖ DₖᴴρDₖ for k = 1, 2, 3. The displayed three-term sum fixes the order of the adjoints and products.

**Definition 1.9 (Constant positive negativity would imply stationarity).**

$$\operatorname{claim} \Leftrightarrow \forall \left(\Gamma: \mathbb{R}\right), \left(\left(0 < \Gamma\right) \Rightarrow \left(\forall \left(r: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{PosSemidef}\left(r\right)\right) \Rightarrow \left(\left(\operatorname{Tr}\left(r\right) = 1\right) \Rightarrow \left(\left(0 < \operatorname{negativity}\left(r\right)\right) \Rightarrow \left(\left(\forall \left(t: \mathbb{R}\right), \left(\left(0 \le t\right) \Rightarrow \left(\operatorname{negativity}\left(\operatorname{evolve}\left(\Gamma, t, r\right)\right) = \operatorname{negativity}\left(r\right)\right)\right)\right) \Rightarrow \left(\forall \left(t: \mathbb{R}\right), \left(\left(0 \le t\right) \Rightarrow \left(\operatorname{evolve}\left(\Gamma, t, r\right) = r\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.claim` (`✓ std3`).

*Citation.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Section I says that time-invariant entanglement allows the quantum state to change while its entanglement remains constant throughout the dynamics. Section V conjectures: "under current dynamics, this feature of time-invariant entanglement may not exist for qutrit-qutrit systems." With the negativity used in Section III as the entanglement measure, claim states that every positive semidefinite unit-trace initial matrix with constant strictly positive negativity is stationary for all t ≥ 0. It quantifies over every Γ > 0 and every such initial matrix.

Negativity is N(ρ) = (‖ρ^{T_B}‖₁−1)/2. The partial transpose exchanges the second subsystem indices. The trace norm is Tr √(AᴴA); its real part is explicit below, matching the real-valued convention. These formulas apply to every complex matrix, with no density hypothesis in the definitions themselves.

$$
\forall \left(r: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\operatorname{negativity}\left(r\right) = \frac{\left\lVert r^{T_{B}} \right\rVert_{1} - 1}{2}\right)
$$

$$
\forall \left(r: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(k: \operatorname{Fin}\left(3\right)\right), \left(\forall \left(l: \operatorname{Fin}\left(3\right)\right), \left(\left(r^{T_{B}}\right)_{\left(i,j\right),\left(k,l\right)} = \left(r\right)_{\left(i,l\right),\left(k,j\right)}\right)\right)\right)\right)\right)
$$

$$
\forall \left(M: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \left(\operatorname{Fin}\left(3\right)\times\operatorname{Fin}\left(3\right)\right), \mathbb{C}\right)\right), \left(\left\lVert M \right\rVert_{1} = \operatorname{Re}\left(\operatorname{Tr}\left(\sqrt{\left(M\right)^{H} \cdot M}\right)\right)\right)
$$

**Theorem 1.10 (A nonstationary state with negativity one quarter).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ali-2018-qutrit-collective-dephasing-invariant-negativity-refutation` (refuted) by `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ali-2018-qutrit-collective-dephasing-invariant-negativity-refutation","declaration_gid":"D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mazhar Ali (2019). *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*. DOI: [10.1142/s0217732319501025](https://doi.org/10.1142/s0217732319501025). URL: <https://arxiv.org/abs/1810.01123v1>.

*Commentary.*

Take Γ = 2 and ρ₀ = ¾|φ⟩⟨φ| + ¼|χ⟩⟨χ|, where φ = (|01⟩+|10⟩)/√2 and χ = (|00⟩+|11⟩)/√2. The two normalized vectors give ρ₀ ⪰ 0 and Tr ρ₀ = 1. For t ≥ 0 put g = γ(2,t) = exp(−t), so 0 < g ≤ 1, and set u₊ = |00⟩+|11⟩, u₋ = |00⟩−|11⟩, w₊ = |01⟩+|10⟩, w₋ = |01⟩−|10⟩.

The evolved matrix is Φ₂,t(ρ₀) = (3/8)w₊w₊ᴴ + ((1+g⁴)/16)u₊u₊ᴴ + ((1−g⁴)/16)u₋u₋ᴴ. Indeed γ²+ω₁² = 1, γ²+ω₂²+ω₃² = 1, and γ²+ω₁ω₂ = γ⁴. Thus only the (00,11) and (11,00) entries change, from 1/8 to g⁴/8.

Its partial transpose is A−B, where A = (1/4)u₊u₊ᴴ + ((3+g⁴)/16)w₊w₊ᴴ + ((3−g⁴)/16)w₋w₋ᴴ and B = (1/8)u₋u₋ᴴ. All coefficients are nonnegative, so A and B are positive semidefinite. Orthogonality of u₋ to u₊, w₊, and w₋ gives AB = 0. Their traces are Tr A = 5/4 and Tr B = 1/4; hence Tr A + Tr B = 3/2. The trace norm of A−B is therefore 3/2, and N(Φ₂,t(ρ₀)) = N(ρ₀) = 1/4 for every t ≥ 0.

At t = 1 the (00,11) entry is exp(−4)/8 < 1/8, so Φ₂,1(ρ₀) ≠ ρ₀. This contradicts claim. The construction uses a two-qubit corner of the two-qutrit space: a stationary Bell component accompanies a changing component without changing the negative part of the partial transpose. It supplies time-invariant positive negativity for the dynamics specified by Ali.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.evolve`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.gammaFactor`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus1`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus2`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.kraus3`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega1`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega2`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.omega3`
- Truth anchor: `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence](../QuantumChannels/LogNegativityCapacityResourceDependence.md)
- Dependency: [D5/S3/QuantumBounds/NegativityReductionInclusionRefutation](../../QuantumBounds/NegativityReductionInclusionRefutation.md)
