# The sharp odd-prime unentangled communication bound

## Abstract

For every odd prime dimension, unentangled quantum messages have sharp average success probability 2/(d + 1), including finite mixtures with shared classical randomness.

**Definition 1.1 (The joint matrix space).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.tensor}\left(A, B\right) = \operatorname{Matrix.reindex}\left(\operatorname{finProdFinEquiv}, \operatorname{finProdFinEquiv}, \operatorname{Matrix.kronecker}\left(A, B\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.tensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard Kronecker product is reindexed by finProdFinEquiv on both indices. Thus matrices on Fin m and Fin n give a matrix on Fin (m * n), representing the joint message space.

**Definition 1.2 (The two coordinate phases).**

$$\forall d \in \mathbb{N},\; \forall s \in \operatorname{ZMod}\left(d\right),\; \forall z \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right),\; \forall x \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.phase}\left(s, z, x\right) = \operatorname{Option.elim}\left(z, s \cdot x.1, (\lambda t: \operatorname{ZMod}\left(d\right), x.2 - 2 \cdot s \cdot t \cdot x.1)\right)$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.phase` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

For none, the phase is s times x.1, the pair's first coordinate. For some t, it is x.2 minus 2 times s times t times x.1. The Lean coordinates x.1 and x.2 correspond to the source coordinates x₀ and x₁, respectively; none represents the source input z = d.

**Definition 1.3 (The winning output).**

$$\forall d \in \mathbb{N},\; \forall z \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right),\; \forall x \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)),\; \forall y \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.win}\left(z, x, y\right) = \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.phase}\left(1, z, x\right) + \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.phase}\left(-1, z, y\right)$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.win` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

Equation (27) adds Alice's phase with sign one to Bob's phase with sign minus one. In the source's coordinate notation, win (some t) x y = x₁ + y₁ − 2t(x₀ − y₀), and win none x y = x₀ − y₀. Both expressions are in ZMod d.

**Definition 1.4 (Density matrices and joint measurements).**

$$\forall d \in \mathbb{N},\; [\operatorname{NeZero}\left(d\right)], \forall alpha \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall beta \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall M \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right),\; (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.Valid}\left((d := d), alpha, beta, M\right)) \Leftrightarrow ((\forall x \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)),\; (\operatorname{Matrix.PosSemidef}\left(alpha\left(x\right)\right)) \land (\operatorname{Matrix.trace}\left(alpha\left(x\right)\right) = 1)) \land ((\forall y \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)),\; (\operatorname{Matrix.PosSemidef}\left(beta\left(y\right)\right)) \land (\operatorname{Matrix.trace}\left(beta\left(y\right)\right) = 1)) \land ((\forall z \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right),\; \forall c \in \operatorname{ZMod}\left(d\right),\; \operatorname{Matrix.PosSemidef}\left(M\left(z, c\right)\right)) \land (\forall z \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right),\; \sum_{c: \operatorname{ZMod}\left(d\right)} (M\left(z, c\right)) = 1))))$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.Valid` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

For every input pair, Alice and Bob each send a positive semidefinite d-by-d matrix of trace one. For each z, Charlie's d effects are positive semidefinite matrices on the joint d²-dimensional space and sum to the identity. The effects may describe an entangled joint measurement.

**Definition 1.5 (The average success probability).**

$$\forall d \in \mathbb{N},\; [\operatorname{NeZero}\left(d\right)], \forall alpha \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall beta \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall M \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.score}\left((d := d), alpha, beta, M\right) = \frac{1}{(d: \mathbb{R})^{4} \cdot ((d: \mathbb{R}) + 1)} \cdot \sum_{x: (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right))} (\sum_{y: (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right))} (\sum_{z: \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right)} (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.tensor}\left(alpha\left(x\right), beta\left(y\right)\right) \cdot M\left(z, \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.win}\left(z, x, y\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.score` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

This is Equation (28), with p(c | x, y, z) = tr(α_x ⊗ β_y M_c|z) from Equation (19), and none the source's z = d. The two input pairs range independently over ZMod d × ZMod d, and Charlie's input ranges over Option (ZMod d). Taking Complex.re defines a real score for all matrices; for a valid strategy the trace is real and is the winning probability.

**Definition 1.6 (Shared classical randomness).**

$$\forall d \in \mathbb{N},\; [\operatorname{NeZero}\left(d\right)], \forall L \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall alpha \in \operatorname{Fin}\left(L\right) \to \left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall beta \in \operatorname{Fin}\left(L\right) \to \left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall M \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right)\right),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.mixtureScore}\left((d := d), q, alpha, beta, M\right) = \sum_{l: \operatorname{Fin}\left(L\right)} (q\left(l\right) \cdot \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.score}\left((d := d), alpha\left(l\right), beta\left(l\right), M\left(l\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.mixtureScore` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

A finite mixture uses one common index l for Alice's encoding, Bob's encoding and Charlie's measurement. The mixture score is their weighted sum. Nonnegative weights summing to one describe shared classical randomness, as allowed in Section V.

**Definition 1.7 (The upper bound and its attainment).**

$$(\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; (\operatorname{Nat.Prime}\left(d\right)) \Rightarrow ((\operatorname{Odd}\left(d\right)) \Rightarrow (((\forall alpha \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall beta \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall M \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right),\; (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.Valid}\left((d := d), alpha, beta, M\right)) \Rightarrow (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.score}\left((d := d), alpha, beta, M\right) \le \frac{2}{(d: \mathbb{R}) + 1})) \land (\forall L \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall alpha \in \operatorname{Fin}\left(L\right) \to \left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall beta \in \operatorname{Fin}\left(L\right) \to \left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall M \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right)\right),\; (\forall l \in \operatorname{Fin}\left(L\right),\; 0 \le q\left(l\right)) \Rightarrow ((\sum_{l: \operatorname{Fin}\left(L\right)} (q\left(l\right)) = 1) \Rightarrow ((\forall l \in \operatorname{Fin}\left(L\right),\; \operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.Valid}\left((d := d), alpha\left(l\right), beta\left(l\right), M\left(l\right)\right)) \Rightarrow (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.mixtureScore}\left((d := d), q, alpha, beta, M\right) \le \frac{2}{(d: \mathbb{R}) + 1}))))) \land (\exists alpha \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \exists beta \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \exists M \in \operatorname{Option}\left(\operatorname{ZMod}\left(d\right)\right) \to \left(\operatorname{ZMod}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d \cdot d\right), \operatorname{Fin}\left(d \cdot d\right), \mathbb{C}\right)\right),\; (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.Valid}\left((d := d), alpha, beta, M\right)) \land (\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.score}\left((d := d), alpha, beta, M\right) = \frac{2}{(d: \mathbb{R}) + 1})))))$$

*Formalization.* `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.claim` (`✓ std3`).

*Citation.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

Conjecture 1, Equation (29), asserts that the largest unentangled value is 2/(d + 1) for every odd prime d. The first two clauses bound every fixed strategy and every finite convex mixture, respectively. The final clause states attainment by a valid fixed strategy. Primality supplies the nonzero dimension required by Valid, score and mixtureScore.

**Theorem 1.8 (The sharp bound holds in every odd prime dimension).**

$$\operatorname{D5.S3.QuantumBounds.UnentangledOddPrimeCommunication.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.result` (`✓ std3`). ∎

*Resolves.* `Problems/bakhshinezhad-mehboudi-roch-i-carceller-tavakoli-2024-odd-prime-unentangled-bound` (proved) by `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bakhshinezhad-mehboudi-roch-i-carceller-tavakoli-2024-odd-prime-unentangled-bound","declaration_gid":"D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli (2024). *Scalable entanglement certification via quantum communication*. DOI: [10.1103/PRXQuantum.5.020319](https://doi.org/10.1103/PRXQuantum.5.020319). URL: <https://arxiv.org/abs/2401.00796v2>.

*Commentary.*

Character orthogonality expands the score into the constant contribution 1/d and a sum over nonzero Fourier modes. Each term pairs the Kronecker product of the two encoding coefficients with a Fourier coefficient of Charlie's POVM. Positivity of the trace of a product of positive semidefinite effects bounds the squared Frobenius norm of each measurement coefficient by d². Cauchy–Schwarz then bounds the real trace term by d/2 times the sum of the two squared encoding norms.

For either encoding sign s, the slope frequencies (s k, 0) for none and (−2s t k, k) for some t, with k nonzero, enumerate every nonzero frequency in (ZMod d)² exactly once. This uses that d is prime and odd. Parseval with the constant mode removed gives d² times the sum of the squared state norms minus the squared norm of their sum. Each density matrix has squared Frobenius norm at most one, while their sum has trace d² and squared norm at least d³. Hence the total nonzero-mode energy is at most d⁴ − d³ for each sender, giving the score bound 2/(d + 1). Nonnegative normalized mixtures preserve the bound.

For attainment, Alice and Bob send the computational-basis states labeled by x₀ and y₀. For none, Charlie measures their label difference and wins with probability one. For some t, the uniform effects (1/d) times the identity give success probability 1/d. Averaging over the d + 1 inputs gives (1 + d(1/d))/(d + 1) = 2/(d + 1).

## References

- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.Valid`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.claim`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.mixtureScore`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.phase`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.result`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.score`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.tensor`
- Truth anchor: `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.win`
- Dependency: [D5/S3/Fourier/FullBispectrumStability](../Fourier/FullBispectrumStability.md)
- Dependency: [D5/S3/Fourier/SparseGeneratorFamily](../Fourier/SparseGeneratorFamily.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall](../Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Quantum/Matrix/CartesianVariance.md)
