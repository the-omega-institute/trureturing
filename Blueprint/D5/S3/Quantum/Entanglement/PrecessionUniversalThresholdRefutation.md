# Singlet padding and the universal precession threshold

## Abstract

A spin-1/2 singlet tensored with the spin-3/2 endpoint state scores 3/4 at K = 3 while remaining separable across the pair–rest bipartition. The threshold 23/32 therefore fails to certify genuine multipartite entanglement.

**Definition 1.1 (Local operator).**

$$\forall N \in (\mathbb{N}),\; \forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; \forall n \in (\operatorname{Fin}\left(N\right)),\; \forall A \in (\operatorname{Matrix}\left((\operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), (\operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), \mathbb{C}\right)),\; \forall x \in (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)),\; \forall y \in (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)),\; \operatorname{siteOperator}\left(j, n, A, x, y\right) = \operatorname{A}\left(\operatorname{x}\left(n\right), \operatorname{y}\left(n\right)\right) \cdot \prod_{r \in \operatorname{Finset.erase}\left(Finset.univ, n\right)} \operatorname{if}\left(\operatorname{x}\left(r\right) = \operatorname{y}\left(r\right), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.siteOperator` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The operator on site n is tensored with identity operators at every other site. The configuration basis is the dependent product of Fin (j n + 1), where j n is twice the physical spin and ℏ = 1.

**Definition 1.2 (Total precession observable).**

$$\forall N \in (\mathbb{N}),\; \forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; \forall K \in (\mathbb{N}),\; \forall k \in (\operatorname{Fin}\left(K\right)),\; \operatorname{ensembleJ}\left(j, K, k\right) = \operatorname{HSMul.hSMul}\left((\operatorname{Real.cos}\left(\operatorname{PrecessionSpinOneSeparableBound.theta}\left(K, k\right)\right): \mathbb{C}), \sum_{n: \operatorname{Fin}\left(N\right)} \operatorname{siteOperator}\left(j, n, \operatorname{PrecessionSpinOneSeparableBound.Jx}\left(\operatorname{j}\left(n\right)\right)\right)\right) + \operatorname{HSMul.hSMul}\left((\operatorname{Real.sin}\left(\operatorname{PrecessionSpinOneSeparableBound.theta}\left(K, k\right)\right): \mathbb{C}), \sum_{n: \operatorname{Fin}\left(N\right)} \operatorname{siteOperator}\left(j, n, \operatorname{PrecessionSpinOneSeparableBound.Jy}\left(\operatorname{j}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.ensembleJ` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The source states: "In each round, one system is prepared in some state, then its total angular momentum is measured along one of the directions" J_k := cos(2πk/K)J_x + sin(2πk/K)J_y, Eq. (1), PDF p. 2. It then uses J_k = Σ_n J_k^(j_n), Eqs. (4)–(6), PDF p. 3. The spin matrices Jx and Jy and the angle theta are the existing spin definitions; the total components are literal sums of site operators.

**Definition 1.3 (Averaged spectral weight).**

$$\forall N \in (\mathbb{N}),\; \forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; \forall K \in (\mathbb{N}),\; \forall h \in (\forall k: \operatorname{Fin}\left(K\right), \operatorname{Matrix.IsHermitian}\left(\operatorname{ensembleJ}\left(j, K, k\right)\right)),\; \operatorname{ensembleQ}\left(j, K\right) = \operatorname{HSMul.hSMul}\left(\frac{1}{(K: \mathbb{C})}, \sum_{k: \operatorname{Fin}\left(K\right)} \operatorname{PrecessionSpinOneSeparableBound.pos}\left(\operatorname{h}\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.ensembleQ` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The source states: "Meanwhile, the expected score for a quantum system in the state ρ is given by P_K = tr(ρ Q_K), with" Q_K := (1/K) Σ_k pos(J_k), Eq. (3), PDF p. 2. pos is the existing Hermitian spectral calculus with weight (1+sgn(m))/2, including half weight at zero. The displayed h supplies a Hermiticity proof for each ensembleJ j K k. Proof irrelevance makes the expression independent of that choice.

**Definition 1.4 (Conjectured threshold).**

$$\forall K \in (\mathbb{N}),\; \operatorname{conjecturedThreshold}\left(K\right) = \operatorname{if}\left(K = 3, \frac{23}{32}, \operatorname{if}\left(K = 5, \frac{(69 + \operatorname{Real.sqrt}\left(181\right))}{128}, \frac{1}{2} \cdot (1 + \frac{\operatorname{PrecessionSpinOneSeparableBound.c}\left(K\right) \cdot ((K - 1): \mathbb{R})}{((K + 1): \mathbb{R})})\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.conjecturedThreshold` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

Result 4, PDF p. 9, defines the threshold piecewise: 23/32 for K = 3, (69+√181)/128 for K = 5, and ½[1+c_K(K−1)/(K+1)] otherwise. c K is the existing normalized central binomial coefficient 2^{−(K−1)} binom(K−1, (K−1)/2). Its (K−1)/2 index uses natural floor division; the displayed threshold ratio casts K−1 and K+1 into ℝ.

**Definition 1.5 (Separability over one cut).**

$$\forall N \in (\mathbb{N}),\; \forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; \forall S \in (\operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right)),\; \forall rho \in (\operatorname{Matrix}\left((\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), \mathbb{C}\right)),\; \operatorname{SeparableAcross}\left(j, S, rho\right) \Leftrightarrow (\exists m \in (\mathbb{N}),\; \exists p \in (\operatorname{Fin}\left(m\right) \to \mathbb{R}),\; \exists A \in (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\forall n: S, \operatorname{Fin}\left(\operatorname{j}\left(\operatorname{val}\left(n\right)\right) + 1\right)), (\forall n: S, \operatorname{Fin}\left(\operatorname{j}\left(\operatorname{val}\left(n\right)\right) + 1\right)), \mathbb{C}\right)),\; \exists B \in (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\forall n: S^{c}, \operatorname{Fin}\left(\operatorname{j}\left(\operatorname{val}\left(n\right)\right) + 1\right)), (\forall n: S^{c}, \operatorname{Fin}\left(\operatorname{j}\left(\operatorname{val}\left(n\right)\right) + 1\right)), \mathbb{C}\right)),\; (\forall r \in (\operatorname{Fin}\left(m\right)),\; \operatorname{p}\left(r\right) \ge 0) \land \left((\sum_{r: \operatorname{Fin}\left(m\right)} \operatorname{p}\left(r\right) = 1) \land \left((\forall r \in (\operatorname{Fin}\left(m\right)),\; (\operatorname{GHZMeasureBiseparableBound.IsDensity}\left(\operatorname{A}\left(r\right)\right)) \land (\operatorname{GHZMeasureBiseparableBound.IsDensity}\left(\operatorname{B}\left(r\right)\right))) \land (\forall x \in (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)),\; \forall y \in (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)),\; \operatorname{rho}\left(x, y\right) = \sum_{r: \operatorname{Fin}\left(m\right)} (\operatorname{p}\left(r\right): \mathbb{C}) \cdot \operatorname{A}\left(r, (\lambda n: S, \operatorname{x}\left(\operatorname{val}\left(n\right)\right)), (\lambda n: S, \operatorname{y}\left(\operatorname{val}\left(n\right)\right))\right) \cdot \operatorname{B}\left(r, (\lambda n: S^{c}, \operatorname{x}\left(\operatorname{val}\left(n\right)\right)), (\lambda n: S^{c}, \operatorname{y}\left(\operatorname{val}\left(n\right)\right))\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.SeparableAcross` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The source states: "With these notations, a state ρ_{𝐉,𝐉ᶜ} of a spin ensemble is separable over the 𝐉-𝐉ᶜ bipartition if ρ_{𝐉,𝐉ᶜ} = Σ_k p_k ρ_{𝐉,k} ⊗ ρ_{𝐉ᶜ,k}, where ρ_{𝐉,k} (or ρ_{𝐉ᶜ,k}) is a state within the subspace ⊗_{j∈𝐉} ℋ^(j) (or ⊗_{j′∈𝐉ᶜ} ℋ^(j′))." PDF p. 3. The probabilities are nonnegative and sum to one; both factors are normalized density matrices. Tensor-product entries are pulled back by restriction of configurations to the two complementary sets. The finite unnormalized PSD cone separableCone does not include these normalization conditions or these dependent local dimensions.

**Definition 1.6 (Genuine multipartite entanglement).**

$$\forall N \in (\mathbb{N}),\; \forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; \forall rho \in (\operatorname{Matrix}\left((\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), \mathbb{C}\right)),\; \operatorname{SpinGME}\left(j, rho\right) \Leftrightarrow (\neg (\exists m \in (\mathbb{N}),\; \exists p \in (\operatorname{Fin}\left(m\right) \to \mathbb{R}),\; \exists S \in (\operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right)),\; \exists sigma \in (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), \mathbb{C}\right)),\; (\forall r \in (\operatorname{Fin}\left(m\right)),\; \operatorname{p}\left(r\right) \ge 0) \land \left((\sum_{r: \operatorname{Fin}\left(m\right)} \operatorname{p}\left(r\right) = 1) \land \left((\forall r \in (\operatorname{Fin}\left(m\right)),\; (\operatorname{Finset.Nonempty}\left(\operatorname{S}\left(r\right)\right)) \land \left((\operatorname{Finset.Nonempty}\left((\operatorname{S}\left(r\right))^{c}\right)) \land \left((\operatorname{GHZMeasureBiseparableBound.IsDensity}\left(\operatorname{sigma}\left(r\right)\right)) \land (\operatorname{SeparableAcross}\left(j, \operatorname{S}\left(r\right), \operatorname{sigma}\left(r\right)\right))\right)\right)) \land (rho = \sum_{r: \operatorname{Fin}\left(m\right)} \operatorname{HSMul.hSMul}\left((\operatorname{p}\left(r\right): \mathbb{C}), \operatorname{sigma}\left(r\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.SpinGME` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The source states: "Conversely, ρ_GME is GME if it is not a convex combination of states separable over any bipartition 𝐉: that is, ρ_GME ≠ Σ_𝐉 p_𝐉 ρ_{𝐉,𝐉ᶜ}." PDF p. 3. Each summand may use its own cut; both sides of every cut are nonempty. Repeated cuts in a finite mixture allow arbitrary finite decompositions and do not impose a preferred bipartition.

**Definition 1.7 (Huynh-Vu–Zaw–Scarani Conjecture 3).**

$$claim \Leftrightarrow (\forall K \in (\mathbb{N}),\; (\operatorname{Odd}\left(K\right)) \Rightarrow ((K \ge 3) \Rightarrow (\forall N \in (\mathbb{N}),\; (N \ge 2) \Rightarrow (\forall j \in (\operatorname{Fin}\left(N\right) \to \mathbb{N}),\; (\forall n \in (\operatorname{Fin}\left(N\right)),\; \operatorname{j}\left(n\right) \ge 1) \Rightarrow (\forall rho \in (\operatorname{Matrix}\left((\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), (\forall n: \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(\operatorname{j}\left(n\right) + 1\right)), \mathbb{C}\right)),\; (\operatorname{GHZMeasureBiseparableBound.IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{conjecturedThreshold}\left(K\right) < \operatorname{Complex.re}\left((\operatorname{Matrix.trace}\left(rho \cdot \operatorname{ensembleQ}\left(j, K\right)\right))\right)) \Rightarrow (\operatorname{SpinGME}\left(j, rho\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.claim` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The source states: "Consider a spin ensemble. Perform the precession protocol with odd K ≥ 3 on the total angular momentum of the system. If the score P_K > 𝐏_K^conj is obtained, then the spin ensemble is GME." Conjecture 3, PDF p. 9. N ≥ 2 counts particles, j n ≥ 1 encodes all positive half-integer spins as twice their value, ρ ranges over every density matrix on the full tensor product, and the score is the real part of trace (ρ * ensembleQ j K).

**Theorem 1.8 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/huynh-vu-zaw-scarani-2023-universal-gme-threshold-refutation` (refuted) by `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"huynh-vu-zaw-scarani-2023-universal-gme-threshold-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. DOI: [10.1103/PhysRevA.109.042402](https://doi.org/10.1103/PhysRevA.109.042402). URL: <https://arxiv.org/abs/2311.00806v2>.

*Commentary.*

The ensemble has spins {1/2,1/2,3/2}. The normalized two-spin singlet projector is tensored with the normalized projector onto the difference of the two extreme spin-3/2 basis vectors. For every remaining spin list, every matrix on its configuration space and every K, prepending two spin-1/2 particles in their normalized singlet preserves the literal precession score. Splitting the sum of site operators gives the pair observable tensored with the rest identity plus the pair identity tensored with the rest observable. The pair's angular momentum annihilates the singlet, so finite spectral calculus preserves its embedding of the remaining system. The score is 3/4 > 23/32. A one-term convex decomposition across the pair–rest cut establishes that the state is not GME.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.SeparableAcross`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.SpinGME`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.conjecturedThreshold`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.ensembleJ`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.ensembleQ`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.siteOperator`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](PrecessionSpinOneSeparableBound.md)
- Dependency: [D5/S3/Resource/CompositeConeProperness](../../Resource/CompositeConeProperness.md)
