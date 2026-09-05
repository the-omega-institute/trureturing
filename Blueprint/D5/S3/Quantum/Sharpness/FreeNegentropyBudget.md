# The Free-Negentropy Budget

## Abstract

Density-state sharpness is controlled by negentropy, with monotone forgetting and sharp endpoint laws.

**Definition 1.1 (The ordered density-state spectrum).**

$$\forall n \in Type, rho \in \operatorname{DensityState}\left(n\right),\; \left(\operatorname{Fintype}\left(n\right) \land \operatorname{DecidableEq}\left(n\right)\right) \Rightarrow \operatorname{stateSpectrum}\left(\rho\right) = \left(eigenvalues_{0}\right)\left(\operatorname{densityMatrix}\left(\rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.stateSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectrum is constructed from the canonical density matrix by taking the decreasing real eigenvalue family of its positive-semidefinite Hermitian representative. It is not defined from any target bound.

**Theorem 1.2 (Von Neumann entropy is Shannon entropy of the ordered spectrum).**

$$\forall n \in Type, rho \in \operatorname{DensityState}\left(n\right),\; \left(\operatorname{Fintype}\left(n\right) \land \operatorname{DecidableEq}\left(n\right)\right) \Rightarrow \operatorname{vonNeumannEntropy}\left(\rho\right) = \operatorname{shannonEntropy}\left(\operatorname{stateSpectrum}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-dimensional spectral calculus expands the trace-log definition over the density matrix eigenvalues. Reindexing those eigenvalues in decreasing order gives the stated Shannon entropy identity.

**Theorem 1.3 (Sharpness, forgetting, and endpoint budgets).**

$$\forall n \in Type, rho \in \operatorname{DensityState}\left(n\right),\; \left(\operatorname{Fintype}\left(n\right) \land \left(\operatorname{DecidableEq}\left(n\right) \land \operatorname{Nonempty}\left(n\right)\right)\right) \Rightarrow \operatorname{let} r: \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right) \to \mathbb{R} := \operatorname{stateSpectrum}\left(\rho\right); \\{}\operatorname{let} u: \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right) \to \mathbb{R} := (i: \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right) \mapsto \frac{1}{\operatorname{card}\left(n\right)}); \\{}\operatorname{let} q: \mathbb{R} \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{R}\right) := (x: \mathbb{R} \mapsto (i: \operatorname{Fin}\left(2\right) \mapsto \operatorname{ite}\left(i = 0, \frac{1}{2} + \frac{x}{2}, \frac{1}{2} - \frac{x}{2}\right))); \\{}\begin{gathered}\left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right),\; 0 \le r\left(i\right)\right) \land \sum_{i \in \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right)} r\left(i\right) = 1 \land\\{}\operatorname{Antitone}\left(r\right) \land\\{}\operatorname{vonNeumannEntropy}\left(\rho\right) = \operatorname{shannonEntropy}\left(r\right) \land\\{}\operatorname{IsGreatest}\left(\{v: \mathbb{R} \mid \exists a \in \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right) \to \mathbb{R},\; \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right),\; \left|a\left(i\right)\right| \le 1\right) \land \operatorname{spectralPairingCapacity}\left(r, a\right) = v\}, \operatorname{spectralSharpness}\left(r\right)\right) \land\\{}\operatorname{spectralSharpness}\left(r\right) \le 2 \cdot \operatorname{totalVariation}\left(r, u\right) \land 2 \cdot \operatorname{totalVariation}\left(r, u\right) \le \operatorname{sqrt}\left(2 \cdot \left(\operatorname{log}\left(\operatorname{card}\left(n\right)\right) - \operatorname{vonNeumannEntropy}\left(\rho\right)\right)\right) \land\\{}\operatorname{spectralSharpness}\left(r\right)^{2} \le 2 \cdot \left(\operatorname{log}\left(\operatorname{card}\left(n\right)\right) - \operatorname{vonNeumannEntropy}\left(\rho\right)\right) \land\\{}\forall sigma \in \operatorname{DensityState}\left(n\right), S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{card}\left(n\right)\right), \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right), \mathbb{R}\right),\; \left(\operatorname{doublyStochastic}\left(S\right) \land r = \operatorname{mulVec}\left(S, \operatorname{stateSpectrum}\left(sigma\right)\right)\right) \Rightarrow \begin{gathered}\operatorname{spectralSharpness}\left(r\right) \le \operatorname{spectralSharpness}\left(\operatorname{stateSpectrum}\left(sigma\right)\right) \land\\{}\operatorname{shannonEntropy}\left(\operatorname{stateSpectrum}\left(sigma\right)\right) \le \operatorname{shannonEntropy}\left(r\right) \land\\{}\operatorname{log}\left(\operatorname{card}\left(n\right)\right) - \operatorname{shannonEntropy}\left(r\right) \le \operatorname{log}\left(\operatorname{card}\left(n\right)\right) - \operatorname{shannonEntropy}\left(\operatorname{stateSpectrum}\left(sigma\right)\right) \land\\{}\forall a \in \operatorname{Fin}\left(\operatorname{card}\left(n\right)\right) \to \mathbb{R},\; \operatorname{Antitone}\left(a\right) \Rightarrow \operatorname{spectralPairingCapacity}\left(r, a\right) \le \operatorname{spectralPairingCapacity}\left(\operatorname{stateSpectrum}\left(sigma\right), a\right).\end{gathered} \land\\{}\forall x \in \mathbb{R},\; \left(0 \le x \land x \le 1\right) \Rightarrow \begin{gathered}\left(\forall i \in \operatorname{Fin}\left(2\right),\; 0 \le q\left(x\right)\left(i\right)\right) \land \sum_{i \in \operatorname{Fin}\left(2\right)} q\left(x\right)\left(i\right) = 1 \land\\{}\operatorname{Antitone}\left(q\left(x\right)\right) \land\\{}\operatorname{shannonEntropy}\left(q\left(x\right)\right) = \operatorname{shannonEntropy}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right)\right) \land\\{}\operatorname{spectralSharpness}\left(q\left(x\right)\right) = x \land\\{}2 \cdot \operatorname{totalVariation}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right), \operatorname{positiveBiasLaw}\left(0\right)\right) = x.\end{gathered} \land\\{}\operatorname{Tendsto}\left((x: \mathbb{R} \mapsto \frac{2 \cdot \operatorname{totalVariation}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right), \operatorname{positiveBiasLaw}\left(0\right)\right)}{\operatorname{sqrt}\left(2 \cdot \left(\operatorname{log}\left(2\right) - \operatorname{shannonEntropy}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right)\right)\right)\right)}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right) \land\\{}\operatorname{IsBigO}\left((x: \mathbb{R} \mapsto 2 \cdot \left(\operatorname{log}\left(2\right) - \operatorname{shannonEntropy}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right)\right)\right) - \left(2 \cdot \operatorname{totalVariation}\left(\operatorname{positiveBiasLaw}\left(\frac{x}{2}\right), \operatorname{positiveBiasLaw}\left(0\right)\right)\right)^{2} - \frac{x^{4}}{6}), \operatorname{nhds}\left(0\right), (x: \mathbb{R} \mapsto x^{6})\right) \land\\{}{\operatorname{spectralSharpness}\left(r\right) = 1 \Rightarrow \begin{gathered}\operatorname{rank}\left(\operatorname{densityMatrix}\left(\rho\right)\right) \le \left\lfloor\frac{\operatorname{card}\left(n\right)}{2}\right\rfloor \land\\{}\operatorname{vonNeumannEntropy}\left(\rho\right) \le \operatorname{log}\left(\operatorname{rank}\left(\operatorname{densityMatrix}\left(\rho\right)\right)\right) \land\\{}\operatorname{vonNeumannEntropy}\left(\rho\right) \le \operatorname{log}\left(\left\lfloor\frac{\operatorname{card}\left(n\right)}{2}\right\rfloor\right).\end{gathered}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.free_negentropy_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a density state on a nonempty finite carrier, let r be its ordered spectrum and u the uniform spectrum. Spectral sharpness is the greatest bounded spectral pairing and is at most twice total variation from u, which Pinsker bounds by the square root of twice the von Neumann entropy deficit. Squaring gives the quantitative free-negentropy budget.

A supplied doubly stochastic spectral mixing witness models forgetting. It decreases sharpness and every antitone pairing capacity, increases Shannon entropy, and therefore decreases the entropy deficit.

The canonical symmetric two-point law realizes the qubit endpoint. Its sharpness and twice-total-variation are the radius, the Pinsker ratio tends to one at the mixed endpoint, and the fourth-order residual has coefficient one sixth with a sixth-order remainder. At sharpness one, the density-matrix rank is at most half the dimension and controls the remaining entropy.

The source's random-spectrum trial count, floating-point alert review, and seven-digit numerical comparison are empirical certificate remarks outside the named theorem. The exact inequalities, limit, expansion, and rank endpoint are the formalized clauses.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.free_negentropy_budget`
- Truth anchor: `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.stateSpectrum`
- Truth anchor: `D5/S3/Quantum/Sharpness/FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../Divergence/VonNeumannEntropyPinching.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Sharpness/SpectralPairingCapacity](SpectralPairingCapacity.md)
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpnessDuality](SpectralSharpnessDuality.md)
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpnessSaturation](SpectralSharpnessSaturation.md)
- Dependency: [D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder](../../TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder.md)
- Dependency: [D5/S3/TotalVariation/SpectralSharpnessNegentropyBudget](../../TotalVariation/SpectralSharpnessNegentropyBudget.md)
