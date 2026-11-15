# Lopes Oliveira Wasserstein Refutation

## Abstract

LopesOliveiraWassersteinRefutation

The registered claim is the preregistered fixed-classical-target extension of the authors' section 8 similar-expression question. It ranges over every integer d at least 2, every real Holder potential on the original positive-index full shift, and every Borel probability law, with one finite real c depending on d and the potential. It explicitly requires the unique invariant classical KS variational equilibrium for that same potential. KS entropy is the supremum over all finite measurable partitions of the limiting normalized entropy of their iterated joins. The binary constant potential minus log 2 has the proved actual unique fair Bernoulli equilibrium. Its pressure-maximizing noninvariant comparison law has zero deficit and transport distance at least 1/8, so no real c satisfies the displayed inequality. The contradiction includes negative and zero c. There is no restriction to invariant, absolutely continuous, full-support or Markov comparison laws and no extra logarithmic-integrability hypothesis. This settles that fixed extension only; it does not claim to settle every interpretation of the authors' broader open question, and it uses neither a replacement equilibrium nor a finite-tail surrogate.

**Definition 1.1 (IsClassicalEquilibrium).**

$$\forall d \in \mathbb{N},\; \forall phi \in \operatorname{Omega}\left(d\right) \to \mathbb{R},\; \forall mu \in \operatorname{Measure}\left(\operatorname{Omega}\left(d\right)\right),\; \operatorname{IsClassicalEquilibrium}\left(phi, mu\right) \Leftrightarrow \left(\operatorname{IsProbabilityMeasure}\left(mu\right) \land \left(\exists hT \in \operatorname{MeasurePreserving}\left(shift, mu, mu\right),\; \forall rho \in \operatorname{Measure}\left(\operatorname{Omega}\left(d\right)\right),\; \operatorname{IsProbabilityMeasure}\left(rho\right) \Rightarrow \left(\forall hR \in \operatorname{MeasurePreserving}\left(shift, rho, rho\right),\; \int_{x:\operatorname{Omega}\left(d\right)}phi\left(x\right) \mathrm{d}rho+\operatorname{ksEntropy}\left(hR\right) \le \int_{x:\operatorname{Omega}\left(d\right)}phi\left(x\right) \mathrm{d}mu+\operatorname{ksEntropy}\left(hT\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsClassicalEquilibrium` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.2 (IsUniqueClassicalEquilibrium).**

$$\forall d \in \mathbb{N},\; \forall phi \in \operatorname{Omega}\left(d\right) \to \mathbb{R},\; \forall mu \in \operatorname{Measure}\left(\operatorname{Omega}\left(d\right)\right),\; \operatorname{IsUniqueClassicalEquilibrium}\left(phi, mu\right) \Leftrightarrow \left(\operatorname{IsClassicalEquilibrium}\left(phi, mu\right) \land \left(\forall rho \in \operatorname{Measure}\left(\operatorname{Omega}\left(d\right)\right),\; \operatorname{IsClassicalEquilibrium}\left(phi, rho\right) \Rightarrow rho = mu\right)\right)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsUniqueClassicalEquilibrium` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.3 (claim).**

$$claim \Leftrightarrow \left(\forall d \in \mathbb{Z},\; 2 \le d \Rightarrow \left(\forall phi \in \operatorname{Omega}\left(\operatorname{toNat}\left(d\right)\right) \to \mathbb{R},\; \operatorname{IsHolder}\left(phi\right) \Rightarrow \left(\exists mu \in \operatorname{Measure}\left(\operatorname{Omega}\left(\operatorname{toNat}\left(d\right)\right)\right),\; \operatorname{IsUniqueClassicalEquilibrium}\left(phi, mu\right) \land \left(\exists c \in \mathbb{R},\; \forall nu \in \operatorname{Measure}\left(\operatorname{Omega}\left(\operatorname{toNat}\left(d\right)\right)\right),\; \operatorname{IsProbabilityMeasure}\left(nu\right) \Rightarrow \operatorname{wassersteinOne}\left(nu, mu\right) \le c\cdot\sqrt{\operatorname{niPressure}\left(phi\right)-\operatorname{niEntropy}\left(nu\right)-\int_{x:\operatorname{Omega}\left(\operatorname{toNat}\left(d\right)\right)}phi\left(x\right) \mathrm{d}nu}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.4 (binary classical equilibrium).**

$$\operatorname{IsUniqueClassicalEquilibrium}\left(Function.const(\operatorname{Omega}\left(2\right),-\log2), SourceEquilibrium.fair\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.binary_classical_equilibrium` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (result).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lopes-oliveira-2026-fixed-classical-target-wasserstein` (refuted) by `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lopes-oliveira-2026-fixed-classical-target-wasserstein","declaration_gid":"D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply. The result refutes the registered fixed-classical-target extension; the authors' broader similar-expression question remains outside this settlement.

## References

- Truth anchor: `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsClassicalEquilibrium`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsUniqueClassicalEquilibrium`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.binary_classical_equilibrium`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.claim`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/FairEquilibrium](KolmogorovSinai/FairEquilibrium.md)
