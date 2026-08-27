# Bayes Plausibility

## Abstract

Finite posterior mixtures reconstruct their prior distribution.

**Theorem 1.1 (The posterior mixture is the prior).**

$$\forall World \in Type, Signal \in Type,\; \left(\operatorname{Fintype}\left(World\right) \land \operatorname{Fintype}\left(Signal\right)\right) \Rightarrow \left(\forall mu \in \operatorname{PMF}\left(World\right), K \in World \to \operatorname{PMF}\left(Signal\right),\; \operatorname{let} jointLaw : Signal \times World \to \mathbb{R} := (s,omega) \mapsto \operatorname{toReal}\left(mu\left(omega\right)\right) \cdot \operatorname{toReal}\left(K\left(omega\right)\left(s\right)\right);\\{}\operatorname{let} lambda : Signal \to \mathbb{R} := s \mapsto \operatorname{marginal}\left(jointLaw, s\right);\\{}\operatorname{let} posterior : Signal \to \left(World \to \mathbb{R}\right) := (s,omega) \mapsto \operatorname{conditional}\left(jointLaw, s, omega\right);\\{}(omega \mapsto \sum_{s \in Signal} lambda\left(s\right) \cdot posterior\left(s, omega\right)) = (omega \mapsto \operatorname{toReal}\left(mu\left(omega\right)\right)) \land \left(\forall omega \in World,\; \sum_{s \in Signal} lambda\left(s\right) \cdot posterior\left(s, omega\right) = \operatorname{toReal}\left(mu\left(omega\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/BayesPlausibility.bayes_plausibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite world PMF and a PMF-valued finite signal kernel construct the displayed real joint law. Its canonical first marginal is the signal weight, and its canonical conditional is the posterior.

On a positive-weight signal fiber, multiplying the conditional by its marginal recovers the joint mass. On a zero-weight fiber, nonnegativity forces every joint mass in that fiber to vanish.

Summing the recovered joint masses over signals leaves the prior mass times the normalized signal-kernel mass. This proves both the function equality and its public pointwise form.

Repository and pinned-library searches found no exact theorem on this finite PMF/kernel carrier. The proof imports the existing marginal and conditional primitives and applies Mathlib's PMF normalization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/BayesPlausibility.bayes_plausibility`
- Dependency: [D5/S3/Divergence/ChainRule](../../Divergence/ChainRule.md)
