# Robust Safety Under Model Expansion

## Abstract

Enlarging the audited model family can only shrink the robust safe-action set.

**Theorem 1.1 (Model expansion shrinks the robust safe set).**

$$\begin{gathered}\forall Model, Action: \operatorname{Type},\\{}risk: Model \to Action \to \mathbb{R}, alpha: \mathbb{R},\\{}\mathcal{M}, \mathcal{M}': \operatorname{Set}\left(Model\right),\\{}\mathcal{M} \subseteq \mathcal{M}' \Rightarrow \\{}\{u: Action \mid \forall m \in \mathcal{M}', \operatorname{risk}\left(m, u\right) \leq alpha\} \subseteq \{u: Action \mid \forall m \in \mathcal{M}, \operatorname{risk}\left(m, u\right) \leq alpha\}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/RobustSafetyModelMonotonicity.model_uncertainty_expansion_shrinks_safe_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A safe action must keep the supplied risk below the threshold for every admitted model. Any action satisfying this condition for an expanded model family also satisfies it for the original subfamily.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/RobustSafetyModelMonotonicity.model_uncertainty_expansion_shrinks_safe_set`
