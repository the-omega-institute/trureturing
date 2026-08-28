# Budget Envelope Completion

## Abstract

Nonnegative budget layers are cofinal among finite residual families, so their escape envelope converges to the all-finite infimum.

**Theorem 1.1 (The finite-family budget envelope has the all-finite limit).**

$$\begin{aligned}\forall I, X, C, Y: \operatorname{Type},\\V: I \to \operatorname{Type}, Gamma: \operatorname{Set}\left(I\right),\\d: \forall i: I, X \to \operatorname{V}\left(i\right),\\q: X \to C, T: X \to Y,\\c: I \to \mathbb{R}, nu: \operatorname{EscapeWeight}\left(X \times X\right),\\\operatorname{let} M_{0} = \operatorname{mass}\left(nu, \operatorname{defectRelation}\left(q, T\right)\right), \operatorname{m}\left(S\right) = \operatorname{mass}\left(nu, \operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{finiteSelectionSupplement}\left(Gamma, d, S\right)\right), T\right)\right),\\\operatorname{C}\left(S\right) = \operatorname{finiteSelectionCost}\left(Gamma, c, S\right),\\\operatorname{M}\left(L\right) = \operatorname{sInf}\left(\{\operatorname{m}\left(S\right) \mid S \in \operatorname{Finset}\left(Gamma\right), \operatorname{C}\left(S\right) \leq L\}\right),\\\operatorname{rho}\left(L\right) = \frac{\operatorname{M}\left(L\right)}{M_{0}}, m_{*} = \operatorname{sInf}\left(\{\operatorname{m}\left(S\right) \mid S \in \operatorname{Finset}\left(Gamma\right)\}\right),\\0 < M_{0} \land \operatorname{Monotone}\left(\operatorname{mass}\left(nu\right)\right) \Rightarrow\\\operatorname{Antitone}\left(M\right) \land\\(\forall L: \mathbb{R}_{\geq0}, 0 \leq \operatorname{M}\left(L\right) \leq M_{0}) \land\\\operatorname{sInf}\left(\{\operatorname{M}\left(L\right) \mid L \in \mathbb{R}_{\geq0}\}\right) = m_{*} \land\\\operatorname{Tendsto}\left(M, atTop, \operatorname{nhds}\left(m_{*}\right)\right) \land\\\operatorname{sInf}\left(\{\operatorname{rho}\left(L\right) \mid L \in \mathbb{R}_{\geq0}\}\right) = \frac{m_{*}}{M_{0}} \land\\\operatorname{Tendsto}\left(rho, atTop, \operatorname{nhds}\left(\frac{m_{*}}{M_{0}}\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion.budget_envelope_infimum_and_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A candidate is a Finset of the active definition subtype Gamma. Its cost uses the canonical finiteSelectionCost, and its residual mass uses the canonical finiteSelectionSupplement, concept join, and target-defect relation.

Every finite candidate is feasible at some nonnegative-real budget, while every budget layer contains only finite candidates. These two directions identify the infimum across budget layers with the infimum across all finite candidates.

Antitonicity and the common greatest lower bound give the filter-level limit atTop. Dividing by the positive baseline mass preserves the infimum and limit for the normalized escape spectrum.

The theorem asserts approximation by cofinal budget layers only. It does not assert that any finite candidate attains either infimum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion.budget_envelope_infimum_and_limit`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](../DefinitionEscape/FiniteCoverCounting.md)
