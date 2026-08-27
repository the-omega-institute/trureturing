# Deterministic Policy Product and Count

## Abstract

Policy sections are canonically equivalent to dependent legal-action choices and have the corresponding product cardinality.

**Theorem 1.1 (Policy sections form the legal-fiber product and obey its count).**

$$\begin{gathered}\forall Q, A: \operatorname{Type},\\{}[\operatorname{Fintype}\left(Q\right)], Legal: Q \to \left(A \to \operatorname{Prop}\right),\\{}\operatorname{Bijective}\left(\Lambda s: \left\{s: Q \to \left\{z: Q \times A \mid \operatorname{Legal}\left(\operatorname{fst}\left(z\right), \operatorname{snd}\left(z\right)\right)\right\} \mid \forall q: Q, \operatorname{fst}\left(s\left(q\right)\right) = q\right\}, \Lambda q: Q, \operatorname{snd}\left(s\left(q\right)\right)\right) \land\\{}\operatorname{NatCard}\left(\left\{s: Q \to \left\{z: Q \times A \mid \operatorname{Legal}\left(\operatorname{fst}\left(z\right), \operatorname{snd}\left(z\right)\right)\right\} \mid \forall q: Q, \operatorname{fst}\left(s\left(q\right)\right) = q\right\}\right) = \prod_{q \in Q} \operatorname{NatCard}\left(\left\{a: A \mid \operatorname{Legal}\left(q, a\right)\right\}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/DeterministicPolicyProductCount.deterministic_policy_product_and_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Legality constructs the total action space from state-action pairs. A policy is a section of its state projection, and the displayed canonical map takes the action coordinate in every state.

The canonical map is bijective. The existing finite section-count theorem then identifies the section cardinality with the product of the legal-fiber cardinalities.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/DeterministicPolicyProductCount.deterministic_policy_product_and_count`
- Dependency: [D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount](FinitePolicySectionCount.md)
