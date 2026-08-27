# Finite Policy Section Count

## Abstract

Finite-state deterministic policy sections are counted by the product of their legal-action fiber sizes.

**Theorem 1.1 (Policy sections have the product of the legal-fiber cardinalities).**

$$\begin{gathered}\forall Q, A: \operatorname{Type},\\{}[\operatorname{Fintype}(Q)], Legal: Q \to \left(A \to \operatorname{Prop}\right),\\{}\operatorname{NatCard}(\left\{s: Q \to \left\{z: Q \times A \mid \operatorname{Legal}(\operatorname{fst}(z), \operatorname{snd}(z))\right\} \mid \forall q: Q, \operatorname{fst}(s(q)) = q\right\}) = \prod_{q \in Q} \operatorname{NatCard}(\left\{a: A \mid \operatorname{Legal}(q, a)\right\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount.finite_policy_sections_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The legality predicate constructs the total action space from state-action pairs. The counted policies are functions into that total space whose first coordinate is the state supplied to the function, so the public statement counts genuine sections of the projection.

A section determines one legal action in every state fiber, and a dependent family of legal actions reconstructs the section with its projection equation. These maps are inverse before finite cardinality is taken.

The equality does not require nonemptiness of the fibers: when a fiber is empty, both the section type and the dependent product are empty. Thus the deposited statement strengthens the finite-nonempty source case.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount.finite_policy_sections_card`
