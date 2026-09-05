# Four-Role Independence

## Abstract

Four explicit Boolean models separate cut, flow, admissibility, and anchor.

**Theorem 1.1 (Each observer role varies independently).**

$$\begin{gathered}(\exists q1 \in Bool \to Bool, q2 \in Bool \to Bool, F \in Bool \to Bool, A \in Bool \to Prop, a \in Bool,\; q1 \ne q2 \land A\left(a\right)) \land\\{}(\exists q \in Bool \to Bool, F1 \in Bool \to Bool, F2 \in Bool \to Bool, A \in Bool \to Prop, a \in Bool,\; F1 \ne F2 \land A\left(a\right)) \land\\{}(\exists q \in Bool \to Bool, F \in Bool \to Bool, A1 \in Bool \to Prop, A2 \in Bool \to Prop, a \in Bool,\; A1 \ne A2 \land \left(A1\left(a\right) \land A2\left(a\right)\right)) \land\\{}(\exists q \in Bool \to Bool, F \in Bool \to Bool, A \in Bool \to Prop, a1 \in Bool, a2 \in Bool,\; a1 \ne a2 \land \left(A\left(a1\right) \land A\left(a2\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/FourRoleIndependence.four_role_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each row shares three coordinates and changes only the fourth. Identity versus a constant cut witnesses CUT independence, and identity versus Boolean negation witnesses FLOW independence.

Universal admissibility versus equality to false separates ADMIT while both predicates accept the false anchor. Universal admissibility then permits false and true as distinct accepted anchors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/FourRoleIndependence.four_role_independence`
