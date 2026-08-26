# Strict Monotone Objective Argmax Alignment

## Abstract

Strictly increasing objective factorization preserves every feasible argmax set.

**Theorem 1.1 (Strictly increasing factorization preserves feasible maximizers).**

$$\forall Z: Type, S: \operatorname{Set}\left(Z\right), O_{A}, O_{P}: Z \to \mathbb{R}, g: \mathbb{R} \to \mathbb{R},\\{}\operatorname{StrictMono}\left(g\right) \land O_{P} = g \circ O_{A}\\{}\Rightarrow \{z \mid z \in S \land \forall w \in S, O_{A}(w) \leq O_{A}(z)\} = \{z \mid z \in S \land \forall w \in S, O_{P}(w) \leq O_{P}(z)\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/StrictMonotoneObjectiveArgmaxAlignment.strict_monotone_factorization_preserves_argmax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The agent and principal objectives are real-valued functions on the same state-action carrier and are optimized over the same feasible set.

A strictly increasing transform preserves and reflects every weak order comparison, so each feasible candidate is maximal for one objective exactly when it is maximal for the other.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/StrictMonotoneObjectiveArgmaxAlignment.strict_monotone_factorization_preserves_argmax`
