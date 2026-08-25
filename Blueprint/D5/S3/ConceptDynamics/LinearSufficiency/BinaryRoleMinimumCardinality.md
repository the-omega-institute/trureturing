# Binary Role Minimum Cardinality

## Abstract

A sufficient subfamily of binary roles has minimum size equal to the dimension of their span.

**Theorem 1.1 (The minimum sufficient subfamily has the span dimension).**

$$\begin{gathered}\forall V, [\operatorname{AddCommGroup}(V)], [\operatorname{Module}(\operatorname{ZMod}(2), V)],\\{}E: \operatorname{Set}(V),\\{}\operatorname{IsLeast}(\{kappa: Cardinal \mid \exists B: \operatorname{Set}(V),\\{}B \subseteq E \land \operatorname{span}(\operatorname{ZMod}(2), B) = \operatorname{span}(\operatorname{ZMod}(2), E) \land \operatorname{card}(B) = kappa\}, \operatorname{rank}(\operatorname{ZMod}(2), \operatorname{span}(\operatorname{ZMod}(2), E))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality.binary_role_minimum_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a family of candidate roles in a module over the binary field, and let H be the span of E.

A selected subfamily B is sufficient exactly when it is drawn from E and spans the same submodule. A linearly independent spanning subfamily exists inside E and has cardinality equal to the dimension of H.

Every other sufficient subfamily spans H, so the dimension bound for a generating family forces its cardinality to be at least that value. Thus the displayed value is attained and least.

## References

- Truth anchor: `D5/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality.binary_role_minimum_cardinality`
