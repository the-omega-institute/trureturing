# Name-Set Distance Sandwich

## Abstract

Distances to three nested nonempty name sets form a reversed sandwich.

**Theorem 1.1 (Nested name sets give a reversed distance sandwich).**

$$\forall \alpha, [\operatorname{PseudoMetricSpace}(\alpha)],\ \forall x\in\alpha, \forall P,T,K\subseteq\alpha,\ P \subseteq T \land T \subseteq K \land \operatorname{Nonempty}(P) \Rightarrow \operatorname{infDist}(x,P) \ge \operatorname{infDist}(x,T) \land \operatorname{infDist}(x,T) \ge \operatorname{infDist}(x,K).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/NameSetDistanceSandwich.nested_name_set_infDist_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the two additive budget shifts are absorbed into the supplied level sets P, T, and K, the source's metric conclusion follows from the two inclusions P subset T and T subset K. The Lean proof invokes Mathlib's infDist_le_infDist_of_subset once for each inclusion.

The nonemptiness premise is necessary for real-valued infDist: Mathlib defines the distance to the empty set as zero. Nonemptiness of T follows from that of P and the first inclusion.

This deposit partially closes only the nested-distance consequence in clause (a) of source theorem 6.5. It does not construct the prefix-to-test or test-to-program coding embeddings, prove their additive overhead bounds, or close either separation family in clause (b); all of those subitems remain unresolved.

## References

- Truth anchor: `D5/S0/Asymptotics/NameSetDistanceSandwich.nested_name_set_infDist_sandwich`
