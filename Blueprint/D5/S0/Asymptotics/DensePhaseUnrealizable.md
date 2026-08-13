# Dense Phase Is Unrealizable

## Abstract

Fixed points cannot have positive exponential density at all large listing sizes.

**Theorem 1.1 (Positive fixed-point density is eventually unrealizable).**

$$\forall Y [\operatorname{Finite}(Y)],\ \forall f: Y\to Y,\ \forall n\in \mathbb{N},\ n \ge 2 \Rightarrow \operatorname{card}(Y) = n \Rightarrow \forall c\in \mathbb{R},\ (0 < c \land c < 1) \Rightarrow \operatorname{card}(\operatorname{Fix}(f)) \le n \land \exists A_{0}\in \mathbb{N},\ \forall A\in \mathbb{N},\ A_{0} \le A \Rightarrow \operatorname{card}(\operatorname{Fix}(f)) \neq c n^{A}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/DensePhaseUnrealizable.fixed_point_dense_phase_eventually_unrealizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite output type Y with cardinality n at least two, the fixed points of f form a subtype of Y, so their cardinality is at most n. For each real c strictly between zero and one, powers n^A eventually exceed n/c, forcing c n^A above n.

Pinned Mathlib supplies Finite.card_subtype_le and tendsto_pow_atTop_atTop_of_one_lt. The proof combines the structural fixed-point bound with exponential divergence to obtain one threshold A0 that excludes the dense-phase equation for every A at least A0.

This formalizes only clause (v) of the revised occurrence of source corollary 3.6: the dense phase is unrealizable. It does not formalize the older occurrence's distinct decay identity, and it does not by itself close the multi-clause corollary atom.

## References

- Truth anchor: `D5/S0/Asymptotics/DensePhaseUnrealizable.fixed_point_dense_phase_eventually_unrealizable`
- Dependency: [D5/S0/Diagonal/EscapeCount](../Diagonal/EscapeCount.md)
