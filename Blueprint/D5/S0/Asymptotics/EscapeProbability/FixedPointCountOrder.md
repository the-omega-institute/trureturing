# Fixed-Point Count Order

## Abstract

Positive-address frozen escape probability strictly reverses fixed-point-count order.

**Theorem 1.1 (Escape probability strictly reverses fixed-point-count order).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f, g: Y \to Y, \forall A\in \mathbb{N}, 0 < A \Rightarrow (\operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) < \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), g\right) \iff \operatorname{card}\left(\operatorname{Fix}\left(g\right)\right) < \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/FixedPointCountOrder.escape_probability_lt_iff_fixed_point_card_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two endomorphisms f and g of the same finite nonempty output alphabet and any positive address count A, the frozen escape probability of f is smaller than that of g exactly when f has strictly more fixed points than g.

The proof applies the frozen closed form to both probabilities. The fixed-point subtype bound makes both power bases nonnegative; pinned Mathlib's pow_lt_pow_iff_left₀ removes the positive power, and div_lt_div_iff_of_pos_right compares the fixed-point counts.

Repository and all-local-ref searches found no existing comparison theorem. This order characterization is independent of the two endpoint characterizations and does not use the distance-profile or weighted-mass developments.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/FixedPointCountOrder.escape_probability_lt_iff_fixed_point_card_gt`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit](PoissonDomainLimit.md)
