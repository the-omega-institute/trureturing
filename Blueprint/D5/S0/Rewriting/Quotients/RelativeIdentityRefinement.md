# Relative Identity Refinement

## Abstract

A finer readout quotient maps uniquely and surjectively onto every factored coarse quotient.

**Theorem 1.1 (Refinement induces the canonical quotient surjection).**

$$\forall X, Fine, Coarse,\ fine: X \to Fine, coarse: X \to Coarse,\ forget: Fine \to Coarse,\ coarse = forget \circ fine \Rightarrow\ \ker fine \subseteq \ker coarse \land\ \exists! descend: \operatorname{Quotient}(\ker fine) \to \operatorname{Quotient}(\ker coarse),\ \operatorname{Surjective}\left(descend\right) \land \forall x, descend([x]_{fine}) = [x]_{coarse}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/RelativeIdentityRefinement.relative_identity_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a coarse readout factor through a fine readout. Equality under the fine readout then implies equality under the coarse readout, so the fine kernel relation is contained in the coarse kernel relation.

Mathlib's Setoid.map_of_le constructs the induced quotient map from that relation inclusion. Every coarse class has the same underlying representative in the fine quotient, which proves surjectivity. Setoid.lift_unique proves that agreement on all representatives determines this map uniquely.

This closes exactly qdo-v1 theorem/30.3, atom qdo-residual-9cbd5454e4464eb527f9e996993dc72fdc5305d0ce8a4ad1fadeaaa429cec9be. No claim about canonical representatives or unrelated observer completion properties is included.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/RelativeIdentityRefinement.relative_identity_refinement`
