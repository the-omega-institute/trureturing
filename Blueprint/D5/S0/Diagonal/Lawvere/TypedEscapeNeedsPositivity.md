# Typed Escape Needs Positivity

## Abstract

Lawvere escape alone does not place the escaped diagonal in the effect interval.

Diagonal non-capture and effecthood are different requirements. Ordinary complement preserves the effect interval in an ordered additive group, but a fixed-point-free twist on a larger codomain can escape while leaving that interval.

**Lemma 1.1 (Ordinary complement preserves effects).**

$$\forall R \in \mathit{Type},\; \left(\operatorname{AddCommGroup}\left(R\right) \land \left(\operatorname{PartialOrder}\left(R\right) \land \left(\operatorname{IsOrderedAddMonoid}\left(R\right) \land \operatorname{One}\left(R\right)\right)\right)\right) \Rightarrow \left(\forall E \in R,\; \operatorname{IsEffect}\left(E\right) \Rightarrow \operatorname{IsEffect}\left(1 - E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.complement_isEffect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E lie between zero and the distinguished order unit in an additive commutative group with a compatible partial order. The upper bound E <= 1 gives 0 <= 1 - E, while the lower bound 0 <= E gives 1 - E <= 1. Thus complement carries every effect back into the same order interval.

**Theorem 1.2 (Lawvere escape does not imply the effect audit).**

$$\forall c \in \mathbb{Z} \to \mathbb{Z},\; \left(\forall E \in \mathbb{Z},\; c\left(E\right) = 1 - E\right) \Rightarrow \left(\exists listing \in \mathit{Unit} \to \left(\mathit{Unit} \to \mathbb{Z}\right),\; \left(\forall E \in \mathbb{Z},\; c\left(E\right) \ne E\right) \land \left(\operatorname{IsEscaped}\left(c, \mathit{listing}\right) \land \left(\neg \operatorname{PassesEffectAudit}\left(c, \mathit{listing}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.typed_escape_does_not_imply_effect_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the integers, the complement c(E) = 1 - E has no fixed point: a fixed point would make the odd integer one equal to twice an integer. Take the one-address listing whose sole entry is 2. Its twisted diagonal is -1, so the fixed-point-free Lawvere argument places that diagonal outside the listing's range.

The same value -1 is below zero and therefore is not an effect. The listing escapes, but it fails the audit requiring every diagonal value to lie between zero and one. Positivity is consequently an additional typed condition, not a consequence of escape alone.

## References

- Truth anchor: `D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.complement_isEffect`
- Truth anchor: `D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.typed_escape_does_not_imply_effect_audit`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](QualitativeEscape.md)
