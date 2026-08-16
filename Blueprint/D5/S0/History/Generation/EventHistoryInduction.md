# Event History Induction

## Abstract

Properties of finite event histories follow from the empty and one-event generation cases.

**Theorem 1.1 (Event histories admit generation induction).**

$$\forall P: \operatorname{EventHistory}\to \operatorname{Prop}, (\operatorname{P}\left(1\right) \land (\forall h: \operatorname{EventHistory}, \forall u: \operatorname{Event}, \operatorname{P}\left(h\right) \Rightarrow \operatorname{P}\left(\operatorname{generate}\left(h, u\right)\right))) \Rightarrow \forall h: \operatorname{EventHistory}, \operatorname{P}\left(h\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Generation/EventHistoryInduction.event_history_induction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty event history satisfies P, and P is preserved when generate appends one event. Every finite EventHistory therefore satisfies P. This closes only Definition 2.3 clause 3, the generation-induction principle; it makes no claim about the neighboring clauses.

Pinned Mathlib was searched before proving. FreeMonoid.inductionOn' is the existing induction engine, while FreeMonoid.reverse_mul, FreeMonoid.reverse_of, and FreeMonoid.reverse_reverse transport its left-generator step to the repository's right-appending generate. The Lean declaration is a thin wrapper over those library results and reuses the existing EventHistory carrier.

## References

- Truth anchor: `D5/S0/History/Generation/EventHistoryInduction.event_history_induction`
- Dependency: [D5/S0/History/HistoryCarrier](../HistoryCarrier.md)
