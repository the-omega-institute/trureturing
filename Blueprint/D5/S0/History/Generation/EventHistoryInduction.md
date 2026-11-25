# Event History Induction

## Abstract

Properties of finite event histories follow from the empty and one-event generation cases.

**Theorem 1.1 (Event histories admit generation induction).**

$$\forall P: \operatorname{EventHistory}\to \operatorname{Prop}, (\operatorname{P}\left(empty\right) \land (\forall h: \operatorname{EventHistory}, \forall u: \operatorname{Event}, \operatorname{P}\left(h\right) \Rightarrow \operatorname{P}\left(\operatorname{pushBack}\left(h, u\right)\right))) \Rightarrow \forall h: \operatorname{EventHistory}, \operatorname{P}\left(h\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Generation/EventHistoryInduction.event_history_induction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty event history satisfies P. A nonempty history consists of a shorter history and one last event. The induction hypothesis gives P for the shorter history, and the append hypothesis gives P for the whole history.

## References

- Truth anchor: `D5/S0/History/Generation/EventHistoryInduction.event_history_induction`
