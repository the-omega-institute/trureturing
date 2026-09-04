# Three Rule Forms and Actor Readout

## Abstract

Actor-visible desires are preserved exactly by readout-compatible transitions, while a recipient's desire requires descent through the actor's readout.

**Theorem 1.1 (Compatibility separates actor-local and recipient-dependent rules).**

$$\begin{aligned}\forall State, Action, Agent: \operatorname{Type},\\Observation: Agent \to \operatorname{Type},\\readout: (agent: Agent) \to State \to Observation(agent),\\transition: State \to \left(Action \to \left(Agent \to \left(Agent \to State\right)\right)\right),\\desire: Agent \to \left(State \to \operatorname{Prop}\right),\\ability: Agent \to \left(State \to \left(Action \to \left(Agent \to \operatorname{Prop}\right)\right)\right),\\action: Action, actor: Agent, recipient: Agent,\\\operatorname{let} q: State \to Observation(actor) := readout(actor),\\mirrored: State \to State := (state: State \mapsto transition(state, action, recipient, actor)),\\actual: State \to State := (state: State \mapsto transition(state, action, actor, recipient)),\\compatible: \operatorname{Prop} := \operatorname{FactorsThrough}(q \circ mirrored, q) \operatorname{in}\\(\operatorname{FactorsThrough}(desire(actor), q) \Rightarrow compatible \Rightarrow \operatorname{FactorsThrough}((state: State \mapsto \neg desire(actor, mirrored(state))), q)) \land\\(\neg compatible \Rightarrow \exists selfDesire: State \to \operatorname{Prop}, (\operatorname{FactorsThrough}(selfDesire, q) \land \neg \operatorname{FactorsThrough}((state: State \mapsto \neg selfDesire(mirrored(state))), q))) \land\\(compatible \Leftrightarrow (\forall selfDesire: State \to \operatorname{Prop}, \operatorname{FactorsThrough}(selfDesire, q) \Rightarrow \operatorname{FactorsThrough}((state: State \mapsto \neg selfDesire(mirrored(state))), q))) \land\\(\operatorname{FactorsThrough}(desire(actor), q) \Rightarrow \operatorname{FactorsThrough}((state: State \mapsto ability(actor, state, action, recipient)), q) \Rightarrow compatible \Rightarrow \operatorname{FactorsThrough}((state: State \mapsto desire(actor, mirrored(state)) \land ability(actor, state, action, recipient)), q)) \land\\(\operatorname{FactorsThrough}((state: State \mapsto \neg desire(recipient, actual(state))), q) \Leftrightarrow \exists descended: Observation(actor) \to \operatorname{Prop}, (state: State \mapsto desire(recipient, actual(state))) = descended \circ q).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability.three_rule_actor_decidability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation family may vary with the agent. The actor readout, mirrored transition, and actual transition are constructed from the displayed source primitives before any rule predicate is stated.

Compatibility preserves every desire already constant on actor-readout fibers. Conversely, two equal-readout states whose mirrored successors have different readouts define a separating desire, so compatibility is necessary for preservation of every such desire.

The positive rule additionally uses the actor's ability predicate. The structural rule uses the recipient's desire after the actual action; Mathlib's factorization criterion constructs its descended predicate.

Repository searches found an adjacent answerability criterion but no theorem with the transition converse and all three rule forms. Pinned Mathlib supplies the fiber-constancy and descent primitives.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability.three_rule_actor_decidability`
