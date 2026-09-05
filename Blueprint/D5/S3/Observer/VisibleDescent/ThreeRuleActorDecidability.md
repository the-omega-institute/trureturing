# Three Rule Forms and Actor Readout

## Abstract

All three actor-relative rule forms descend on the full action-input carrier.

**Theorem 1.1 (Compatibility, separation, and recipient descent).**

$$\begin{aligned}\forall X, U, I: \operatorname{Type},\\B: I \to \operatorname{Type},\\readout: (agent: I) \to X \to B(agent),\\transition: X \to \left(U \to \left(I \to \left(I \to X\right)\right)\right),\\actor: I,\\\operatorname{let} actorInputReadout: X \times U \times I \to B(actor) \times U \times I := (input: X \times U \times I \mapsto \operatorname{triple}(readout(actor)(\operatorname{state}(input)), \operatorname{action}(input), \operatorname{recipient}(input))),\\mirroredTransition: X \times U \times I \to X := (input: X \times U \times I \mapsto transition(\operatorname{state}(input), \operatorname{action}(input), \operatorname{recipient}(input), actor)),\\actualTransition: X \times U \times I \to X := (input: X \times U \times I \mapsto transition(\operatorname{state}(input), \operatorname{action}(input), actor, \operatorname{recipient}(input))),\\compatible: \operatorname{Prop} := \operatorname{FactorsThrough}(\operatorname{compose}(readout(actor), mirroredTransition), actorInputReadout) \operatorname{in}\\(\forall wish \in X \to \operatorname{Prop},\; \operatorname{FactorsThrough}(wish, readout(actor)) \Rightarrow compatible \Rightarrow \operatorname{FactorsThrough}((input: X \times U \times I \mapsto \neg wish(mirroredTransition(input))), actorInputReadout)) \land\\(\neg compatible \Rightarrow \exists wish \in X \to \operatorname{Prop},\; \operatorname{FactorsThrough}(wish, readout(actor)) \land \neg \operatorname{FactorsThrough}((input: X \times U \times I \mapsto \neg wish(mirroredTransition(input))), actorInputReadout)) \land\\(compatible \Leftrightarrow (\forall wish \in X \to \operatorname{Prop},\; \operatorname{FactorsThrough}(wish, readout(actor)) \Rightarrow \operatorname{FactorsThrough}((input: X \times U \times I \mapsto \neg wish(mirroredTransition(input))), actorInputReadout))) \land\\(\forall wish \in X \to \operatorname{Prop}, capable \in X \times U \times I \to \operatorname{Prop},\; \operatorname{FactorsThrough}(wish, readout(actor)) \Rightarrow \operatorname{FactorsThrough}(capable, actorInputReadout) \Rightarrow compatible \Rightarrow \operatorname{FactorsThrough}((input: X \times U \times I \mapsto wish(mirroredTransition(input)) \land capable(input)), actorInputReadout)) \land\\(\forall otherWish \in \forall recipient: I, X \to \operatorname{Prop},\; \operatorname{FactorsThrough}((input: X \times U \times I \mapsto \neg otherWish(\operatorname{recipient}(input), actualTransition(input))), actorInputReadout) \Leftrightarrow \exists descended \in B(actor) \times U \times I \to \operatorname{Prop},\; (input: X \times U \times I \mapsto otherWish(\operatorname{recipient}(input), actualTransition(input))) = \operatorname{compose}(descended, actorInputReadout)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability.three_rule_actor_decidability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actor-visible input retains the action and recipient coordinates while replacing the state by the actor's readout.

The frozen observer-action criterion supplies compatibility, universal preservation, and the positive desire-and-ability rule on this carrier. Its contrapositive yields the separating desire.

For the actual transition evaluated by the recipient's desire, Mathlib's factorization criterion exposes the descended predicate explicitly.

Repository search found the frozen full-carrier owner but no declaration that publicly states both the separating witness and descended predicate. Pinned Mathlib supplies the latter factorization step.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability.three_rule_actor_decidability`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability](../../ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability.md)
