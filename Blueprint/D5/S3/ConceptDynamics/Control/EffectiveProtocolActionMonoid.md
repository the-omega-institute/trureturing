# Effective Protocol Action Monoid

## Abstract

Protocol words modulo equality of their state actions form a faithful effective monoid.

**Theorem 1.1 (The protocol action-kernel quotient is faithful).**

$$\begin{aligned}\forall A, Q: \operatorname{Type},\\\operatorname{MonoidAction}(\operatorname{FreeMonoid}(A), Q),\\rhoAct(u, v) := \forall z: Q, u(z) = v(z),\\Mact := \operatorname{ConQuotient}(\operatorname{ker}(\operatorname{ActionEnd}(\operatorname{FreeMonoid}(A), Q))),\\alphaAct := \operatorname{MulActionOfEndHom}(\operatorname{kerLift}(\operatorname{ActionEnd}(\operatorname{FreeMonoid}(A), Q))),\\\operatorname{Equivalence}(rhoAct) \land\\(\forall p: \operatorname{FreeMonoid}(A), u: \operatorname{FreeMonoid}(A), v: \operatorname{FreeMonoid}(A), rhoAct(u, v) \Rightarrow rhoAct(p \cdot u, p \cdot v)) \land\\(\forall s: \operatorname{FreeMonoid}(A), u: \operatorname{FreeMonoid}(A), v: \operatorname{FreeMonoid}(A), rhoAct(u, v) \Rightarrow rhoAct(u \cdot s, v \cdot s)) \land\\\operatorname{FaithfulAction}(Mact, Q, alphaAct).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/EffectiveProtocolActionMonoid.effective_protocol_action_monoid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The protocol carrier is the free monoid on the action alphabet. Two words are related exactly when their given action agrees on every state; this relation is therefore constructed from the source action rather than declared independently.

The public conclusion records equivalence and compatibility with multiplication on both sides. The effective carrier is the canonical quotient by the kernel of the action representation, and its action is induced by the canonical injective kernel lift, which proves faithfulness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/EffectiveProtocolActionMonoid.effective_protocol_action_monoid`
