# Two-Time Knowledge and Forgetting

## Abstract

The finite forgetting certificate instantiates semantic loss of observer-fiber constancy.

**Theorem 1.1 (The finite certificate instantiates two-time forgetting).**

$$\operatorname{Transition}(s_{0}, s_{1}) \land\\\operatorname{Forgot}(unit, \mathrm{false}, \mathrm{true}) \land\\\operatorname{ForgottenLogged}(s_{1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/TwoTimeKnowledge.finite_certificate_instantiates_forgot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s0 be the imported initial Remember certificate and s1 the imported certificate after its Forget action. The frozen transition theorem executes that action from s0 to s1. The semantic interpretation maps Boolean false and true to those two certificate states, reads the world bit at s0, and uses a constant readout at s1.

For the unit event with its Boolean world value and universal complete ledger, the same concrete state pair therefore satisfies Forgot. The target certificate also computes to ForgottenLogged. This is a derived model-satisfies-semantics bridge; it does not define Forgot as a cognitive state label or as an audit bit.

**Theorem 1.2 (Forgot normalizes to a later-fiber counterexample).**

$$\forall e, t_{0}, t_{1},\ \operatorname{Forgot}(e, t_{0}, t_{1}) \iff (t_{0}<t_{1} \land \operatorname{Persists}(e, t_{0}, t_{1}) \land\\(\forall x, y,\ r_{t_{0}}(x)=r_{t_{0}}(y) \Rightarrow v_{e}(x)=v_{e}(y)) \land\\\exists x, y,\ r_{t_{1}}(x)=r_{t_{1}}(y) \land v_{e}(x)\neq v_{e}(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/TwoTimeKnowledge.forgot_iff_later_fiber_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forgot is defined by strict time order, persistence in the complete ledger, early knowledge, and later nonknowledge. Knows is itself defined as Function.FactorsThrough. This secondary corollary unfolds those two definitions and classically converts later failure of fiber constancy into two worlds on one readout fiber with different event values.

Pinned Mathlib supplies Function.FactorsThrough for fiber constancy and Function.factorsThrough_iff for its factor-map form. Searches also checked Function.FactorsThrough.extend_comp, Function.not_injective_iff, Classical.not_forall, and Set.Icc. No library declaration performs this domain-specific normalization.

The equivalence exposes the quantifiers already present in the definitions; it is not an independent characterization of forgetting. In particular, it does not identify forgetting with a state label, ledger deletion, physical erasure, or a recall transition.

**Theorem 1.3 (Later knowledge pulls back along readout factorization).**

$$\forall e, t_{0}, t_{1},\ (\operatorname{FactorsThrough}(r_{t_{1}}, r_{t_{0}}) \land \operatorname{Knows}(e, t_{1})) \Rightarrow \operatorname{Knows}(e, t_{0}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/TwoTimeKnowledge.knows_of_later_readout_factors_through_earlier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the later readout is constant on every earlier readout fiber, so the later readout factors through the earlier one. Worlds equal under the earlier readout are then equal under the later readout. If the event value is constant on every later fiber, it is consequently constant on every earlier fiber. The implication runs from later knowledge to earlier knowledge under this stated direction of factorization.

## References

- Truth anchor: `D5/S3/ObserverMemory/TwoTimeKnowledge.finite_certificate_instantiates_forgot`
- Truth anchor: `D5/S3/ObserverMemory/TwoTimeKnowledge.forgot_iff_later_fiber_counterexample`
- Truth anchor: `D5/S3/ObserverMemory/TwoTimeKnowledge.knows_of_later_readout_factors_through_earlier`
- Dependency: [D5/S3/ObserverMemory/FiniteForgettingCertificate](FiniteForgettingCertificate.md)
