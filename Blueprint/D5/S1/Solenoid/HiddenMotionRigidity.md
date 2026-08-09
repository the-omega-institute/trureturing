# Hidden-Motion Rigidity

## Abstract

Every continuous path in the prime-adic hidden fiber is constant.

**Theorem 1.1 (Every continuous prime-adic hidden motion is constant).**

$$\forall gamma: I \to \prod_{p\in \mathbb{P}} \mathbb{Z}_p, \operatorname{Continuous}(gamma) \Rightarrow \forall s, t \in I, gamma(s) = gamma(t)$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/HiddenMotionRigidity.prime_adic_hidden_motion_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path domain is the closed unit interval, while the hidden codomain is the product of the rings of p-adic integers over all primes. Each p-adic factor is ultrametric and therefore totally disconnected; the product retains total disconnectedness. Mathlib's general rigidity theorem then makes any continuous map from the connected interval constant, excluding every genuine pure hidden continuous slide.

**Theorem 1.2 (The total-disconnectedness hypothesis is weight-bearing).**

$$\exists gamma: I \to \mathbb{R}, \operatorname{Continuous}(gamma) \land \exists s, t, gamma(s) \neq gamma(t)$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/HiddenMotionRigidity.real_unit_interval_has_nonconstant_continuous_motion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing the hidden codomain by the real line invalidates the rigidity conclusion: the subtype inclusion from the unit interval to the reals is continuous and sends zero and one to distinct values. This kernel-checked counterexample shows that total disconnectedness, not the path notation alone, carries the exclusion.

## References

- Truth anchor: `D5/S1/Solenoid/HiddenMotionRigidity.prime_adic_hidden_motion_rigidity`
- Truth anchor: `D5/S1/Solenoid/HiddenMotionRigidity.real_unit_interval_has_nonconstant_continuous_motion`
