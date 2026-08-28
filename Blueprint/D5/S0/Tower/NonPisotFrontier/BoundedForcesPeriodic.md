# Bounded Forces Periodic

## Abstract

A bounded orbit under an expanding multiplier is zero, so periodic digits make the remainders repeat with the same period.

Two sequences driven by the same digits from some index onward differ by something that is multiplied by the base at every step. If the sequences are bounded, that difference cannot grow, and under an expanding multiplier the only bounded orbit is the zero one. So the difference vanishes and the sequence repeats.

The multiplier is arbitrary, so the same statement applies on both sides of the conjugation: at the base, where remainders are confined to the unit interval, and at the conjugate, where the bound has to come from somewhere else.

**Theorem 1.1 (Periodic digits force a periodic orbit).**

$$1 < \left|c\right| \Rightarrow \left(\forall n \in N,\; N \le n \Rightarrow \operatorname{r}\left(n + p\right) = \operatorname{r}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic.periodic_digits_force_periodic_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boundedness is a hypothesis here, not a conclusion. Supplying it for the greedy remainders is immediate; supplying it on the conjugate side is exactly what the escape estimate denies, and that opposition is the point of the chain this module belongs to. Nothing about any particular base appears here, by the generality ordering; the instantiation lives one tier down.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic.periodic_digits_force_periodic_orbit`
