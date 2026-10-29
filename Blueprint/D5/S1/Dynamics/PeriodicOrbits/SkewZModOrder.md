# Finite cyclic holonomy and skew periods

## Abstract

Finite cyclic holonomy converts a skew return period into a gcd quotient.

**Theorem 1.1 (The gcd formula for a finite cyclic fiber).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrder.skew_minimalPeriod_zmod`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrder.skew_minimalPeriod_zmod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an additive skew map over a base self-map f with fiber ZMod q, the return holonomy accumulated over the base minimal period is an element h of ZMod q. The lifted minimal period is the base period multiplied by the additive order of h.

When q is nonzero, Mathlib identifies that additive order with q divided by gcd(q,h.val). Thus the theorem exposes the arithmetic content of the group action: a base cycle closes in the fiber after exactly the number of repetitions required to kill its holonomy. The zero holonomy case gives multiplier one, while a nonzero residue can lengthen the orbit by a proper divisor of q.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrder.skew_minimalPeriod_zmod`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn](SkewAdditiveReturn.md)
