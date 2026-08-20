# Sandwich Phase Period

## Abstract

The sandwich winding phase falls by two each step and first returns modulo twelve after exactly six steps.

The crossing sandwich lowers the winding phase by exactly two at every step. That displacement law is the content of the exact propagation theorem, reached here through its three public consequences rather than through the private lemmas of the orbit module, whose declaration set is frozen.

What follows from a constant drop of two is a period, not merely a drift: twelve is the sixth multiple of two, so the phase returns to its residue modulo twelve after six steps and after no smaller positive number of steps. The orbit module proves only that the orbit meets phase zero once; the periodicity is stated here for the first time.

The minimality half is what carries the word period. Without it the statement would be satisfied by every multiple of six and would assert only that six steps suffice, which a constant drop makes automatic.

**Theorem 1.1 (The sandwich phase first returns modulo twelve at six).**

$$\forall n\in \mathbb{N},\ \operatorname{Psi}(sigma^{n+6}(A)) = \operatorname{Psi}(sigma^{n}(A)) - 12.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod.sandwich_phase_period_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the return law; the package also carries the single-step drop and the exclusion of every smaller positive period.

## References

- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod.sandwich_phase_period_package`
- Dependency: [D5/S3/PrimeForms/Crossing/WindingOrbitZero](../Crossing/WindingOrbitZero.md)
