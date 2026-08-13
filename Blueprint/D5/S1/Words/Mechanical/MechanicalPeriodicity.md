# Periodicity of Lower Mechanical Words

## Abstract

Classify eventual periodicity of lower mechanical words by rationality of the slope.

Fix a real slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. A rational slope gives a period from the reduced denominator. Conversely, exact repetition on a tail and the frozen discrepancy bound force the slope to equal a quotient of two natural numbers.

**Definition 1.1 (Eventual periodicity begins after a finite prefix).**

$$\exists s,p\in\mathbb{N},\ 0<p \land \forall n\in\mathbb{N},\ w_{\alpha,\rho}(s+n+p) = w_{\alpha,\rho}(s+n)$$

*Formalization.* `D5/S1/Words/Mechanical/MechanicalPeriodicity.lowerMechanicalEventuallyPeriodic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition records a start s, a positive period p, and equality of every letter after shifting the tail by p.

**Theorem 1.2 (The reduced denominator is a period for a rational slope).**

$$\forall r\in\mathbb{Q}, \forall \rho\in\mathbb{R},\ \operatorname{Periodic}(w_{r,\rho},\operatorname{den}(r))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_word_rat_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shifting an index by the reduced denominator adds the integer numerator to both floor endpoints, so their difference and Boolean readout are unchanged.

**Theorem 1.3 (Eventual periodicity is equivalent to rationality of the slope).**

$$\neg\operatorname{Irrational}(\alpha) \iff \exists s,p\in\mathbb{N},\ 0<p \land \forall n\in\mathbb{N},\ w_{\alpha,\rho}(s+n+p) = w_{\alpha,\rho}(s+n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_eventually_periodic_iff_not_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the reverse implication, periodic block counts grow exactly linearly. The discrepancy bound keeps their difference from length times alpha below one at every multiple, forcing the block count to equal p alpha.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalPeriodicity.lowerMechanicalEventuallyPeriodic`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_eventually_periodic_iff_not_irrational`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_word_rat_periodic`
- Dependency: [D5/S1/Words/Mechanical/MechanicalDensity](MechanicalDensity.md)
