# Global logarithmic lower envelope for actual occupation

## Abstract

One positive logarithmic scale bounds both actual occupation masses at every integer.

**Theorem 1.1 (A common scale for raw and normalized mass).**

$$\exists t\in \mathbb{R},\quad0<t \land (\forall z\in \mathbb{Z},\quad t\cdot \operatorname{discrepancyProfile}\left(z\right)\le \operatorname{rawOccupation}\left(z\right)\quad\land\quad\frac{2}{a}\cdot t\cdot \operatorname{discrepancyProfile}\left(z\right)\le \operatorname{occupation}\left(z\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedLogEnvelope.actual_raw_occupation_log_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The discrepancy profile is the reciprocal of the product of the square root and logarithm of two plus the absolute position. It is strictly positive and is largest at the origin, which supplies one upper bound on the whole integer lattice.

Both the compensated gain and the quadratic cost use the same two neighbors at each positive jump length. The fixed point comparison balances the linear gain with the quadratic cost on the tails and uses the positive forcing in the finite core. Multiplication by the positive normalizing factor carries the raw bound to normalized occupation without changing the chosen scale.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedLogEnvelope.actual_raw_occupation_log_envelope`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss](OccupiedNonlinearLoss.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedResidualGain](OccupiedResidualGain.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedTailComparison](OccupiedTailComparison.md)
