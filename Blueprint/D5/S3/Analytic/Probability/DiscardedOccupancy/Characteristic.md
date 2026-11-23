# Occupancy word laws and characteristic functions

## Abstract

The explicit finite word measure is the product of the individual throw measures.

**Theorem 1.1 (The finite word measure is a product).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), 0<n \implies 0 \leq p \implies p \leq 1 \implies \operatorname{toMeasure}\left(\operatorname{wordPMF}\left(n, p, j\right)\right) = \prod_{i: \operatorname{Fin}\left(j\right)} \operatorname{toMeasure}\left(\operatorname{throwPMF}\left(n, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A throw is discarded with probability one minus p and each ordinary bin has mass p divided by n. The mass of a word is the product of the coordinate masses. The transition calculation for the characteristic function uses this same law and conditions on the count of occupied bins after the prefix.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions](Transitions.md)
