# The zero-section probability under the original shift

## Abstract

Zero-bit marginals and shift dependence of the conditional Parry probability.

**Theorem 1.1 (The first two zero-bit probabilities).**

Lean statement: `D5/S3/TotalVariation/ParrySectionMarginals.section_zero_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParrySectionMarginals.section_zero_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the bilateral Parry law and its normalized restriction to the zero section. Write p for the reciprocal Perron root. The probability of a false bit at index zero is p, and the probability of a false bit at index one is 2 p^2. The original left shift does not preserve this probability.

The one-bit word 0 and each of the two-bit words 00 and 10 end in a reset. The conditional raw-window formula assigns them masses p, p^2 and p^2. The latter two cylinders are disjoint and exhaust the false-bit event at index one. Since p > 1/2, this event has strictly larger probability than the false-bit event at index zero whose preimage it is.

## References

- Truth anchor: `D5/S3/TotalVariation/ParrySectionMarginals.section_zero_marginals`
- Dependency: [D5/S3/TotalVariation/ParryFirstReturn](ParryFirstReturn.md)
