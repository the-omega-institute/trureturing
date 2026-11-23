# Dyadic dilation of integral formal series

## Abstract

Dyadic power congruences hold at every degree.

In characteristic two, squaring sends every monomial to its degree doubling. Lifting the resulting difference of powers in the integer series ring raises the power of two that divides the difference. Repeating gives larger dilations at a fixed modulus.

**Definition 1.1 (reduce).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Reduce every integer coefficient modulo the given natural modulus.

**Theorem 1.2 (coeff_reduce_eq_zero).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.coeff_reduce_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DyadicDilation.coeff_reduce_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A reduced coefficient vanishes exactly when the modulus divides the original coefficient.

**Theorem 1.3 (map_mod_eq_iff).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.map_mod_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DyadicDilation.map_mod_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Two reductions coincide exactly when the constant series of the modulus divides the difference.

**Theorem 1.4 (dyadic_lift).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.dyadic_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DyadicDilation.dyadic_lift` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The difference between the 2^(j+1)-th power and the 2^j-th power after degree doubling is divisible by the constant 2^(j+1).

**Theorem 1.5 (reduce_lift).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Iterated degree doubling gives a dilation by 2^(r+1) modulo 2^(j+1).

**Theorem 1.6 (reduce_lift_mul).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The iterated congruence remains valid after raising both sides to any natural power.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.coeff_reduce_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.dyadic_lift`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.map_mod_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DyadicDilation.reduce_lift_mul`
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../../../S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.md)
