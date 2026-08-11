# Quartic Divisibility by Thirty-Six

## Abstract

The quartic 27k^4+108k^3+171k^2+126k+36 is divisible by 36 for every integer k.

**Theorem 1.1 (Thirty-six divides the quartic for every integer).**

$$36 \mid 27k^{4}+108k^{3}+171k^{2}+126k+36$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/QuarticThirtySix.thirtySix_dvd_m` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quartic m(k) = 27k^4 + 108k^3 + 171k^2 + 126k + 36 is divisible by 36 for every integer k. Reducing modulo 36, the polynomial evaluates to zero on every residue class, so 36 divides m(k) identically. The residue check is a finite kernel decision over the 36 elements of ZMod 36, lifted to the integers by the standard cast-vanishes-iff-divides equivalence.

This is the self-contained arithmetic corroboration of the 36-theorem; it makes no claim about the geodesic-word or fixed-point-form context in which the quartic arises.

## References

- Truth anchor: `D5/S3/Arith/Congruence/QuarticThirtySix.thirtySix_dvd_m`
