# A five-probe noncube sieve

## Abstract

Five small finite readouts restrict a compatible local cubic character at every positive native Lucas level.

**Theorem 1.1 (The alternating marked digit and the common-character sieve).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicOneTameSieve.marked_one_tame_sieve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicOneTameSieve.marked_one_tame_sieve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level n+1 the native parameter is the Lucas value at 3 to the power n+1. The operational probe evaluates a Cardano radicand in split or inert residue arithmetic, assigns its oriented cubic label, and adds the explicit signed correction modulo three. The proof uses the protected Lucas recurrence and checks closure and the resulting digits on five finite orbits, for probes 7, 11, 17, 23 and 47. In particular, the corrected digit at 17 is one for even n and two for odd n, and the digit at 23 is always two.

For a candidate prime congruent to one modulo 18, assume a single multiplicative cubic character on its units matches all five operational digits after multiplication by a common nonzero orientation in the field of three elements. Then 17, 23, 161, 253 and 1081 are noncubes modulo the candidate. The last three tests multiply by 23; the character is additive in the labels, and a cube of a unit has zero label.

The compatibility premise is not a proved identification with global reciprocity. Neither the existence of a sole tame conductor nor a Wall–Sun–Sun settlement, an analytic search bound, or a priority claim about classical cubic characters is asserted.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicOneTameSieve.marked_one_tame_sieve`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
