# Erdős #375: three consecutive composites

## Abstract

Three consecutive composite integers admit pairwise distinct prime divisors.

**Theorem 1.1 (Distinct prime divisors for three consecutive composites).**

$$\forall n \in \mathbb{N}, \left(\left(\left(1 \le n \land \left(\neg Prime\left(n + 1\right)\right)\right) \land \left(\neg Prime\left(n + 2\right)\right)\right) \land \left(\neg Prime\left(n + 3\right)\right)\right) \Rightarrow \exists p1, p2, p3 \in \mathbb{N}, \left(\left(\left(\left(\left(\left(\left(Prime\left(p1\right) \land Prime\left(p2\right)\right) \land Prime\left(p3\right)\right) \land p1 \mid n + 1\right) \land p2 \mid n + 2\right) \land p3 \mid n + 3\right) \land p1 \ne p2\right) \land p1 \ne p3\right) \land p2 \ne p3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/Erdos375ThreeComposites.exists_distinct_prime_divisors_of_three_composites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one, assume n+1, n+2 and n+3 are all composite. The theorem supplies prime divisors p1, p2 and p3 of the corresponding terms and proves all three pairwise inequalities.

The endpoint argument uses the four-divisibility alternative: both endpoints cannot be multiples of four because their difference is two, so one endpoint has an odd prime divisor. Coprimality of successive terms separates the middle divisor. This is only the three-term slice of the open Grimm conjecture; no claim for intervals of length at least four is made.

## References

- Truth anchor: `D5/S3/Arith/Congruence/Erdos375ThreeComposites.exists_distinct_prime_divisors_of_three_composites`
