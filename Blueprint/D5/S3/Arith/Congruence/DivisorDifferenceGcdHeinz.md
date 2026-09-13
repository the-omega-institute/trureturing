# Wiseman's Divisor-Difference GCD Identity

## Abstract

For every n at least two, the divisor-minus-one gcd agrees with the gcd of successive divisor gaps and with the prime-index gcd of their Heinz number.

For every n at least two, the positive divisors are read in increasing order. Natural subtraction forms each successive gap, and prime indices are one-based, so prime(1)=2 is encoded by Nat.nth Nat.Prime 0.

**Definition 1.1 (The divisor-minus-one gcd).**

$$\forall n \in N,\; a\left(n\right) = gcd\left(\left\{d - 1 \mid d \in divisors\left(n\right)\right\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.a` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two, a(n) is the gcd of d-1 over all positive divisors d of n.

**Definition 1.2 (Successive divisor differences).**

$$\forall n \in N,\; consecutiveDivisorDifferences\left(n\right) = zipWith\left((y - x), sort\left(divisors\left(n\right)\right), tail\left(sort\left(divisors\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.consecutiveDivisorDifferences` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two, this list applies the binary map (x,y) to y-x to the increasing divisor list and its tail, retaining the multiplicity of equal gaps.

**Definition 1.3 (The gcd of successive divisor differences).**

$$\forall n \in N,\; consecutiveDifferenceGcd\left(n\right) = gcd\left(toFinset\left(consecutiveDivisorDifferences\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.consecutiveDifferenceGcd` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two, this is the gcd of the finite set underlying the list of successive divisor gaps; repeated gaps do not change the gcd.

**Definition 1.4 (The Heinz number of the divisor gaps).**

$$\forall n \in N,\; heinzDifferences\left(n\right) = \prod_{d \in consecutiveDivisorDifferences\left(n\right)} prime\left(d\right)$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.heinzDifferences` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two, this is the product of prime(delta) over the full list of successive gaps delta. The source uses one-based prime indices, while the Lean definition encodes prime(delta) as Nat.nth Nat.Prime (delta-1).

**Definition 1.5 (The gcd of prime indices).**

$$\forall m \in N,\; primeIndexGcd\left(m\right) = gcd\left(\left\{primeIndex\left(p\right) \mid p \in primeFactors\left(m\right)\right\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.primeIndexGcd` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two and m=heinzDifferences(n), this is the gcd of the one-based indices of all prime factors of m.

**Theorem 1.6 (Wiseman's three-term identity).**

$$\forall n \in N,\; 2 \le n \Rightarrow (a\left(n\right) = primeIndexGcd\left(heinzDifferences\left(n\right)\right) \land a\left(n\right) = consecutiveDifferenceGcd\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.wiseman_a258409` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a258409-divisor-difference-gcd-heinz` (proved) by `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.wiseman_a258409`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a258409-divisor-difference-gcd-heinz","declaration_gid":"D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.wiseman_a258409","resolution_kind":"proved"} -->

*Citation.* Gus Wiseman (2019). *OEIS A258409, Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n*. URL: <https://oeis.org/A258409>.

*Commentary.*

For every n at least two, a(n) equals both the prime-index gcd obtained by decoding the Heinz number of the gaps and the gcd of the gaps themselves. The first equality follows because the prime factors of the product are exactly the primes indexed by the gaps. For the second equality, a common divisor of every d-1 divides every successive difference, while a common divisor of the gaps divides each d-1 by telescoping from the first divisor 1.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.a`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.consecutiveDifferenceGcd`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.consecutiveDivisorDifferences`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.heinzDifferences`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.primeIndexGcd`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.wiseman_a258409`
