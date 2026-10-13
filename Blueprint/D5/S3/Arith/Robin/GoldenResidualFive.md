# Five Residual Primes in the 5040 Branch

## Abstract

A bounded 2,3,5,7 core with at most five residual primes, excluding 11, satisfies strict Robin. In the 5040 power-congruence branch this closes total support up to nine primes.

The objects here are integers n = 2^a*3^b*5*7*r with 4 <= a <= 6, 2 <= b <= 3, r coprime to 210 and 11 not dividing r. The residual r may contain arbitrary positive prime exponents. Its number of distinct prime factors is restricted to at most five.

**Theorem 1.1 (Strict Robin for at most five residual primes).**

Lean statement: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_core_residual_le_five`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_core_residual_le_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b,r satisfying the stated hypotheses and n > 5040, sigma(1,n)/n < exp(gamma)*log(log(n)).

Coprimality gives exactly four old primes and the distinct primes of r. If r has at most four primes, the existing theorem for at most eight total primes applies. If r has five, those primes are at least 13,17,19,23,29 in increasing order. Their product is at least 2800733, so n >= 14115694320 > 2^33.

The finite core has sigma/core <= 254/63. The residual Euler product is at most (13/12)*(17/16)*(19/18)*(23/22)*(29/28) = 2800733/2128896. Thus sigma(1,n)/n <= 355693091/67060224 < 267/50. The existing rational logarithm certificates give log(log(2^33)) > 3, and exp(gamma) > 89/50, so Robin's right side is strictly above 267/50.

**Theorem 1.2 (Nine total primes in the congruence branch).**

Lean statement: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n > 5040 such that 5040 divides n, 3^n is congruent to 2241 modulo n, and n has at most nine distinct prime factors, strict Robin holds.

The existing shape theorem provides the core exponent windows and a residual coprime to 2*3*5*7*83. The small-prime exclusion theorem excludes 11 from n and hence from r. The disjoint support identity card(primeFactors(n)) = 4 + card(primeFactors(r)) reduces the nine-prime hypothesis to the five-prime residual theorem.

Robin's equivalence with the Riemann hypothesis is recalled in `D5/L/ArithSums/choie2006robincriterion`. This result concerns only the stated 5040 divisibility and power congruence branch with at most nine total primes. It does not establish that every integer satisfies the branch hypotheses or bound residual support in general. The Riemann hypothesis remains open.

## References

- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_core_residual_le_five`
- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_nine`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040Shape](../GoldenResource/GoldenCell5040Shape.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion](../GoldenResource/GoldenCell5040SmallPrimeExclusion.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciPrimeSupport](FibonacciPrimeSupport.md)
