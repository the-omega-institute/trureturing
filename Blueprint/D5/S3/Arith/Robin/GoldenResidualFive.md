# Strict Robin in the Bounded-Support 5040 Branch

## Abstract

A bounded 2,3,5,7 core with at most five residual primes, excluding 11, satisfies strict Robin. In the 5040 power-congruence branch this closes total support up to thirty-nine primes.

The objects here are integers n = 2^a*3^b*5*7*r with 4 <= a <= 6, 2 <= b <= 3, r coprime to 210 and 11 not dividing r. The residual r may contain arbitrary positive prime exponents. The first theorem assumes at most five distinct residual primes; the power-congruence theorem below covers at most thirty-nine total distinct prime factors.

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

**Theorem 1.3 (Thirty-nine total primes in the congruence branch).**

Lean statement: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_thirty_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_thirty_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n > 5040 such that 5040 divides n, 3^n is congruent to 2241 modulo n, and n has at most thirty-nine distinct prime factors, strict Robin holds.

The existing nine-prime result handles support at most nine. For larger support, the shape theorem gives n = 2^a*3^b*5*7*r, with 4 <= a <= 6 and 2 <= b <= 3. Coprimality gives exactly four core primes, so the residual r has between six and thirty-five distinct prime factors. The existing small-prime exclusions force all of them to be at least 47.

For a finite set of k distinct integers each at least m+1, the Euler product is at most (m+k)/m. Removing the largest integer proves the bound by telescoping induction. The proof applies this with m = 46 and combines it with the existing core bound 254/63.

If the residual support k is at most fourteen, the ratio is at most (254/63)*(60/46) = 2540/483 < 267/50. The bound n >= 5040*47^5 > 2^33 and the existing rational logarithm certificate give log(log(n)) > 3, so Robin's capacity exceeds 267/50.

If k is greater than fourteen, the proof uses the weaker bound k >= thirteen to obtain n >= 5040*47^13 > 2^84. The same logarithm-certificate interface gives log(log(2^84)) > 4: first log(2^84) > 58, then log(58) > 4. Since k <= 35, the ratio is at most (254/63)*(81/46) = 1143/161 < 178/25. The existing bound exp(gamma) > 89/50 puts Robin's capacity above 178/25.

All prime exponents in r remain arbitrary. The theorem keeps the divisibility, power-congruence and finite support hypotheses. It does not bound unrestricted support or prove the Riemann hypothesis.

**Theorem 1.4 (Explicit size lower bound for a counterexample in this branch).**

Lean statement: `D5/S3/Arith/Robin/GoldenResidualFive.counterexample_size_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenResidualFive.counterexample_size_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose n > 5040, 5040 divides n, 3^n is congruent to 2241 modulo n, and exp(gamma)*log(log(n)) <= sigma(1,n)/n. Then 5040*47^36 <= n.

The proved thirty-nine-support theorem excludes a counterexample with at most thirty-nine distinct primes. Thus n has at least forty distinct primes. The existing shape has four coprime core primes, leaving at least thirty-six distinct residual primes. Each is at least 47 by the existing small-prime exclusions. The same radical lower-bound helper used in the support theorem gives 47^36 <= r, while the core is at least 5040.

The exact threshold is 7905938326547719933989230085718562349144472262468774945155665840, approximately 7.9059383265 times 10^63. This is a lower bound for a hypothetical counterexample satisfying the stated divisibility and congruence conditions. It does not establish that such a counterexample exists or constrain counterexamples outside this branch.

## References

- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.counterexample_size_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_core_residual_le_five`
- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_nine`
- Truth anchor: `D5/S3/Arith/Robin/GoldenResidualFive.robin_of_modEq_2241_card_le_thirty_nine`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040Shape](../GoldenResource/GoldenCell5040Shape.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion](../GoldenResource/GoldenCell5040SmallPrimeExclusion.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciPrimeSupport](FibonacciPrimeSupport.md)
