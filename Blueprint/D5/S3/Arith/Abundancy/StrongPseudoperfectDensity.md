# McCormack and Zelinsky's Question 43

## Abstract

Strongly pseudoperfect positive integers have natural density zero.

**Definition 1.1 (Complementary divisor sums).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.StronglyPseudoperfect`

*Formalization.* `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.StronglyPseudoperfect` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

A positive integer n is strongly pseudoperfect when a subset S of its positive divisors is closed under d maps to n/d and the sum of its elements is 2n. No condition requires 1 or n to belong to S. Positivity excludes zero, in agreement with Wang and Zelinsky's definition.

**Definition 1.2 (Counting positive integers).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.spCount`

*Formalization.* `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.spCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

The count includes exactly the strongly pseudoperfect integers in the closed interval from 1 to X.

**Theorem 1.3 (Zero natural density).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/mccormack-zelinsky-2023-question-43` (refuted) by `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mccormack-zelinsky-2023-question-43","declaration_gid":"D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

Question 43 asks: Does SP have positive natural density? The quotient spCount(X)/X tends to zero as the natural number X tends to infinity. Thus the answer is no. Wang and Zelinsky repeat the same question as Question 22.

Let q be prime with q not dividing m. For a complementary divisor subset S of mq with sum 2mq, put T equal to its intersection with the divisors of m. The disjoint decomposition into T and its complements gives A + qB = 2mq, where A is the sum of d over T and B is the sum of m/d over T. Since A is positive, B is less than 2m and q = A/(2m-B). Consequently at most 2^tau(m) primes q can occur for a fixed m.

Write Omega for the number of prime factors with multiplicity. The inequalities tau(m) <= 2^Omega(m) and 2^4 < (3/2)^7 give tau(m)^(4/7) <= (3/2)^Omega(m). A finite Euler product and a weak Mertens upper bound give a constant D for which, for X at least three, the sum up to X of (3/2)^Omega(m)/m is at most D*(log X)^(3/2). The factor at the prime two has geometric ratio 3/4.

For sufficiently large X, put L = log X, a = 15/16, b = 31/32, z = exp(L^b), and Y equal to the integer part of z. The Rankin bound with exponent 1-1/log z counts the integers whose prime factors are at most Y. A finite inverse-square sum bounds integers divisible by q^2 for q greater than Y. Every other integer has a representation mq with q prime, q greater than Y, q not dividing m, and m at most X/(Y+1).

Cofactors with tau(m) at most L^a contribute at most (X/z)*2^(L^a). The others have reciprocal mass at most L^(-15/28) times the weighted Omega sum. Chebyshev's bound applies at X/m, whose logarithm is at least L^b. After division by X, their contribution is at most a constant times L^(-1/224). The remaining terms are bounded by constants times (1+L^b)*exp(-L^(1/32)), exp(-L^b), and exp((log 2)*L^a-L^b). All four terms tend to zero.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.StronglyPseudoperfect`
- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result`
- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.spCount`
