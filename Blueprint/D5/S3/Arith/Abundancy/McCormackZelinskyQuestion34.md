# McCormack and Zelinsky's Question 34

## Abstract

Odd pseudoperfect divisor sets containing one satisfy A < C.

**Definition 1.1 (The proposed odd primitive example).**

Lean statement: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.claim`

*Formalization.* `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.claim` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

Question 34 asks whether there is a natural number n which is odd and primitive non-deficient, together with a finite subset S of its positive divisors such that 1 belongs to S, the sum of S is 2*n, and weightC(S,n) < weightA(S,n). Primitive non-deficiency means that n is non-deficient and every positive proper divisor of n is deficient. The two weights are exactly equations (12) and (14), using real logarithms and exact natural division inside the complementary totient. The set may include n and is not required to be closed under complementary divisors.

**Theorem 1.2 (Strict reverse inequality for every odd divisor set).**

Lean statement: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.odd_weight_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.odd_weight_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

For every odd natural number n and every finite subset S of n.divisors containing 1 and summing to 2*n, weightA(S,n) < weightC(S,n). No primitivity or separate non-deficiency hypothesis is needed.

Put T={n/d : d in S}. Exact divisor complementation gives sum over e in T of 1/e = 2, and the reciprocal mass on e>1 is at least one. An odd e>1 with phi(e)<8 belongs to {3,5,7,9}. Using log(8) as a baseline on the remaining terms and allowing all four exceptional indices gives

sum over e in T of log(phi(e))/e >= log(2)/3 + log(4)/5 + (1/7+1/9)*log(6) + (67/315)*log(8) = (512*log(2)+80*log(3))/315 > 2*log(2). The strict final inequality follows from 9>8, hence 2*log(3)>3*log(2).

Totient supermultiplicativity bounds A above by log(phi(n)) minus half that complementary logarithmic sum. The element 1 contributes phi(n)/2 to the sum defining C, and another positive term is present because the divisor sum is 2*n. Thus C>log(phi(n)/2), while A<log(phi(n)/2). All logarithm arguments used here are strictly positive.

**Theorem 1.3 (Question 34 has a negative answer).**

Lean statement: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result` (`✓ std3`). ∎

*Resolves.* `Problems/mccormack-zelinsky-2023-question-34` (refuted) by `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mccormack-zelinsky-2023-question-34","declaration_gid":"D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

The existence statement claim is false. Any proposed example satisfies the hypotheses of the strict reverse inequality, contradicting its requirement A>C. The obstruction holds for every odd divisor set of sum 2*n containing 1, including all primitive non-deficient candidates. It does not assert the same inequality after removing oddness or the requirement that 1 belong to the set.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.odd_weight_reverse`
- Truth anchor: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result`
- Dependency: [D5/S3/Arith/Abundancy/WeightedTotientEulerDensity](WeightedTotientEulerDensity.md)
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive](ZelinskyZhangDoublePrimitive.md)
