# McCormack and Zelinsky's Question 38

## Abstract

Sixty times every nonnegative power of two is strongly pseudoperfect.

**Theorem 1.1 (An affirmative answer for the entire binary family).**

Lean statement: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result` (`✓ std3`). ∎

*Resolves.* `Problems/mccormack-zelinsky-2023-question-38` (proved) by `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mccormack-zelinsky-2023-question-38","declaration_gid":"D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

For every natural number j, including zero, n=60*2^j is strongly pseudoperfect. This uses the positive integer predicate StrongPseudoperfectDensity.StronglyPseudoperfect: there is a finite subset S of n.divisors with sum 2*n, and for every divisor d, d is in S if and only if n/d is in S. This is exactly Question 38 on page 17 of the source.

Write a=j+2, so n=15*2^a. For a>=5, every chosen divisor has the form 2^i*d with d dividing 15. At levels 0 and a take d in {1,15}; at levels 1 and a-1 take d in {1,3,5,15}; at levels 2 and a-2 take nothing; at levels 3 through a-3 take d in {3,5}. The last range is empty when a=5. Coprimality of 15 and 2^a makes the products distinct.

Complementation sends (i,d) to (a-i,15/d). Each of the three odd-part sets is closed under d -> 15/d, and its level set is closed under i -> a-i. Thus the chosen divisor set is closed under exact complementation.

The geometric sum over 3<=i<=a-3 equals 2^(a-2)-8. Consequently the chosen divisor sum is 16*(1+2^a)+24*(2+2^(a-1))+8*(2^(a-2)-8) =30*2^a=2*n. The three smaller cases n=60,120,240 use all divisors except, respectively, {2,30,6,10}, {3,40,5,24,6,20,10,12}, and {2,120,4,60,6,40,12,20}; every omitted set is a union of complementary pairs, and the remaining sums are 120,240,480.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result`
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectDensity](StrongPseudoperfectDensity.md)
