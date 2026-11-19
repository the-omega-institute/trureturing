# McCormack and Zelinsky's Question 45 (#31746)

## Abstract

The weighted totient condition D1 is a strong property among Euler forms.

**Definition 1.1 (Pseudoperfect integers).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.Pseudoperfect`

*Formalization.* `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.Pseudoperfect` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

Pseudoperfect(n) means that a finite subset T of the proper divisors of n has sum n. Positivity is imposed by the counting interval, which excludes zero.

**Definition 1.2 (The weighted logarithmic mean).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightA`

*Formalization.* `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightA` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

For a finite set S and a natural number n, weightA(S,n) is the sum over d in S of (d/(2*n))*log(phi(d)), with the weights, totients and logarithms interpreted in the reals. This is equation (12).

**Definition 1.3 (The complementary totient sum).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightC`

*Formalization.* `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightC` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

For a finite set S and a natural number n, weightC(S,n) is log of the sum over d in S of phi(n/d)/(2*d). Here n/d inside phi is natural division, and the outer sum and logarithm are real. Divisor membership ensures exact division when this expression is used for D1. This is equation (14).

**Definition 1.4 (The source's D1 property).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.D1`

*Formalization.* `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.D1` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

D1(n) requires Pseudoperfect(n) and the existence of a finite subset S of the positive divisors of n with sum 2*n and weightA(S,n) <= weightC(S,n). The independent pseudoperfect conjunct is retained. The set S may contain n and need not contain 1 or be closed under complementary divisors.

**Definition 1.5 (Counting D1 Euler forms).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.eulerD1Count`

*Formalization.* `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.eulerD1Count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

eulerD1Count(X) counts integers n from 1 to X satisfying both EulerForm(n) and D1(n). EulerForm is the existing predicate n=q^s*m^2 with q prime, q and s congruent to one modulo four, m positive, and q coprime to m. It does not impose oddness on m. Integers are counted once regardless of their representations.

**Theorem 1.6 (D1 is a strong property).**

Lean statement: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/mccormack-zelinsky-2023-question-45` (proved) by `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mccormack-zelinsky-2023-question-45","declaration_gid":"D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

As the natural threshold X tends to infinity, eulerD1Count(X)/eulerCount(X) tends to zero. This is precisely the source's definition of a strong property and answers Question 45. Real thresholds reduce to natural-number floors.

For any prime q and positive r, D1(q*r) implies q <= sigma(r), without a coprimality assumption. If q exceeds sigma(r), the elements of S not divisible by q divide r. Their sum u is less than q, while the total sum 2*q*r and the remaining terms show q divides u. Thus u is zero, and positivity makes that subset empty.

Consequently S=q*T for a nonempty subset T of the divisors of r. The sum of phi(r/e) over all divisors e of r equals r. It follows that the logarithm argument Z satisfies 0 < Z <= r/(2*q) < 1. Hence weightC(S,q*r) is negative. Positive divisors have totient at least one, so weightA is nonnegative, contradicting the D1 inequality.

For exponent s=1, the prime obstruction bounds q by sigma(m^2). The existing finite images for small and large square factors apply directly. Their cardinalities are at most 3*T^3 and 2*X/(T+1). For every allowed exponent at least five, write s=5+4*j and absorb q^(2*j) into m. The existing high-power image contributes at most sqrt(X). Image cardinalities bound the count without requiring uniqueness of representation.

With T the integer part of X^(1/6), these bounds give eulerD1Count(X) <= 4*X^(5/6) when X^(1/6) is at least two. For smaller X, the elementary bound eulerD1Count(X) <= X gives the same estimate. Thus it holds for all X at least one. Every prime congruent to one modulo four is an Euler form with s=m=1, giving eulerCount(X) >= exp(-50)*X/log(X) eventually. The ratio is therefore at most 4*exp(50)*log(X)/X^(1/6), which tends to zero. Five also witnesses positivity of the denominator for every X at least five.

Question 44 concerns complementary-divisor-closed sets. Its density conclusion alone does not imply this one, because D1 imposes no such closure on S.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.D1`
- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.Pseudoperfect`
- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.eulerD1Count`
- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result`
- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightA`
- Truth anchor: `D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.weightC`
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity](StrongPseudoperfectEulerDensity.md)
