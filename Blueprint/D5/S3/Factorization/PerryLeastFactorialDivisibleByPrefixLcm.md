# Perry's Least Factorial Index for the Prefix Lcm

## Abstract

The prefix lcm divides the factorial of its largest prime, which is the least factorial index.

**Theorem 1.1 (The maximal-prime factorial contains the prefix lcm).**

$$\forall n \in \mathrm{Nat}, p \in \mathrm{Nat},\; ((5 \le n) \land ((Prime\left(p\right)) \land (\forall q \in \mathrm{Nat},\; ((Prime\left(q\right)) \land (q \le n)) \Rightarrow q \le p))) \Rightarrow lcmUpto\left(n\right) \mid p!$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.prefix_lcm_dvd_factorial_of_maximal_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Perry (2004). *OEIS A094802, a(n) = smallest k such that all of 1 through n divides k!*. URL: <https://oeis.org/A094802>.

*Commentary.*

For n at least five and any prime p at least as large as every prime not exceeding n, the lcm of 1 through n divides p!. This is stronger than the membership half of the least-index result: it does not require p at most n. It can also be used in later prime-gap and Chebyshev estimates. The pinned lcmUpto factorial endpoint only yields divisibility by n!, whereas the prime-gap bound and the nonprime square and nonsquare cases lower it to p!.

**Theorem 1.2 (The maximal prime is the least factorial index).**

$$\forall n \in \mathrm{Nat}, p \in \mathrm{Nat},\; ((5 \le n) \land ((Prime\left(p\right)) \land ((p \le n) \land (\forall q \in \mathrm{Nat},\; ((Prime\left(q\right)) \land (q \le n)) \Rightarrow q \le p)))) \Rightarrow IsLeast\left(S\left(n\right), p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a094802-perry-least-factorial-divisible-by-prefix-lcm` (proved) by `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a094802-perry-least-factorial-divisible-by-prefix-lcm","declaration_gid":"D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jon Perry (2004). *OEIS A094802, a(n) = smallest k such that all of 1 through n divides k!*. URL: <https://oeis.org/A094802>.

*Commentary.*

Let S(n) be the set of natural k for which the lcm of 1 through n divides k!. For n at least five, a prime p at most n that bounds every prime not exceeding n is the least element of S(n). The maximal-prime factorial lemma supplies membership. Any k in S(n) has p dividing k!, so prime factorial divisibility implies p at most k. The upper bound uses Bertrand's prime gap and a prime-power factorial estimate, including the square case.

## References

- Truth anchor: `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.prefix_lcm_dvd_factorial_of_maximal_prime`
- Truth anchor: `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.result`
