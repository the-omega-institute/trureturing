# The original OEIS A167857 question

## Abstract

An integral polynomial represents all increasing divisors of an integer with three distinct prime factors.

**Theorem 1.1 (A term with three distinct prime divisors exists).**

$$\exists n \in \mathbb{N}, 0 < n \land \operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right) = 3 \land \exists f \in \mathbb{Z}[X], \forall j \in \mathbb{N}, j < \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right) \Rightarrow f\left(j\right) = \operatorname{get}\left(\operatorname{sortIncreasing}\left(\operatorname{divisors}\left(n\right)\right), j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a167857-sorted-divisor-polynomial-three-primes` (proved) by `D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a167857-sorted-divisor-polynomial-three-primes","declaration_gid":"D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. D. Noe (2009). *OEIS A167857: Numbers whose divisors are represented by an integer polynomial*. URL: <https://oeis.org/A167857>.

*Commentary.*

Choose three increasing primes p, q, r, each congruent to 1 modulo 5040, using Nat.exists_prime_gt_modEq_one. Their product n is positive, has exactly three distinct prime factors and exactly eight positive divisors. Decomposition of a divisor of p*q*r into divisors of the three primes shows that every divisor is 1 modulo 5040.

Let d_i be entry i in the actual increasing sort of Nat.divisors n. For i=0,...,7 let D_i be the product of i-j over the other seven indices and N_i(X) the product of X-j over those indices. The signed D_i are -5040, 720, -240, 144, -144, 240, -720, 5040; each is nonzero and divides 5040. Thus c_i=(d_i-1)/D_i is an integer and f=1+sum_i c_i*N_i belongs to Polynomial Int. Its rational image is 1 plus the existing Lagrange interpolant of d_i-1. Applying Lagrange.eval_interpolate_at_node and injectivity of the integer-to-rational map gives the required integer evaluation at every original zero-based index.

The sorted finset contains all positive divisors of this same n exactly once. The statement imposes no minimum n, degree bound, prescribed numerical candidate, divisor subset or input shift. Polynomial Int ensures integral coefficients; integer-valued rational interpolation alone would not establish this claim.

The source asks: Are there terms with three distinct prime divisors? The proof applies existing Mathlib results on primes in arithmetic progressions and Lagrange interpolation. No new-method or priority claim is made. Source license: CC-BY-SA-4.0.

## References

- Truth anchor: `D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result`
