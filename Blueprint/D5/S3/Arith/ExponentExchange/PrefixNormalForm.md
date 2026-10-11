# Exponent Normal Form with the Same Number of Distinct Primes

## Abstract

Every positive integer has a companion no larger, with as many distinct primes and non-increasing exponents, whose normalized divisor sum is at least as large.

**Theorem 1.1 (A no-larger integer with non-increasing exponents dominates sigma(n)/n).**

Lean statement: `D5/S3/Arith/ExponentExchange/PrefixNormalForm.exists_antitone_exponent_form`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/PrefixNormalForm.exists_antitone_exponent_form` (`✓ std3`). ∎

*Citation.* Leonidas Alaoglu and Paul Erdos (1944). *On highly composite and similar numbers*. DOI: [10.2307/1990319](https://doi.org/10.2307/1990319).

*Commentary.*

For every natural number n at least 1 there is m with 1 <= m <= n, the same number of distinct prime factors as n (the cardinality of Nat.primeFactors), Nat.factorization m q <= Nat.factorization m p for all primes p < q, and sigma(1,n)/n <= sigma(1,m)/m in the real numbers. The exponent condition forces the support of m to be an initial segment of the primes: if q divides m then every smaller prime divides m.

The proof is strong induction on n. When the exponents already decrease, m = n. Otherwise there are primes p < q with smaller exponent at p, possibly zero, and the frozen exchange theorem IntegerSwap.prime_exponent_swap swaps the two exponents: the result is a smaller positive integer with a strictly larger normalized divisor sum. Writing the integer as t*p^a*q^b with t coprime to p*q, its number of distinct primes is that of t plus one for each nonzero exponent, so the swap keeps the count. The induction hypothesis applied to the smaller integer finishes.

Because the companion is no larger, e^gamma*log(log(m)) <= e^gamma*log(log(n)) whenever m > 1, so Robin's inequality at a companion m above 5040 implies it at n. The theorem therefore reduces Robin's inequality for integers with a bounded number of distinct primes to products of powers of the first primes with non-increasing exponents. The exchange argument is the one Alaoglu and Erdos use for superabundant numbers; here it is iterated on an arbitrary integer and keeps the number of distinct primes. The companion is not claimed to be unique or to maximize sigma(1,m)/m among integers up to n.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/PrefixNormalForm.exists_antitone_exponent_form`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](IntegerSwap.md)
