# Weighted ordered prime-factor words

## Abstract

Weighted ordered prime-factor words

The finite words are distinct permutations of the prime-factor list, including the empty word at one. Their weights depend only on the positive integer and a natural weight parameter, independently of any recurrence. The actual A124056 divisor-count and uniform frequency estimates consume these arithmetic bounds. The Lean constants use the shared D5.S3.Arith.Recurrence.A124056Occurrence namespace; their source owner and declaration handles are this module.

**Theorem 1.1 (Splitting distinct ordered prime words).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive v, primeWords(v) is the finite set of distinct permutations of its prime-factor list. Its cardinality b(v) counts ordered prime words and omega(v) is their common length, counting prime factors with multiplicity. For every j from zero through omega(v), the sum of b(d)b(v/d) over divisors d of v with omega(d)=j equals b(v). Concatenation is a bijection: take and drop at position j recover the two words, and unique prime factorization recovers d from the first product. The empty word gives b(1)=1, so both endpoint splits are included.

**Theorem 1.2 (The proper-divisor weight sum is absorbed).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural A and positive v define W(A,v)=A to the power omega(v), times b(v). For every natural q, q times the sum of W(q+1,d) over proper divisors d of v is at most W(q+1,v). At each factor-count layer, the split identity and b(v/d) at least one bound the sum of b(d) by b(v). A proper divisor has strictly fewer prime factors with multiplicity. The geometric identity q times the sum of (q+1) to the powers below k, plus one, equals (q+1) to the power k completes the estimate.

**Theorem 1.3 (The exact weighted first-letter recurrence).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_first_letter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_first_letter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural weight A and every v greater than one, W(A,v) equals A times the sum of W(A,v/p) over the distinct prime divisors p of v. This follows from the rank-one prime-word split; a word of length one is exactly one prime, and removing it decreases the length by one.

**Theorem 1.4 (Finite prime sums control all prime words).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If C times the sum of p to the power minus r is at most one for every finite prime set, then W(C,v) is at most v to the power r for every positive v. Strong induction applies the exact first-letter recurrence and factors out v to the power r. The empty word at v=1 is included.

**Theorem 1.5 (A polynomial bound with a fixed exponent).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_polynomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_polynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural A there exists a real r greater than one, chosen using A alone, such that W(2A,v) is at most v to the power r for all positive v. The convergent square reciprocal series bounds every finite prime sum. Increasing the exponent by a natural k introduces at most the factor two to the power minus k, which can be made small enough independently of v.

**Theorem 1.6 (A finite rough first-moment bound).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.rough_prime_word_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.rough_prime_word_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let roughPrefix(S,X) contain the positive integers at most X with every prime divisor outside S. Suppose C times every finite outside prime sum of p to the power minus sigma is at most one half. Then the sum of W(C,n) times n to the power minus sigma over roughPrefix(S,X) is at most two. The first-letter pairs inject into the product of the outside primes at most X and the same rough prefix. Their sum is at most half the original sum; the empty word contributes at most one.

**Theorem 1.7 (Doubled weights bound a product split).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural A and positive m,n, W(A,mn) is at most W(2A,m)W(2A,n). The proof inducts on m+n and uses the first-letter recurrence. Every prime divisor of mn divides m or n; their union sum is at most the two sums together. The doubled weight absorbs both terms. No coprimality or multiplicativity assumption is used.

**Theorem 1.8 (The fixed fractional moment on finite positive sets).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_finite_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_finite_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix A at least one, real r,s with s positive and at most one and rs equal to one half, and a pointwise bound W(2A,v) at most v to the power r for every positive v. For every sigma greater than one there exists a positive H such that the sum of W(A,v) to the power s times v to the power minus sigma over every finite positive set is at most H. A finite prime tail is chosen before the set. Splitting prime support gives an injective map into smooth and rough factors. The smooth bound uses the finite-prime Euler product at sigma minus one half, requiring local prime-power convergence only. The rough bound is the finite absorption estimate. The same s applies to every sigma.

**Theorem 1.9 (Weights increase with the weight parameter).**

Lean statement: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural A,B,v with A at most B, W(A,v) is at most W(B,v). Monotonicity of natural powers and multiplication gives this bound. The product estimate and the actual recurrence's uniform count estimate consume it; it is a supporting monotonicity fact rather than additional mathematical content.

All prime-word rearrangements are finite. The finite-prime Euler-product supplier requires convergence along each prime-power sequence, without global summability of the unweighted smooth majorant on all naturals. The fixed fractional exponent is chosen before the Dirichlet exponent; the prime tail and smooth bound may depend on that later exponent.

## References

- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_finite_moment`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_first_letter`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_pointwise`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_polynomial_bound`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_product_bound`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_split`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_bound`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.prime_word_weight_mono`
- Truth anchor: `D5/S3/Arith/Factorization/PrimeWordWeight.rough_prime_word_sum`
