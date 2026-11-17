# A124056 divisibility-count recurrence

## Abstract

A124056 divisibility-count recurrence

The sequence starts with one. Each later term counts all preceding indices whose values divide the immediately preceding value, including that preceding index and retaining multiplicities. The internal value term(n) is the source value a(n+1). Its finite tuple contains exactly the first n+1 terms. The positive-index sourceTerm(n)=term(n-1) is used only at n at least one; no value at zero enters its recurrence.

**Theorem 1.1 (Exact original initialization and recurrence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source sequence has sourceTerm(1)=1. For every positive natural n, sourceTerm(n+1) is the cardinality of the indices i in the closed interval from one to n for which sourceTerm(i) divides sourceTerm(n). The tuple consistency proof establishes the actual index dictionary, preserving the self index and repeated values. The initial values are 1,1,2; the only ones occur at internal indices zero and one, and all terms from internal index three onward are at least three.

**Theorem 1.2 (A global sublinear multiplicity estimate is impossible).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let count(N,d) count occurrences of d at internal indices less than N, and let prefixMax(N) be the maximum through internal index N, inclusive. There are no fixed positive real C and delta such that count(N,d) is at most C times prefixMax(N) to the power 1-delta for every N and every positive d. At repeated equal values the successors strictly increase, so the pair consisting of a value and its successor is injective and the sequence is unbounded. A proposed estimate and the classical divisor subpower bound at epsilon=delta/2 would bound every prefix maximum by one fixed constant, a contradiction.

**Theorem 1.3 (Infinitely many threes imply full positive occurrence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that for every natural B there is an internal index n at least B with term(n)=3. Then for every positive k there is a positive source index n with sourceTerm(n)=k. The exact successor of a three is two plus the number of threes through that occurrence. The count increases by zero or one, and the assumed cofinal occurrences make it unbounded. Its first crossing of each positive threshold therefore gives that exact count. This result explicitly retains the infinitely-many-threes hypothesis.

**Theorem 1.4 (Finitely many threes force one missing residue class).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the set of internal indices at which the value is three is finite, there is a natural q at least two such that every sequence value greater than one has remainder different from one modulo q. A seed is an internal index i at least two with no earlier divisor value at an index from two to i-1. Such a seed is equivalent to its successor having value three, so there are finitely many seeds. Their values have a finite LCM q, divisible by two. The earliest divisor index from two through any index n is a seed, providing a common divisor at least two of q and term(n). Such a value cannot have remainder one modulo q.

**Theorem 1.5 (Residue avoidance bounds contributor ranks).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.contributor_rank_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.contributor_rank_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write D(t,v) for the number of internal indices i less than t whose values divide v. Suppose q is at least two and every term through internal index N greater than one has remainder different from one modulo q. For every t at most N and v at least two, D(t,v) is at most q times the sum of count(t,d) over the proper divisors d of v. A proper-divisor contributor increases the available bound by q. An equal-value contributor cannot cross that bound, since the crossing successor would be one modulo q. The first rank is a proper-divisor contribution from the initial one; t=0 has no contributors. The successor of every counted index remains within the avoided prefix.

**Theorem 1.6 (Splitting distinct ordered prime words).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive v, primeWords(v) is the finite set of distinct permutations of its prime-factor list. Its cardinality b(v) counts ordered prime words and omega(v) is their common length, counting prime factors with multiplicity. For every j from zero through omega(v), the sum of b(d)b(v/d) over divisors d of v with omega(d)=j equals b(v). Concatenation is a bijection: take and drop at position j recover the two words, and unique prime factorization recovers d from the first product. The empty word gives b(1)=1, so both endpoint splits are included.

**Theorem 1.7 (The proper-divisor weight sum is absorbed).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural A and positive v define W(A,v)=A to the power omega(v), times b(v). For every natural q, q times the sum of W(q+1,d) over proper divisors d of v is at most W(q+1,v). At each factor-count layer, the split identity and b(v/d) at least one bound the sum of b(d) by b(v). A proper divisor has strictly fewer prime factors with multiplicity. The geometric identity q times the sum of (q+1) to the powers below k, plus one, equals (q+1) to the power k completes the estimate.

**Theorem 1.8 (Prime-word majorant for actual divisor counts).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.divisor_card_le_prime_word_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.divisor_card_le_prime_word_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same prefix residue avoidance with q at least two, every t at most N and every positive v satisfy D(t,v) at most 2W(q+1,v). Strong induction on v combines the contributor-rank bound, count(t,d) at most D(t,d), and the proper-divisor weight estimate. For v=1 the only possible contributors are the two initial ones, and W(q+1,1)=1. This is a pointwise bound under finite-prefix avoidance, without a uniform sublinear frequency conclusion.

**Theorem 1.9 (Occurrences and distinct predecessor values).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.count_le_prime_word_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.count_le_prime_word_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same avoidance hypothesis, for every t at most N and d at least two, count(t,d) is bounded both by 2W(q+1,d) and by the cardinality of the positive v at most prefixMax(N) with d at most 2W(q+1,v). Each occurrence index i of d is positive and maps to the actual predecessor term(i-1). Equal predecessor values have strictly increasing successors, so this map is injective on occurrences of d. The exact recurrence and the pointwise majorant place every image in the displayed finite level set. The restriction d at least two excludes the initial term, which has no predecessor.

**Theorem 1.10 (The exact weighted first-letter recurrence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_first_letter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_first_letter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural weight A and every v greater than one, W(A,v) equals A times the sum of W(A,v/p) over the distinct prime divisors p of v. This follows from the rank-one prime-word split; a word of length one is exactly one prime, and removing it decreases the length by one.

**Theorem 1.11 (Finite prime sums control all prime words).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If C times the sum of p to the power minus r is at most one for every finite prime set, then W(C,v) is at most v to the power r for every positive v. Strong induction applies the exact first-letter recurrence and factors out v to the power r. The empty word at v=1 is included.

**Theorem 1.12 (A polynomial bound with a fixed exponent).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_polynomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_polynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural A there exists a real r greater than one, chosen using A alone, such that W(2A,v) is at most v to the power r for all positive v. The convergent square reciprocal series bounds every finite prime sum. Increasing the exponent by a natural k introduces at most the factor two to the power minus k, which can be made small enough independently of v.

**Theorem 1.13 (A finite rough first-moment bound).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.rough_prime_word_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.rough_prime_word_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let roughPrefix(S,X) contain the positive integers at most X with every prime divisor outside S. Suppose C times every finite outside prime sum of p to the power minus sigma is at most one half. Then the sum of W(C,n) times n to the power minus sigma over roughPrefix(S,X) is at most two. The first-letter pairs inject into the product of the outside primes at most X and the same rough prefix. Their sum is at most half the original sum; the empty word contributes at most one.

**Theorem 1.14 (Doubled weights bound a product split).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural A and positive m,n, W(A,mn) is at most W(2A,m)W(2A,n). The proof inducts on m+n and uses the first-letter recurrence. Every prime divisor of mn divides m or n; their union sum is at most the two sums together. The doubled weight absorbs both terms. No coprimality or multiplicativity assumption is used.

**Theorem 1.15 (The fixed fractional moment on finite positive sets).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_finite_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_finite_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix A at least one, real r,s with s positive and at most one and rs equal to one half, and a pointwise bound W(2A,v) at most v to the power r for every positive v. For every sigma greater than one there exists a positive H such that the sum of W(A,v) to the power s times v to the power minus sigma over every finite positive set is at most H. A finite prime tail is chosen before the set. Splitting prime support gives an injective map into smooth and rough factors. The smooth bound uses the finite-prime Euler product at sigma minus one half, requiring local prime-power convergence only. The rough bound is the finite absorption estimate. The same s applies to every sigma.

**Theorem 1.16 (Uniform sublinear counts under residue avoidance).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.uniform_count_bound_of_avoidance`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.uniform_count_bound_of_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each q at least two there are positive real constants C and delta such that for every prefix N and every positive d, AvoidsResidue(q,N) implies count(N,d) at most C times prefixMax(N) to the power 1-delta. Choose r using q alone, set s=1/(2r), delta=s squared divided by two and sigma=1+delta. The fixed-s finite moment bounds the actual distinct predecessor level set by the finite Markov inequality. For d at most the maximum to the power s, the pointwise bound gives exponent one half. For larger d, the Markov bound gives exponent 1-delta. The two initial ones and all small prefixes are included. Every parameter is fixed before N and d.

**Theorem 1.17 (Every positive integer occurs in the original sequence).**

Lean statement: `D5/S3/Arith/Recurrence/A124056Occurrence.full_positive_occurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/A124056Occurrence.full_positive_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k there exists a positive source index n with sourceTerm(n)=k. If the three fiber were finite, the missing-residue theorem would provide one fixed modulus avoided by every prefix. The uniform count bound for that modulus would contradict the impossibility of a global sublinear multiplicity bound. Thus the three fiber is infinite and has cofinal indices. The exact infinite-three implication then gives all positive source values, without an added assumption. The recurrence, repeated values and self index are the original ones.

The analytic proof uses finite sums throughout. The fixed fractional exponent is selected from the weight parameter before sigma; only the finite prime tail and its smooth constant depend on sigma. The finite-prime Euler-product supplier requires convergence along each prime-power sequence, without global summability of the unweighted smooth majorant on all naturals. The full occurrence conclusion concerns the exact initialized recurrence and does not assert a uniform multiplicity bound for arbitrary sequences.

## References

- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.contributor_rank_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.count_le_prime_word_bounds`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.divisor_card_le_prime_word_weight`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.full_occurrence_of_infinite_three`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.full_positive_occurrence`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.no_uniform_sublinear_count_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_finite_moment`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_first_letter`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_pointwise`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_polynomial_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_product_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_split`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.prime_word_weight_bound`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.rough_prime_word_sum`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.source_specification`
- Truth anchor: `D5/S3/Arith/Recurrence/A124056Occurrence.uniform_count_bound_of_avoidance`
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Divisors/DivisorSubpower.md)
