# Square Divisibility of the Collinear-Triple Formula

## Abstract

Bala's square-divisibility conjecture holds for Alekseyev's A146557 formula.

The Lean sequence is defined by Max Alekseyev's formula in OEIS A146557. The identification of that formula with the geometric count is the OEIS author's formula and is not re-proved here. Ordered matrix triples and unordered geometric triples differ by a factor of six; neither counting interpretation is a formal claim of this module. Peter Bala stated the divisibility conjecture on July 24, 2025.

Indices and triple coordinates are natural numbers. The functions fst and snd are the two product projections, so a triple has type N times (N times N). The function range(m) is the finite set of natural numbers strictly below m. The gcd values are natural numbers, coerced to integers in summand. All arithmetic in summand, a, and the three theorem conclusions is integer arithmetic; the hypothesis that three does not divide n is natural-number divisibility.

**Definition 1.1 (Positive three-part compositions).**

$$\forall n: \mathbb{N}, \operatorname{triples}\left(n\right) = \{triple \in \operatorname{range}\left(n + 1\right) \times (\operatorname{range}\left(n + 1\right) \times \operatorname{range}\left(n + 1\right)) \mid (0 < \operatorname{fst}\left(triple\right)) \land (0 < \operatorname{fst}\left(\operatorname{snd}\left(triple\right)\right)) \land (0 < \operatorname{snd}\left(\operatorname{snd}\left(triple\right)\right)) \land (\operatorname{fst}\left(triple\right) + \operatorname{fst}\left(\operatorname{snd}\left(triple\right)\right) + \operatorname{snd}\left(\operatorname{snd}\left(triple\right)\right) = n)\}$$

*Formalization.* `D5/S3/Factorization/CollinearTripleCountDivisibility.triples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite product supplies all three coordinates from zero through n. Filtering retains precisely the positive coordinates whose sum is n.

**Definition 1.2 (Alekseyev's symmetric summand).**

$$\forall n: \mathbb{N}, \forall triple: \mathbb{N} \times (\mathbb{N} \times \mathbb{N}), \operatorname{summand}\left(n, triple\right) = n \cdot \operatorname{gcd}\left(\operatorname{gcd}\left(\operatorname{fst}\left(triple\right), \operatorname{fst}\left(\operatorname{snd}\left(triple\right)\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(triple\right)\right)\right) - \operatorname{gcd}\left(\operatorname{fst}\left(triple\right), n\right) - \operatorname{gcd}\left(\operatorname{fst}\left(\operatorname{snd}\left(triple\right)\right), n\right) - \operatorname{gcd}\left(\operatorname{snd}\left(\operatorname{snd}\left(triple\right)\right), n\right) + 2$$

*Formalization.* `D5/S3/Factorization/CollinearTripleCountDivisibility.summand` (`✓ std3`).

*Citation.* Peter Bala; Max Alekseyev (2025). *OEIS A146557, collinear triples in Z_n x Z_n*. URL: <https://oeis.org/A146557>.

*Commentary.*

The three subtractions take place in the integers. Cyclically permuting the coordinates preserves the nested gcd and permutes the subtracted terms.

**Definition 1.3 (The formula-defined sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = n \cdot \sum_{triple \in \operatorname{triples}\left(n\right)} (\operatorname{summand}\left(n, triple\right) \cdot \operatorname{snd}\left(\operatorname{snd}\left(triple\right)\right))$$

*Formalization.* `D5/S3/Factorization/CollinearTripleCountDivisibility.a` (`✓ std3`).

*Citation.* Peter Bala; Max Alekseyev (2025). *OEIS A146557, collinear triples in Z_n x Z_n*. URL: <https://oeis.org/A146557>.

*Commentary.*

The sequence is n times the sum of summand multiplied by the third coordinate. This is a definition by Alekseyev's formula, not a proof that the formula enumerates geometric triples.

**Lemma 1.4 (The cyclic moment identity).**

$$\forall n: \mathbb{N}, 3 \cdot \operatorname{a}\left(n\right) = n^{2} \cdot \sum_{triple \in \operatorname{triples}\left(n\right)} (\operatorname{summand}\left(n, triple\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleCountDivisibility.three_mul_a_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map (i,j,k) to (j,k,i) preserves the finite composition set and has inverse (i,j,k) to (k,i,j). Reindexing by this explicit bijection equates the three coordinate-weighted sums. Adding them replaces the coordinate weight by i+j+k=n, and multiplying by n gives the identity. This reindexing is the new intermediate fact on the main proof path.

**Lemma 1.5 (The symmetric total is divisible by three).**

$$\forall n: \mathbb{N}, \neg (3 \mid n) \implies 3 \mid \sum_{triple \in \operatorname{triples}\left(n\right)} (\operatorname{summand}\left(n, triple\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleCountDivisibility.three_dvd_summand_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moment identity shows that three divides n squared times the symmetric total. Since three is prime and does not divide n, it is coprime to n squared. Mathlib's integer Euclid lemma therefore gives divisibility of the total. This avoids an unnecessary totient expansion.

**Theorem 1.6 (Bala's conjecture for the formula-defined sequence).**

$$\forall n: \mathbb{N}, \neg (3 \mid n) \implies n^{2} \mid \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleCountDivisibility.sq_dvd_a` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a146557-collinear-triple-square-divisibility` (proved) by `D5/S3/Factorization/CollinearTripleCountDivisibility.sq_dvd_a`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a146557-collinear-triple-square-divisibility","declaration_gid":"D5/S3/Factorization/CollinearTripleCountDivisibility.sq_dvd_a","resolution_kind":"proved"} -->

*Citation.* Peter Bala; Max Alekseyev (2025). *OEIS A146557, collinear triples in Z_n x Z_n*. URL: <https://oeis.org/A146557>.

*Commentary.*

Write the symmetric total as three times an integer quotient. Substitution in the cyclic moment identity and cancellation of three expresses a(n) as n squared times that quotient. The theorem holds for every natural n not divisible by three, without a search bound.

## References

- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.a`
- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.sq_dvd_a`
- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.summand`
- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.three_dvd_summand_sum`
- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.three_mul_a_eq`
- Truth anchor: `D5/S3/Factorization/CollinearTripleCountDivisibility.triples`
