# Two-Dense Divisor Blocks Are Palindromic

## Abstract

The maximal two-dense divisor blocks form a palindromic composition.

Omar E. Pol's June 3, 2025 entry OEIS A384222 states Conjecture 1: row n is a palindromic composition of A000005(n). The proof here applies to every positive natural n.

The function splitBy retains adjacent entries a,b in the same maximal block exactly when its Boolean relation is true. The first coordinates of divisorsAntidiagonalList(n) list every positive divisor once, in increasing order. All lengths and indices are natural numbers.

**Definition 1.1 (Lengths of the maximal blocks).**

$$\forall l: \operatorname{List}(\mathbb{N}), \operatorname{twoDenseBlockLengths}(l) = \operatorname{map}(\operatorname{length}, \operatorname{splitBy}((a b \mapsto \operatorname{decide}(b \le 2\cdot a)), l))$$

*Formalization.* `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.twoDenseBlockLengths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cut precisely where b exceeds twice a, and take the length of each resulting nonempty block.

**Definition 1.2 (The row of OEIS A384222).**

$$\forall n: \mathbb{N}, \operatorname{row}(n) = \operatorname{twoDenseBlockLengths}(\operatorname{map}(\operatorname{fst}, \operatorname{divisorsAntidiagonalList}(n)))$$

*Formalization.* `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the block-length function to the increasing divisor list. Mathlib uses an empty divisor list at n=0.

**Theorem 1.3 (The sum is the divisor count).**

$$\forall n: \mathbb{N}, 0 < n \implies \operatorname{sum}(\operatorname{row}(n)) = \operatorname{card}(\operatorname{divisors}(n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening splitBy restores the original list. Its distinct entries are exactly the positive divisors, so the sum of the block lengths equals the cardinality of divisors(n).

**Theorem 1.4 (Conjecture 1).**

$$\forall n: \mathbb{N}, 0 < n \implies \operatorname{reverse}(\operatorname{row}(n)) = \operatorname{row}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_palindrome` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a384222-two-dense-divisor-blocks-palindrome` (proved) by `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_palindrome`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a384222-two-dense-divisor-blocks-palindrome","declaration_gid":"D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_palindrome","resolution_kind":"proved"} -->

*Citation.* Omar E. Pol (2025). *OEIS A384222, lengths of the 2-dense sublists of divisors of n*. URL: <https://oeis.org/A384222>.

*Commentary.*

The divisor complement d maps to n divided by d, using natural integer division, and reverses the divisor list. For divisors a,b, the relation b at most twice a is equivalent to the complement of a being at most twice the complement of b. A general reversal lemma constructs the reversed block decomposition and verifies both its internal links and its separating boundaries using splitBy uniqueness. Taking lengths gives the palindrome. The sum theorem and nonemptiness of every block complete the composition assertion.

## References

- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_palindrome`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.row_sum`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.twoDenseBlockLengths`
