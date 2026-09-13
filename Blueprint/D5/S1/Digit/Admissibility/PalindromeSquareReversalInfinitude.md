# Palindrome Squares and Their Reversals

## Abstract

Brockhaus and Seidov's sequence of palindromes with reversed-square witnesses is infinite.

All variables are natural numbers. Decimal digits are read by Nat.digits from least significant to most significant; reversing that list before applying ofDigits therefore reverses the ordinary decimal representation numerically.

**Definition 1.1 (Decimal reversal).**

$$\forall n \in \mathbb{N},\; rev10\left(n\right) = ofDigits\left(10, reverse\left(digits\left(10, n\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.rev10` (`✓ std3`).

*Citation.* Klaus Brockhaus; Zak Seidov (2007). *OEIS A133901, Numbers in A128921 whose square is not a palindrome*. URL: <https://oeis.org/A133901>.

*Commentary.*

The value rev10(n) is the number whose decimal representation is obtained by reversing the decimal representation of n. Nat.digits lists the least-significant digit first.

**Definition 1.2 (Decimal palindromes).**

$$\forall n \in \mathbb{N},\; IsPalindrome10\left(n\right) \Leftrightarrow (rev10\left(n\right) = n)$$

*Formalization.* `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.IsPalindrome10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural number is a decimal palindrome exactly when decimal reversal leaves it unchanged.

**Definition 1.3 (Membership in A133901).**

$$\forall p \in \mathbb{N},\; IsMember\left(p\right) \Leftrightarrow (IsPalindrome10\left(p\right) \land \left(\left(\neg IsPalindrome10\left(p^{2}\right)\right) \land \left(\exists q \in \mathbb{N},\; rev10\left(p^{2}\right) = q^{2}\right)\right))$$

*Formalization.* `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.IsMember` (`✓ std3`).

*Citation.* Klaus Brockhaus; Zak Seidov (2007). *OEIS A133901, Numbers in A128921 whose square is not a palindrome*. URL: <https://oeis.org/A133901>.

*Commentary.*

This is the intersection of A128921 with the requirement that the member's square is not a palindrome: p is palindromic, p squared is not palindromic, and the reversed square is itself a square.

**Theorem 1.4 (Infinitude of A133901).**

$$\forall B \in \mathbb{N},\; \exists p \in \mathbb{N},\; B < p \land IsMember\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.brockhaus_seidov_a133901` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a133901-palindrome-square-reversal-infinitude` (proved) by `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.brockhaus_seidov_a133901`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a133901-palindrome-square-reversal-infinitude","declaration_gid":"D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.brockhaus_seidov_a133901","resolution_kind":"proved"} -->

*Citation.* Klaus Brockhaus; Zak Seidov (2007). *OEIS A133901, Numbers in A128921 whose square is not a palindrome*. URL: <https://oeis.org/A133901>.

*Commentary.*

For every natural bound B, the explicit decimal-block construction supplies a larger palindrome p whose square is not a palindrome and whose reversed square is a perfect square. Thus the sequence is unbounded and hence infinite.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.IsMember`
- Truth anchor: `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.IsPalindrome10`
- Truth anchor: `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.brockhaus_seidov_a133901`
- Truth anchor: `D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude.rev10`
