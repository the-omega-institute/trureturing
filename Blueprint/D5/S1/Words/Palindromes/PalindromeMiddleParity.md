# Middle Parity of an Odd Palindrome

## Abstract

An odd-length palindrome decomposes around a middle entry that determines its sum parity.

This document closes only the palindrome lemma in residual appendix E.107. It does not formalize the subsequent Pell or Rademacher claims.

**Theorem 1.1 (The middle entry determines the sum parity).**

$$\forall w\in\operatorname{List}(\mathbb{N}),\ \operatorname{Palindrome}(w) \land \operatorname{odd}(\operatorname{length}(w)) \Rightarrow \exists u,m,\ w = \operatorname{append}(u,[m],\operatorname{reverse}(u)) \land \operatorname{mod}(\operatorname{sum}(w),2) = \operatorname{mod}(m,2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PalindromeMiddleParity.odd_palindrome_sum_mod_two_eq_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Palindrome induction removes matching endpoints in pairs. Odd length leaves one middle entry, and every removed pair contributes an even amount to the natural-number sum.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PalindromeMiddleParity.odd_palindrome_sum_mod_two_eq_middle`
