# Balance of an Even Palindrome

## Abstract

An even-length palindrome has zero alternating sum.

This document closes only the even-palindrome balance sentence in residual remark 27.330. It does not formalize the trace formula, drift formula, or the converse claim that balance need not imply palindromicity.

**Theorem 1.1 (An even palindrome is alternatingly balanced).**

$$\forall w\in\operatorname{List}(\mathbb{Z}),\ \operatorname{Palindrome}(w) \land \operatorname{even}(\operatorname{length}(w)) \Rightarrow \operatorname{alternatingSum}(w) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PalindromeBalance.even_palindrome_alternating_sum_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's alternating-sum reversal law changes the sign when the list has even length. Palindromicity identifies the reversed list with the original list, so the integer alternating sum equals its own negative and therefore vanishes.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PalindromeBalance.even_palindrome_alternating_sum_eq_zero`
