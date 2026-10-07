# Signed-Weight Lower Bound for Period Doubling

## Abstract

Every actual period-doubling prefix requires at least the signed weight of its rounded half.

**Theorem 1.1 (A lower bound for the true prefix palindromic length).**

$$\left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(j < n \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{Nat.sub}\left(n, j\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(j + \operatorname{val}\left(i\right)\right)\right)\right)\right) \Rightarrow \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{Nat.div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) \le \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{Nat.div}\left(j + 1, 2\right), \mathbb{Z}\right)\right) + 1\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{Nat.div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) \le \operatorname{PL}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound.palindromic_suffix_signed_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual palindrome suffix from cut j to endpoint n, the signed binary weight of the rounded half of n is at most one more than the weight at j. The short-radius and long-radius cases use different dyadic estimates, and the even-palindrome case has length two. Strong induction along optimal suffix cuts gives the second clause for every prefix. Nat.sub is truncated natural subtraction, Nat.div is natural integer division, and cast denotes the natural-to-integer embedding.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound.palindromic_suffix_signed_bound`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight](DyadicSignedWeight.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome](EvenPalindrome.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius](OddPalindromeRadius.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength](PalindromicLength.md)
