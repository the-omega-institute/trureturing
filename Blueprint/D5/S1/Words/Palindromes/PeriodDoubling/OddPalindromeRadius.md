# Exact Odd-Palindrome Radii

## Abstract

Every scale and every positive center has a complete reflection test.

**Theorem 1.1 (The complete positive-center radius law).**

$$\forall r \in \mathbb{N},\; \forall u \in \mathbb{N},\; \forall R \in \mathbb{N},\; \left(\operatorname{mod}\left(u, 2\right) = 1 \land R < 2^{r} \cdot u\right) \Rightarrow \left(\operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(2 \cdot R + 1\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{Nat.sub}\left(\operatorname{Nat.sub}\left(2^{r} \cdot u, R\right), 1\right) + \operatorname{val}\left(i\right)\right)\right)\right) \Leftrightarrow R < \operatorname{ite}\left(u = 1, 2^{r}, \operatorname{ite}\left(\operatorname{mod}\left(\operatorname{max}\left(\operatorname{padicValNat}\left(2, \operatorname{Nat.sub}\left(u, 1\right)\right), \operatorname{padicValNat}\left(2, u + 1\right)\right), 2\right) = 0, 2^{r}, 3 \cdot 2^{r}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius.odd_palindrome_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The center is the positive one-based index 2^r u, with odd u. The tested radius is strictly below the center, so every left index remains positive. For u=1 all available reflections agree. Otherwise the first disagreement is at q=2^r when the maximum adjacent valuation is even, and at 3q when it is odd. The word uses zero-based indexing, hence the subtraction of one from both positive endpoints. Natural subtraction is truncated, and mod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius.odd_palindrome_radius`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/Word](Word.md)
