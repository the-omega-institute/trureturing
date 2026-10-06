# Alternating Tail Upper Bound

## Abstract

Two legal cuts remove two alternating blocks at every scale.

**Theorem 1.1 (Uniform upper bound including the neighboring endpoint).**

$$\forall k \in \mathbb{N},\; \forall eps \in \mathbb{N},\; eps \le 1 \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(2 \cdot k\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) \le 2 \cdot k + eps$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper.alternating_tail_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For epsilon zero or one, two odd palindromic suffix cuts remove two alternating binary blocks and preserve the endpoint bit. Their centers use odd parts nine and one. Induction repeats the construction and ends at the empty prefix or a singleton. PL is the true minimum number of nonempty palindrome factors, and val denotes the natural value of a finite index.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper.alternating_tail_upper`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PalindromicLength](../FridPrefix/PalindromicLength.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius](OddPalindromeRadius.md)
