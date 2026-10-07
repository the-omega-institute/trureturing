# Even Palindromes in Period Doubling

## Abstract

An even palindrome in period doubling has length zero or two.

**Theorem 1.1 (The even-palindrome obstruction).**

$$\forall s \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(2 \cdot k\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(s + \operatorname{val}\left(i\right)\right)\right)\right) \Rightarrow k \le 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome.even_palindrome_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuo Li (2020). *Palindromic length sequence of the ruler sequence and of the period-doubling sequence*. URL: <https://arxiv.org/abs/2007.08317v1>.

*Commentary.*

The subword starts at zero-based offset s and has length 2k. Reflection in an even length exchanges index parities. All source letters at even zero-based positions are zero, whereas every four consecutive positions include a one at index congruent to one modulo four. Thus a palindromic factor of even length at least four is impossible.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome.even_palindrome_length`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/Word](Word.md)
