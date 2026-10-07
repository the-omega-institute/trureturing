# An explicit upper bound for Frid prefixes

## Abstract

An explicit upper bound for Frid prefixes

**Theorem 1.1 (frid_upper).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow PL\left(goldenFactor\left(N\left(k\right), 0\right)\right) \le 2 \cdot k + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/FridUpper.frid_upper` (`✓ std3`). ∎

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

Frid writes on printed page 12: “We proved that 2k + 1 palindromes are enough for this word, so, it remains just to prove that this is the minimal possible value.” The proof uses consecutive symmetric trims of Fibonacci central palindromes. True represents the letter 0 and false the letter 1.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/FridUpper.frid_upper`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/FridNumerals](FridNumerals.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PalindromicLength](PalindromicLength.md)
