# The exact palindromic length of every Frid prefix

## Abstract

The exact palindromic length of every Frid prefix

**Definition 1.1 (claim).**

$$claim = \left(\forall k \in \mathbb{N},\; 1 \le k \Rightarrow PL\left(goldenFactor\left(N\left(k\right), 0\right)\right) = 2 \cdot k + 1\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.claim` (`✓ std3`).

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

Conjecture 2 on printed page 12 states: “For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.” N(k) is the value of that Zeckendorf numeral with weights G(0)=1,G(1)=2. goldenFactor(N(k),0) is the zero-indexed prefix of goldenWord, the fixed point of 0 -> 01 and 1 -> 0; true represents 0. PL is the minimum number of nonempty palindrome factors. The claim includes the matching upper bound, hence states the exact value 2k+1.

**Theorem 1.2 (result).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow PL\left(goldenFactor\left(N\left(k\right), 0\right)\right) = 2 \cdot k + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result` (`✓ std3`). ∎

*Resolves.* `Problems/frid-2018-fibonacci-prefix-palindromic-length` (proved) by `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"frid-2018-fibonacci-prefix-palindromic-length","declaration_gid":"D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Acknowledgement.* Anna E. Frid (2018). *Sturmian numeration systems and decompositions to palindromes*. DOI: [10.1016/j.ejc.2018.04.003](https://doi.org/10.1016/j.ejc.2018.04.003). URL: <https://arxiv.org/abs/1710.11553v2>.

*Commentary.*

Equal-width canonical encodings are partitioned into six-bit chunks. Palindrome reflection forces endpoint acceptance. The finite product potential bounds every palindrome edge by one score unit, while the explicit Frid chunk cycle has score 2k+1. Induction along any factorisation gives the lower bound, and symmetric central-word trims give the matching upper bound.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.claim`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result`
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](../../../Digit/GoldenBase4DenseInput.md)
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](../../../Digit/GoldenZeckendorfLanguage.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/ChunkTransport](ChunkTransport.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity](EndpointNecessity.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/FridUpper](FridUpper.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PotentialBound](PotentialBound.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/RankCyclesA](RankCyclesA.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/RankProductA](RankProductA.md)
