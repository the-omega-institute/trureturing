# Signed Potential for Mixed Thue-Morse Factorizations

## Abstract

A signed potential lower bound for mixed factorizations of literal Thue-Morse prefixes.

**Definition 1.1 (Allowed factors).**

$$\forall w \in List\left(Bool\right),\; Allowed\left(w\right) = \left(Palindrome\left(w\right) \lor w = map\left(not, reverse\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ThueMorseSignedCut.Allowed` (`✓ std3`).

*Citation.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Section 6, pallen_classP.tex lines 624–635, defines exchange-reversal antipalindromes and the minimum number of factors that may be either kind. False encodes a and true encodes b. Exchange is Bool.not, and no change of the word or its index origin is made.

**Theorem 1.2 (Adjacent transitions and period doubling).**

$$\forall n \in \mathbb{N},\; transition\left(n\right) = ite\left(\left(u_{\mathrm{pd}}\right)\left(n\right), 0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseSignedCut.transition_period_doubling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent transition is one exactly when neighboring letters differ. Its even and odd recursion identifies it with the complement of the literal period-doubling word. The finite substitution approximant theorem supplies that word's valuation parity. This relationship transfers both reversal symmetries to an ordinary palindrome on adjacent transitions.

**Theorem 1.3 (One allowed factor increases potential by at most one).**

$$\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; i < j \Rightarrow \left(Allowed\left(factor\left(natSub\left(j, i\right), i\right)\right) \Rightarrow signedWeight\left(int\left(j\right)\right) \le signedWeight\left(int\left(i\right)\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseSignedCut.allowed_factor_signed_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here factor(length,start) is the original list of letters t(start+r), with 0 ≤ r < length; j−i uses natural subtraction and i<j excludes the empty factor. Even cuts use the period-doubling palindrome bound. Odd endpoints require extending the Thue-Morse factor by one letter on both sides and combining the two rounded endpoint bounds. An odd length has an even length derivative palindrome, hence length one or three. The three-letter case excludes starts zero and one modulo four. All signedWeight arguments are integer casts of natural endpoints.

**Definition 1.4 (Actual consecutive mixed factorizations).**

$$\forall w \in List\left(Bool\right),\; \forall k \in \mathbb{N},\; MixedFactors\left(w, k\right) = \left(\exists ps \in List\left(List\left(Bool\right)\right),\; flatten\left(ps\right) = w \land \left(length\left(ps\right) = k \land \left(\forall p \in List\left(Bool\right),\; mem\left(p, ps\right) \Rightarrow \left(p \neq nil \land Allowed\left(p\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ThueMorseSignedCut.MixedFactors` (`✓ std3`).

*Citation.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Section 6 asks for the smallest number of factors, each either a palindrome or an antipalindrome. The list of nonempty factors is flattened in its original order and must equal the entire word. This includes a zero-factor decomposition of the empty word.

**Definition 1.5 (Minimum mixed cost).**

$$\forall w \in List\left(Bool\right),\; combinedLength\left(w\right) = min\left(\{k \in \mathbb{N} \mid MixedFactors\left(w, k\right)\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ThueMorseSignedCut.combinedLength` (`✓ std3`).

*Citation.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Section 6, lines 631–635, considers this combined pal-antipal length. Singleton letters give a factorization of every finite word, so the natural minimum exists. The definition uses Nat.find on that existence statement.

**Theorem 1.6 (The prefix cost sandwich).**

$$\forall n \in \mathbb{N},\; signedWeight\left(int\left(n\right)\right) \le combinedLength\left(factor\left(n, 0\right)\right) \land combinedLength\left(factor\left(n, 0\right)\right) \le PL\left(factor\left(n, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseSignedCut.combined_prefix_signed_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split an actual factorization at each successive factor. The cut bound telescopes from signedWeight(0)=0, giving the lower inequality for every factorization and hence its minimum. Every ordinary palindrome factorization is allowed, giving the upper inequality with the existing generic PL. This bound alone does not establish the Section 6 assertion of unbounded prefixes with equal costs: an unbounded attaining family and an ordinary palindromic upper bound on that family are still needed.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.Allowed`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.MixedFactors`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.allowed_factor_signed_cut`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.combinedLength`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.combined_prefix_signed_lower`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSignedCut.transition_period_doubling`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](../Complexity/ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound](PeriodDoubling/SignedCutLowerBound.md)
