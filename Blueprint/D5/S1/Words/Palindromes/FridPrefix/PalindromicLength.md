# Minimum nonempty palindrome factorisation

## Abstract

Minimum nonempty palindrome factorisation

**Definition 1.1 (PalFactors).**

$$\forall A \in Type,\; \forall w \in List\left(A\right),\; \forall k \in \mathbb{N},\; PalFactors\left(w, k\right) = \left(\exists ps \in List\left(List\left(A\right)\right),\; flatten\left(ps\right) = w \land \left(length\left(ps\right) = k \land \left(\forall p \in List\left(A\right),\; mem\left(p, ps\right) \Rightarrow \left(p \neq nil \land Palindrome\left(p\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PalFactors` (`✓ std3`).

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

On printed page 9 Frid writes: “The palindromic length of a finite word u is the minimal number Q of palindromes P₁, . . . , P_Q such that u = P₁ · · · P_Q.” PalFactors(w,k) expresses the displayed concatenation using exactly k nonempty palindrome factors. Deleting empty factors preserves concatenation and cannot increase the minimum. The empty word has a zero-factor decomposition. List.flatten preserves the order of the factors.

**Definition 1.2 (PL).**

$$\forall A \in Type,\; \forall w \in List\left(A\right),\; PL\left(w\right) = min\left(\{k \in \mathbb{N} \mid PalFactors\left(w, k\right)\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PL` (`✓ std3`).

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

On printed page 9 Frid writes: “The palindromic length of a finite word u is the minimal number Q of palindromes P₁, . . . , P_Q such that u = P₁ · · · P_Q.” PL is this minimum, with empty factors removed. A factorisation into singleton letters makes the set nonempty; the definition uses Nat.find on that existence proof. The minimum for the empty word is zero.

**Theorem 1.3 (pl_one_letter_lipschitz).**

$$\forall A \in Type,\; \forall w \in List\left(A\right),\; \forall a \in A,\; abs\left(int\left(PL\left(append\left(w, singleton\left(a\right)\right)\right)\right) - int\left(PL\left(w\right)\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.pl_one_letter_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All lengths in the absolute difference are cast to integers. Appending one singleton supplies one inequality. For the reverse inequality, removing the last letter of a palindrome splits its remainder into a shorter central palindrome and at most one singleton.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PL`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.PalFactors`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.pl_one_letter_lipschitz`
