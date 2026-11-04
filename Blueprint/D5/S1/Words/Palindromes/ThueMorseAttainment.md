# Attaining Thue-Morse Prefixes

## Abstract

An explicit unbounded family of literal Thue-Morse prefixes has equal ordinary and mixed palindromic costs.

**Definition 1.1 (The positive prefix family).**

$$attainingLength\left(0\right) = 1 \land \left(\forall m \in \mathbb{N},\; attainingLength\left(m + 1\right) = natSub\left(4 \cdot attainingLength\left(m\right), 1\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ThueMorseAttainment.attainingLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Index zero denotes n_1=1. Every next positive length is four times its predecessor minus one. NatSub is truncated natural subtraction. The signed expansion is the least-significant-first list obtained from [1] by prepending [-1,0] at each step; the existing nonadjacent signed-digit minimality theorem gives its weight m+1.

**Theorem 1.2 (Exact attainment on the same literal family).**

$$\forall m \in \mathbb{N},\; signedWeight\left(int\left(attainingLength\left(m\right)\right)\right) = m + 1 \land \left(combinedLength\left(factor\left(attainingLength\left(m\right), 0\right)\right) = m + 1 \land PL\left(factor\left(attainingLength\left(m\right), 0\right)\right) = m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

The substitution tau sends b to [b,not b,not b,b]. Reversing a substituted word commutes with substitution, so images of nonempty palindrome factors remain nonempty palindromes. Applying it to every factor gives PL(tau(w)) <= PL(w). The original even/odd Thue-Morse recurrences identify tau(t[0:n)) with t[0:4n). The existing ordinary-PL one-letter Lipschitz theorem then gives PL(t[0:4n-1)) <= PL(t[0:n))+1. Induction gives the ordinary upper bound on this exact family. The universal literal-cut lower bound sandwiches the actual mixed minimum between signed weight m+1 and ordinary PL m+1. Transporting an actual factorization under the substitution supplies the ordinary upper bound.

**Theorem 1.3 (The whole quantified Section 6 assertion).**

$$\forall K \in \mathbb{N},\; 1 \le K \Rightarrow \left(\exists n \in \mathbb{N},\; 1 \le n \land \left(combinedLength\left(factor\left(n, 0\right)\right) = PL\left(factor\left(n, 0\right)\right) \land K \le PL\left(factor\left(n, 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost` (`✓ std3`). ∎

*Resolves.* `Problems/ambroz-kadlec-masakova-pelantova-2019-thue-morse-equal-cost` (proved) by `D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ambroz-kadlec-masakova-pelantova-2019-thue-morse-equal-cost","declaration_gid":"D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

The final paragraph of Section 6 and Table 2 motivate this exact quantified assertion. Choose n=attainingLength(K); both minima equal K+1. The word is Complexity.factor(n,0), with false=a and true=b. Ordinary PL minimizes nonempty palindrome factors; combinedLength minimizes nonempty factors that are palindromes or exchange-reversal antipalindromes. No derivative cost, parity proxy, empty factor or restricted window replaces these definitions. The substitution and signed-cut arguments establish the motivating assertion.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.attainingLength`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits](PeriodDoubling/NonadjacentSignedDigits.md)
- Dependency: [D5/S1/Words/Palindromes/ThueMorseSignedCut](ThueMorseSignedCut.md)
