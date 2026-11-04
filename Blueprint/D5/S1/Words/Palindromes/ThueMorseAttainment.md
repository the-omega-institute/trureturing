# Attaining Thue-Morse Prefixes

## Abstract

An explicit unbounded family of literal Thue-Morse prefixes has equal ordinary and mixed palindromic costs.

**Definition 1.1 (The positive prefix family).**

$$attainingLength\left(0\right) = 1 \land \left(\forall m \in \mathbb{N},\; attainingLength\left(m + 1\right) = natSub\left(4 \cdot attainingLength\left(m\right), 1\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ThueMorseAttainment.attainingLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Index zero denotes n_1=1. Every next positive length is four times its predecessor minus one. NatSub is truncated natural subtraction. The signed expansion is the least-significant-first list obtained from [1] by prepending [-1,0] at each step; the existing nonadjacent signed-digit minimality theorem gives its weight m+1. No finite table is used as proof.

**Theorem 1.2 (Exact attainment on the same literal family).**

$$\forall m \in \mathbb{N},\; signedWeight\left(int\left(attainingLength\left(m\right)\right)\right) = m + 1 \land \left(combinedLength\left(factor\left(attainingLength\left(m\right), 0\right)\right) = m + 1 \land PL\left(factor\left(attainingLength\left(m\right), 0\right)\right) = m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The substitution tau sends b to [b,not b,not b,b]. Reversing a substituted word commutes with substitution, so images of nonempty palindrome factors remain nonempty palindromes. Applying it to every factor gives PL(tau(w)) <= PL(w). The original even/odd Thue-Morse recurrences identify tau(t[0:n)) with t[0:4n). The existing ordinary-PL one-letter Lipschitz theorem then gives PL(t[0:4n-1)) <= PL(t[0:n))+1. Induction gives the ordinary upper bound on this exact family. The universal literal-cut lower bound sandwiches the actual mixed minimum between signed weight m+1 and ordinary PL m+1. The new combinatorial bridge is the substitution transport of an actual factorization; the signed-digit and deletion suppliers are reused. These are StageA mathematical source candidates; independent admission and source-binding review remain separate.

**Theorem 1.3 (The whole quantified Section 6 assertion).**

$$\forall K \in \mathbb{N},\; 1 \le K \Rightarrow \left(\exists n \in \mathbb{N},\; 1 \le n \land \left(combinedLength\left(factor\left(n, 0\right)\right) = PL\left(factor\left(n, 0\right)\right) \land K \le PL\left(factor\left(n, 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AKMP Section 6 final paragraph and Table 2 motivate this exact quantified assertion. Choose n=attainingLength(K); both minima equal K+1. The word is Complexity.factor(n,0), with false=a and true=b. Ordinary PL minimizes nonempty palindrome factors; combinedLength minimizes nonempty factors that are palindromes or exchange-reversal antipalindromes. No derivative cost, parity proxy, empty factor or restricted window replaces these definitions. The argument is repository-derived, rather than attributed to the article. Worldwide openness and external originality have not been verified. The pre-existing signed-cut binding exceptions are disclosed at issue 26539; this source does not certify freezing, independent admission, or publication.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.attainingLength`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits](PeriodDoubling/NonadjacentSignedDigits.md)
- Dependency: [D5/S1/Words/Palindromes/ThueMorseSignedCut](ThueMorseSignedCut.md)
