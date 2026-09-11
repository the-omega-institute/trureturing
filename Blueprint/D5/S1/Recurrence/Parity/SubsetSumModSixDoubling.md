# Subset Sums Modulo Six

## Abstract

Subset complementation and a three-period symmetry prove the A068012 doubling conjecture.

OEIS A068012 counts subsets of the interval from one to n whose sum is zero modulo six. David A. Corneth's September 13, 2025 comment conjectures doubling when n exceeds two and three does not divide n-1. The argument below proves that assertion for every such n.

Indices n and m are natural numbers. Residues r lie in ZMod 6, and iota6 denotes the natural-number map into that ring. Cardinalities are natural numbers; subtraction of indices is natural subtraction. The powerset consists of all finite subsets, including the empty set.

**Definition 1.1 (The residue counts).**

$$\forall n \in \mathbb{N}, \forall r \in \operatorname{ZMod}\left(6\right), \operatorname{C}\left(n, r\right) = \operatorname{card}\left(\{ S \in \operatorname{powerset}\left(\operatorname{Icc}\left(1, n\right)\right) \mid \sum_{x \in S} \operatorname{iota6}\left(x\right) = r \}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.C` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Antti Karttunen; David A. Corneth (2025). *OEIS A068012 subset sum doubling conjecture*. URL: <https://oeis.org/A068012>.

*Commentary.*

Each subset contributes once, in the residue of its element sum. Using the powerset makes this the subset count in the OEIS definition.

**Definition 1.2 (The zero residue).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{C}\left(n, 0\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.a` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Antti Karttunen; David A. Corneth (2025). *OEIS A068012 subset sum doubling conjecture*. URL: <https://oeis.org/A068012>.

*Commentary.*

The sequence is the zero-residue coordinate, including index zero.

**Lemma 1.3 (Splitting at the last element).**

$$\forall n \in \mathbb{N}, \forall r \in \operatorname{ZMod}\left(6\right), \operatorname{C}\left(n + 1, r\right) = \operatorname{C}\left(n, r\right) + \operatorname{C}\left(n, r - \operatorname{iota6}\left(n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Antti Karttunen; David A. Corneth (2025). *OEIS A068012 subset sum doubling conjecture*. URL: <https://oeis.org/A068012>.

*Commentary.*

A subset either omits n+1, or is obtained by adjoining n+1 to a unique subset of the preceding interval. In the second case its preceding sum must be r-iota6(n+1). Mathlib's sum_powerset_insert gives this partition, applied to the indicator of the prescribed residue.

**Lemma 1.4 (Three-periodic residue counts).**

$$\forall m \in \mathbb{N}, 3 \le m \implies \forall r \in \operatorname{ZMod}\left(6\right), \operatorname{C}\left(m, r\right) = \operatorname{C}\left(m, r + 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_three_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three, split off element three from the interval. The two contributions to residue r have preceding sums r and r-3. Since -3=3 modulo six, shifting r by three exchanges these terms. The threshold ensures that the element being split off is present.

**Lemma 1.5 (Equality in the residue-one phase).**

$$\forall m \in \mathbb{N}, 4 \le m \implies m \bmod 3 = 1 \implies \operatorname{C}\left(m, 0\right) = \operatorname{C}\left(m, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_zero_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complementation is a bijection on the subsets of the interval. If its total sum is T, the bijection sends a sum r to T-r. Induction on m gives 2T=m(m+1). When m is one modulo three, this forces T to be one or four modulo six. Complementation therefore identifies the zero count with one of those two counts, and three-periodicity identifies both with the count at one.

**Theorem 1.6 (The doubling conjecture).**

$$\forall n \in \mathbb{N}, 2 < n \implies \neg (3 \mid n - 1) \implies \operatorname{a}\left(n\right) = 2 \times \operatorname{a}\left(n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.subset_sum_mod_six_doubling` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a068012-subset-sum-doubling` (proved) by `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.subset_sum_mod_six_doubling`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a068012-subset-sum-doubling","declaration_gid":"D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.subset_sum_mod_six_doubling","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Antti Karttunen; David A. Corneth (2025). *OEIS A068012 subset sum doubling conjecture*. URL: <https://oeis.org/A068012>.

*Commentary.*

Put m=n-1. The recurrence reduces doubling to equality of the counts at -n and zero. The allowed residues of m modulo six are 1, 2, 4, and 5. The corresponding residues of -n are 4, 3, 1, and 0. Three-periodicity and the residue-one equality handle all four. The boundary n=3 is checked directly within the proof. The result has no upper bound on n.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.C`
- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.a`
- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_succ`
- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_three_periodic`
- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.count_zero_eq_one`
- Truth anchor: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.subset_sum_mod_six_doubling`
