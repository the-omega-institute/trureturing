# Odd-Index Zeckendorf Freedom

## Abstract

Odd natural indices free every subset from adjacency and give the full powerset count.

**Theorem 1.1 (Odd-index subsets are nonadjacent and exactly counted).**

$$\forall I\subset_{\mathrm{fin}}\mathbb{N},\ (\forall n\in I,n\ \text{ odd}) \Rightarrow \left((\forall S\subseteq I,\forall n\in S,\neg(n+1\in S)) \land \lvert(\operatorname{powerset}(I)\setminus\{\emptyset\})\rvert=2^{\lvert I\rvert}-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/OddIndexFreedom.odd_index_subsets_are_admissible_and_counted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any finite set of odd natural indices. Every subset S of I inherits oddness, while the successor of an odd index is even. Thus S cannot contain both n and n+1, which is exactly the local Zeckendorf nonadjacency condition used by the source atom.

Pinned Mathlib was searched before proving. No combined theorem was found. The proof directly reuses Nat.Odd.add_one and Nat.not_even_iff_odd for the parity exclusion, then Finset.card_powerset and Finset.card_erase_of_mem for the exact nonempty-subset count. When the index set has cardinality twelve, the formula evaluates to 4095.

This closes only the odd-index freedom and exact-count assertion in the first paragraph of source remark 27.192. The cone-series expansion, its numerical approximations, the missing second family, and the longer research roadmap in the same atom are not asserted here.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/OddIndexFreedom.odd_index_subsets_are_admissible_and_counted`
