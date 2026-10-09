# Paired Dyadic Removals

## Abstract

Two removals of the same dyadic amount from a heap deeper than the unique minimum produce exactly two minimum-depth heaps.

**Theorem 1.1 (The intermediate heap and its second remainder).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \forall h \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, k + 1\right) \land \left(\operatorname{countAt}\left(P, k + 1\right) = 1 \land \left(\operatorname{mem}\left(h, P\right) \land k + 1 < \operatorname{valuation}\left(h\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{erase}\left(\operatorname{successor}\left(P, h, 2^{k}\right), h - 2^{k}\right) = \operatorname{erase}\left(P, h\right) \land \left(\left(\forall x \in \mathrm{Nat},\; \operatorname{mem}\left(x, \operatorname{erase}\left(\operatorname{successor}\left(P, h, 2^{k}\right), h - 2^{k}\right)\right) \Rightarrow k + 1 \le \operatorname{valuation}\left(x\right)\right) \land \left(\operatorname{countAt}\left(\operatorname{erase}\left(\operatorname{successor}\left(P, h, 2^{k}\right), h - 2^{k}\right), k + 1\right) = 1 \land \left(0 < h - 2^{k} - 2^{k} \land \operatorname{valuation}\left(h - 2^{k} - 2^{k}\right) = k + 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmallSupport.paired_pivot_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the first removal, erasing the new heap recovers the unchanged heaps. They retain exactly one heap of depth k plus one. The second removal leaves a positive heap of that same depth.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmallSupport.paired_pivot_structure`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundOutcome](DivisorNimBoundOutcome.md)
