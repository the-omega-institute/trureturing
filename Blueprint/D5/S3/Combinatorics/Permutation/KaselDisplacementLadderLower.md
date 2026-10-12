# The Kasel Displacement Lower Bound

## Abstract

Every valid normalized Kasel scheme has distinguished displacement at least m minus two.

**Theorem 1.1 (A distinguished value attains the lower bound).**

$$\forall m \in \mathbb {N},\; 2 \le m \Rightarrow \left(\forall s \in \mathbb {N} \to \mathbb {N}, r \in \mathbb {N} \to \mathbb {N},\; (\operatorname{Valid}\left(\operatorname{SA}\left(m\right), s, r\right) \land \operatorname{Normalized}\left(\operatorname{SA}\left(m\right), s\right)) \Rightarrow \left(\exists v \in distinguished,\; \left\lfloor\frac{\operatorname{block}\left(v\right)}{2}\right\rfloor + m - 2 \le \operatorname{s}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower.lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least two and every pair of natural-valued functions s and r forming a valid normalized scheme on SA m, some distinguished value v has stage at least its block index divided by two plus m minus two. At m equal to two, take v equal to three and apply normalization. For m at least three, suppose both fifteen and sixteen have stage below m. Put M equal to twice four to the power m minus one. Every value in (M, 2M] has block index 2m and hence stage at least m. Counting predecessors in the strict total concatenation order gives an injective natural-valued rank that preserves and reflects that order. Validity excludes both monotone arithmetic progressions in this block. Each attack from fifteen or sixteen forces its guard before its bottom, since the attack itself precedes the bottom and validity forbids a monotone progression. These ranks form an Erdos-Graham order gadget at scale M at least thirty-two. The frozen all-scale impossibility theorem gives a contradiction. Thus fifteen or sixteen has stage at least m, which is exactly the required lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower.lower_bound`
- Dependency: [D5/S3/Combinatorics/ErdosGrahamOrderGadget](../ErdosGrahamOrderGadget.md)
- Dependency: [D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs](KaselDisplacementLadderDefs.md)
