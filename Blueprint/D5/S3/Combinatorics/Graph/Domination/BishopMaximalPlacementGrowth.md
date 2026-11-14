# Growth of maximal bishop placements

## Abstract

Growth of maximal bishop placements

**Definition 1.1 (The fixed-coordinate bishop graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.bishopGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.bishopGraph` (`✓ std3`).

*Citation.* Paolo Bonzini; The OEIS Foundation Inc. (2008). *OEIS A146304: inclusion-maximal nonattacking bishop placements*. URL: <https://oeis.org/A146304>.

*Commentary.*

The board is Fin n times Fin n. A square (x,y) has integer difference x-y and integer sum x+y. Distinct squares attack precisely when their differences or their sums agree. Placements are unlabelled subsets of this board, without identifying rotations or reflections.

**Definition 1.2 (Inclusion-maximal placements).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.count`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.count` (`✓ std3`).

*Citation.* Paolo Bonzini; The OEIS Foundation Inc. (2008). *OEIS A146304: inclusion-maximal nonattacking bishop placements*. URL: <https://oeis.org/A146304>.

*Commentary.*

The count is the cardinality of all independent subsets maximal under inclusion, at every size. Maximal means that another bishop cannot be added; it does not mean maximum cardinality. The total convention at n=0 is outside the OEIS offset one.

**Definition 1.3 (The complete asymptotic assertion).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\exists (C : \mathbb{R}), (0 < C) \land (\exists (N : \mathbb{N}), (1 \le N) \land (\forall (n : \mathbb{N}), (N \le n) \Rightarrow (\operatorname{count}\left(n\right) \le C \cdot (n)^{n - 1}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.claim` (`✓ std3`).

*Citation.* Paolo Bonzini; The OEIS Foundation Inc. (2008). *OEIS A146304: inclusion-maximal nonattacking bishop placements*. URL: <https://oeis.org/A146304>.

*Commentary.*

The assertion is the existence of a positive real C and a natural N at least one such that a(n) is at most C times n^(n-1) for every natural n at least N. Both the constant and the cutoff remain unrestricted.

**Theorem 1.4 (The physical upper bound).**

$$\forall (n : \mathbb{N}), (2 \le n) \Rightarrow (\forall (M : \operatorname{Placement}\left(n\right)), \operatorname{card}\left(\operatorname{val}\left(M\right)\right) \le 2 \cdot n - 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.physical_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, every counted maximal placement has at most 2n-2 bishops. Difference diagonals give an injective label map into 2n-1 possibilities. Both extreme diagonals are single corners with the same sum, so independence excludes at least one extreme. Removing that label gives the upper bound. The one-square board has its unique singleton maximal placement; a zero cap is not imposed there.

**Theorem 1.5 (The source cap preserves the native count).**

$$\forall (n : \mathbb{N}), \operatorname{card}\left(\operatorname{sourceFamily}\left(n\right)\right) = \operatorname{count}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.source_family_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering the native maximal placements by the physical cap for n at least two leaves their cardinality unchanged. The implication is vacuous at n=1, so the source boundary is preserved.

**Theorem 1.6 (Many distinct maximal completions).**

$$\forall (m : \mathbb{N}), (m)^{6 \cdot m} \le \operatorname{count}\left(4 \cdot m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.count_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, a(4m+1) is at least m^(6m). Within each diagonal parity, list signed difference lines by increasing length and select the fixed 3m lines at one-based positions m+1 through 4m. The jth selected line has at least m+j-1 squares, and each legal prefix leaves at least m choices. The two colors have disjoint sum labels as well as disjoint difference labels, so their choices combine on the same board. Every seed extends to an inclusion-maximal independent set by the finite maximal-extension theorem. Every selected line is already occupied. Independence prevents the extension from adding another square there, so restriction to the selected lines recovers the seed. Equivalently, a completed placement determines the chosen square on every prescribed difference line. Thus the map from the actual unordered seeds into maximal placements is injective.

**Theorem 1.7 (Exponential divergence of the ratio).**

$$\forall (m : \mathbb{N}), (50 \le m) \Rightarrow ((4)^{m} \cdot (4 \cdot m + 1)^{4 \cdot m} \le \operatorname{count}\left(4 \cdot m + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.ratio_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least 50, 4^m times (4m+1)^(4m) is at most a(4m+1). Indeed 4m+1 is at most 5m, and m squared is at least 2500, giving 4 times (5m)^4 at most m^6. Raising this inequality to m and using the seed bound proves the multiplied ratio estimate with positive denominators.

**Theorem 1.8 (Failure of the Big-O bound).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete asymptotic assertion is false. Given any positive real C and any cutoff N, choose m at least 50 and N with 4^m greater than C. Then n=4m+1 is beyond the cutoff and the ratio estimate gives a(n) greater than C times n^(n-1). This is an unbounded family of strict violations, independent of any finite table.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.bishopGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.count_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.physical_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.ratio_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.source_family_card`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount](FiniteLinePrefixCount.md)
- Dependency: [D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction](../../../Geometry/FiniteGraphSubgraphSuspensionConstruction.md)
