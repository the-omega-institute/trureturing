# Four tail colors and inward branch compositions

## Abstract

Four tail colors and inward branch compositions.

**Definition 1.1 (An arbitrary exact decoder).**

Lean statement: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.DecoderContract`

*Formalization.* `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.DecoderContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let t be the reciprocal golden ratio, g = t cubed, I = [-1,t], and X = [-1,1+t]. The five labels are the existing legal three-bit windows three, null, five, two, and twenty-five. Their actual branches are f_a(y) = offset(a) - g y. A scalar coloring Q takes values in five colors, represented by zero through four. One deterministic decoder D takes the current color first and the actual tail color second. It decodes all closed legal branches: three, null, and two have tail domain X; five and twenty-five have tail domain I. The endpoint colors at -t squared, g, t, 2t, and 1+t are respectively zero, one, two, three, and four; the color at -1 is three.

**Definition 1.2 (The four actual tail colors).**

Lean statement: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.tailColor`

*Formalization.* `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.tailColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume the image Q(I) consists exactly of colors zero through three. The restriction tailColor assigns each actual scalar in I its color in the four-element palette. Its embedding into the five-element palette equals Q at that scalar, and each of the four colors is realized.

**Definition 1.3 (The inward color transformations).**

Lean statement: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.branchColor`

*Formalization.* `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.branchColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three inward outer labels are indexed zero, one, and two, denoting three, null, and five. For each tail color, choose an actual tail with that color and apply the corresponding actual branch. Its output color is branchColor. Exact decoding makes every realized tail-color column a bijection between the five current colors and the five labels. Consequently branchColor is independent of the representative: it is the unique current color decoded to the chosen label in that column. For one tail color its three inward outputs are pairwise different.

**Theorem 1.4 (No nontrivial color cycle).**

Lean statement: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coloring and decoder satisfying this contract and four-tail-color condition, choose any inward label a and any finite legal branch word w. Its guard path starts with guard one and ends in either guard; all intermediate branches obey the actual guard transitions. The closed input interval I lies inside either terminal tail domain, and the word scalar maps I into I. Empty words give the identity. Suppose this actual word induces a deterministic four-color map V: tailColor(wordScalar(w,y)) = V(tailColor(y)) for every y in I. Set T = branchColor(a) composed with V. For every color c and every integer m at least one, T iterated m times at c equals c only if T(c) = c. Thus every periodic color is fixed. No continuity, measurability, or finite-component condition is imposed on Q.

Each legal word is affine and continuous. Appending an inward branch gives a closed-interval self-contraction. It has an actual fixed point, whose color is fixed by the induced map T. If a color c were periodic and not fixed, let b and d be the other inward labels. The actual composites f_b v (f_a v) iterated m-1 times and f_d v (f_a v) iterated m-1 times likewise have actual fixed points. Their colors are fixed by the corresponding alternate color maps.

The three fixed-color sets are pairwise disjoint because different outer labels have different outputs in the same tail-color column. They also avoid every color on the alleged nontrivial cycle. In particular c and T(c) are different and avoid all three fixed colors. These five pairwise different colors cannot fit inside the four-element tail palette. This gives the contradiction.

## References

- Truth anchor: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.DecoderContract`
- Truth anchor: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.branchColor`
- Truth anchor: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.result`
- Truth anchor: `D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity.tailColor`
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/OddColorThreeSource](OddColorThreeSource.md)
- Dependency: [D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction](SixCellPositiveMarginObstruction.md)
