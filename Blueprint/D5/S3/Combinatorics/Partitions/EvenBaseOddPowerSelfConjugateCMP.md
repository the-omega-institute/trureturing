# The least odd exponent for a self-conjugate CMP at an even base

## Abstract

The least odd exponent admitting a self-conjugate CMP at an even base, as asked in Question 5.12 of Dietz, Flowers and Lockard.

**Definition 1.1 (The published diagram).**

$$publishedDiagram:\mathbb{N}\to\operatorname{YoungDiagram}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.publishedDiagram` (`✓ std3`).

*Citation.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

For each j from zero through m, take the rectangle with height m to the power j and width m to the power m − j, with its upper left cell at the origin. The diagram is the union of these rectangles. Its row lengths and multiplicities are those of Flowers and Lockard, Lemma 4.2.

**Theorem 1.2 (Minimum odd exponent).**

$$\forall m \in \mathbb{N},\; ((2 \le m) \Rightarrow ((\operatorname{Even}\left(m\right)) \Rightarrow (\operatorname{IsLeast}\left(\{e \in \mathbb{N}\mid\operatorname{Odd}\left(e\right) \land \left(\exists mu \in \operatorname{YoungDiagram},\; (\operatorname{card}\left(mu\right) = m^{e} \land \left(\operatorname{IsCMP}\left(m, mu\right) \land \operatorname{transpose}\left(mu\right) = mu\right))\right)\}, m + 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Write N for the number of cells and L for the first row length. The first row and column meet in one cell, and the diagram lies inside an L by L square. Thus 2L − 1 ≤ N ≤ L². If N = mᵉ and L = mᴷ, with e odd, these bounds give 0 < 2K − e ≤ e − 2. The square congruence for N − (2L − 1), together with the first-order expansion of the two powers modulo (m − 1)², shows that m − 1 divides 2K − e. Hence e ≥ m + 1, including at base 2 and for the candidate e = 1.

The attaining diagram is the union of rectangles with height mʲ and width m to the power m − j, for j = 0 through m. Transposition swaps the rectangles indexed by j and m − j. The top row has width mᵐ. For each j from 1 through m, the rows with zero-based index from m to the power j − 1 inclusive up to mʲ exclusive have width m to the power m − j. These are the multiplicities in Flowers and Lockard, Lemma 4.2, cited in Discussion 5.11 of the source. Each of those m bands has mᵐ − m to the power m − 1 cells, so the exact area is m to the power m + 1. Evenness of m makes that exponent odd.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.publishedDiagram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.result`
- Dependency: [D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP](OddPowerSelfConjugateCMP.md)
