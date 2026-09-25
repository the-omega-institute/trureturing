# PositivePairFiltration

## Abstract

The full indexed positive-pair family has the required cutoff filtration.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Definition 1.1 (Full recursive choice index).**

$$PositivePairIndex$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.PositivePairIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.

**Definition 1.2 (Actual recursive positive pairs).**

$$positivePairWords$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).

**Definition 1.3 (Actual Magnus cutoff).**

$$cutoffMagnus$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.cutoffMagnus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.

**Definition 1.4 (Actual positive-pair Magnus ratio).**

$$positivePairRatio$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).

**Theorem 1.5 (Full indexed family agrees below its level).**

$$fullpositivePairratiofiltration$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.full_positivePair_ratio_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family.

**Theorem 1.6 (Cancellation of actual cutoff Magnus factors).**

$$cutoffMagnuscancellation$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.cutoffMagnus_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

The empty-word coefficient of every actual Magnus image is one. Finite geometric inverses in the truncated split-convolution algebra therefore cancel common left factors and equal right factors in appended positive words at every cutoff.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.PositivePairIndex`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.cutoffMagnus`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.cutoffMagnus_cancellation`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.full_positivePair_ratio_filtration`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairRatio`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairWords`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients](MagnusWordCoefficients.md)
