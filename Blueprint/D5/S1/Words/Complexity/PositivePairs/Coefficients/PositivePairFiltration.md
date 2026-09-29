# PositivePairFiltration

## Abstract

The full indexed positive-pair family has the required cutoff filtration.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Definition 1.1 (Full recursive choice index).**

$$\forall A,r,\operatorname{PositivePairIndex}\left(A, r\right) = \operatorname{functions}\left(\operatorname{Fin}\left(r\right), A\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.PositivePairIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.

**Definition 1.2 (Actual recursive positive pairs).**

$$(\forall index0,\operatorname{positivePairWords}\left(0, index0\right) = \operatorname{pair}\left(empty, empty\right))\land(\forall index1,\operatorname{positivePairWords}\left(1, index1\right) = \operatorname{pair}\left(\operatorname{singleton}\left(\operatorname{apply}\left(index1, 0\right)\right), empty\right))\land\forall r,index,\operatorname{positivePairWords}\left(r + 2, index\right) = \operatorname{pair}\left(\operatorname{append}\left(\operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{FinInit}\left(index\right)\right)\right), \operatorname{singleton}\left(\operatorname{apply}\left(index, \operatorname{FinLast}\left(r + 1\right)\right)\right), \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{FinInit}\left(index\right)\right)\right)\right), \operatorname{append}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{FinInit}\left(index\right)\right)\right), \operatorname{singleton}\left(\operatorname{apply}\left(index, \operatorname{FinLast}\left(r + 1\right)\right)\right), \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{FinInit}\left(index\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).

**Definition 1.3 (Actual Magnus cutoff).**

$$\forall r,source,\operatorname{cutoffMagnus}\left(r, source\right) = \operatorname{cutoffRestriction}\left(r, \operatorname{toRationalWordPolynomial}\left(\operatorname{magnusPolynomial}\left(source\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.cutoffMagnus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.

**Definition 1.4 (Actual positive-pair Magnus ratio).**

$$\forall cutoff,r,index,\operatorname{positivePairRatio}\left(cutoff, r, index\right) = \operatorname{cutoffMul}\left(cutoff, \operatorname{cutoffMagnus}\left(cutoff, \operatorname{left}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right), \operatorname{cutoffGeometricInverse}\left(cutoff, \operatorname{cutoffMagnus}\left(cutoff, \operatorname{right}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right) - \operatorname{cutoffOne}\left(cutoff\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.positivePairRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).

**Theorem 1.5 (Full indexed family agrees below its level).**

$$\forall cutoff,r,index,\operatorname{VanishesBelow}\left(cutoff, r, \operatorname{cutoffMagnus}\left(cutoff, \operatorname{left}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right) - \operatorname{cutoffMagnus}\left(cutoff, \operatorname{right}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right)\right)\land\operatorname{VanishesBelow}\left(cutoff, r, \operatorname{positivePairRatio}\left(cutoff, r, index\right) - \operatorname{cutoffOne}\left(cutoff\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration.full_positivePair_ratio_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family.

**Theorem 1.6 (Cancellation of actual cutoff Magnus factors).**

$$(\forall r,prefix,left,right,\operatorname{cutoffMagnus}\left(r, \operatorname{append}\left(prefix, left\right)\right) = \operatorname{cutoffMagnus}\left(r, \operatorname{append}\left(prefix, right\right)\right)\Rightarrow\operatorname{cutoffMagnus}\left(r, left\right) = \operatorname{cutoffMagnus}\left(r, right\right))\land(\forall r,left,right,suffixLeft,suffixRight,\operatorname{cutoffMagnus}\left(r, suffixLeft\right) = \operatorname{cutoffMagnus}\left(r, suffixRight\right)\land\operatorname{cutoffMagnus}\left(r, \operatorname{append}\left(left, suffixLeft\right)\right) = \operatorname{cutoffMagnus}\left(r, \operatorname{append}\left(right, suffixRight\right)\right)\Rightarrow\operatorname{cutoffMagnus}\left(r, left\right) = \operatorname{cutoffMagnus}\left(r, right\right))$$

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
