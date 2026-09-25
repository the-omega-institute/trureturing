# PositivePairLeadingCoefficients

## Abstract

Successor positive pairs have the actual leading commutator coefficients.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Theorem 1.1 (Successor difference is a commutator).**

$$\forall r,index, \operatorname{cutoffMagnus}\left(r + 2, \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 2, index\right)\right)\right) - \operatorname{cutoffMagnus}\left(r + 2, \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 2, index\right)\right)\right) = \operatorname{cutoffMul}\left(r + 2, \operatorname{cutoffMagnus}\left(r + 2, \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) - \operatorname{cutoffMagnus}\left(r + 2, \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right), \operatorname{cutoffRestriction}\left(r + 2, \operatorname{toRationalWordPolynomial}\left(\operatorname{wordAbelianization}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) + \operatorname{wordMonomial}\left(\operatorname{singleton}\left(\operatorname{atLast}\left(index\right)\right)\right)\right)\right)\right) - \operatorname{cutoffMul}\left(r + 2, \operatorname{cutoffRestriction}\left(r + 2, \operatorname{toRationalWordPolynomial}\left(\operatorname{wordAbelianization}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) + \operatorname{wordMonomial}\left(\operatorname{singleton}\left(\operatorname{atLast}\left(index\right)\right)\right)\right)\right), \operatorname{cutoffMagnus}\left(r + 2, \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) - \operatorname{cutoffMagnus}\left(r + 2, \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients.full_positivePair_successor_leading_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A with decidable equality and index at level r+2, let c be the preceding actual cutoff-Magnus difference and x the rationalized abelianization of the previous right word plus X_a. The successor Magnus difference equals cutoffMul c x - cutoffMul x c in cutoff r+2.

**Theorem 1.2 (The ratio has the same leading commutator).**

$$\forall r,index, \operatorname{positivePairRatio}\left(r + 2, r + 2, index\right) - \operatorname{cutoffOne}\left(r + 2\right) = \operatorname{cutoffMul}\left(r + 2, \operatorname{cutoffMagnus}\left(r + 2, \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) - \operatorname{cutoffMagnus}\left(r + 2, \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right), \operatorname{cutoffRestriction}\left(r + 2, \operatorname{toRationalWordPolynomial}\left(\operatorname{wordAbelianization}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) + \operatorname{wordMonomial}\left(\operatorname{singleton}\left(\operatorname{atLast}\left(index\right)\right)\right)\right)\right)\right) - \operatorname{cutoffMul}\left(r + 2, \operatorname{cutoffRestriction}\left(r + 2, \operatorname{toRationalWordPolynomial}\left(\operatorname{wordAbelianization}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) + \operatorname{wordMonomial}\left(\operatorname{singleton}\left(\operatorname{atLast}\left(index\right)\right)\right)\right)\right), \operatorname{cutoffMagnus}\left(r + 2, \operatorname{left}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right) - \operatorname{cutoffMagnus}\left(r + 2, \operatorname{right}\left(\operatorname{positivePairWords}\left(r + 1, \operatorname{init}\left(index\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients.full_positivePair_successor_ratio_leading_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Under the same hypotheses and definitions, positivePairRatio at level and cutoff r+2 minus cutoffOne equals cutoffMul c x - cutoffMul x c.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients.full_positivePair_successor_leading_bracket`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients.full_positivePair_successor_ratio_leading_bracket`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration](PositivePairFiltration.md)
