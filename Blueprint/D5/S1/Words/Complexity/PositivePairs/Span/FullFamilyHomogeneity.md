# FullFamilyHomogeneity

## Abstract

Actual full-family leading differences are homogeneous in their true degree.

The classical Lyndon bracket basis motivates the target directions. The new content here is realizability by the complete family of actual recursively generated positive-word pairs, without quotienting duplicate indices.

**Definition 1.1 (Rational homogeneous polynomials).**

$$\forall p,r, \operatorname{RationalHomogeneous}\left(p, r\right)\iff\forall w\in\operatorname{support}\left(p\right),\operatorname{length}\left(w\right) = r$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.RationalHomogeneous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

RationalHomogeneous p r means every free word in the coefficient support of p has length r.

**Definition 1.2 (An actual indexed leading difference).**

$$\forall r,index, \operatorname{actualLeadingDifference}\left(r, index\right) = \operatorname{cutoffLift}\left(r, \operatorname{cutoffMagnus}\left(r, \operatorname{left}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right) - \operatorname{cutoffMagnus}\left(r, \operatorname{right}\left(\operatorname{positivePairWords}\left(r, index\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.actualLeadingDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, level r, and a PositivePairIndex, actualLeadingDifference lifts the complete degree-r cutoff difference cutoffMagnus(u)-cutoffMagnus(v) to the full rational word algebra.

**Definition 1.3 (Span of the full actual family).**

$$\forall A,r, \operatorname{fullFamilySpan}\left(A, r\right) = \operatorname{spanQ}\left(\operatorname{range}\left(index, \operatorname{PositivePairIndex}\left(A, r\right), \operatorname{actualLeadingDifference}\left(r, index\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.fullFamilySpan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

fullFamilySpan A r is the Q-submodule spanned by the range of actualLeadingDifference over every PositivePairIndex A r.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.RationalHomogeneous`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.actualLeadingDifference`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity.fullFamilySpan`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients](../Coefficients/PositivePairLeadingCoefficients.md)
