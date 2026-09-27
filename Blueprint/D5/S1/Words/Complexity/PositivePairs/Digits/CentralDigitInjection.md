# CentralDigitInjection

## Abstract

Multi-scale central digits are injective with exact length control.

This module combines the private central-coefficient identities with linear independence of the selected actual directions. Its public theorem packages lower-degree agreement, the exact degree-r coordinate formula, injectivity, digit-array cardinality, nonempty equal-length pairs, and exact word length.

**Theorem 1.1 (Full central-digit system from actual pairs).**

$$\forall A,r,t,2\leq r\Rightarrow\operatorname{LinearIndependent}\left(Q, \operatorname{lambda}\left(direction, \operatorname{actualLeadingDifference}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right)\land(\forall direction\in\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right),(\operatorname{left}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\neq empty\land \operatorname{right}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\neq empty\land\operatorname{length}\left(\operatorname{left}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right) = \operatorname{length}\left(\operatorname{right}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right)))\land(\forall digits,pattern,\operatorname{length}\left(pattern\right)< r\Rightarrow\operatorname{scatteredCount}\left(pattern, \operatorname{multiScaleWord}\left(r, t, digits\right)\right) = \operatorname{scatteredCount}\left(pattern, \operatorname{referenceWord}\left(r, t\right)\right))\land(\forall digits,pattern,\operatorname{length}\left(pattern\right) = r\Rightarrow\operatorname{castQ}\left(\operatorname{scatteredCount}\left(pattern, \operatorname{multiScaleWord}\left(r, t, digits\right)\right)\right) - \operatorname{castQ}\left(\operatorname{scatteredCount}\left(pattern, \operatorname{referenceWord}\left(r, t\right)\right)\right) = \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right), \operatorname{lambda}\left(direction, \operatorname{castQ}\left(\operatorname{digitValue}\left(r, t, digits, direction\right)\right) \cdot \operatorname{coeff}\left(\operatorname{actualLeadingDifference}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right), \operatorname{ofList}\left(pattern\right)\right)\right)\right))\land\operatorname{Injective}\left(\operatorname{lambda}\left(digits, \operatorname{cutoffMagnus}\left(r, \operatorname{multiScaleWord}\left(r, t, digits\right)\right)\right)\right)\land\operatorname{card}\left(\operatorname{DigitArray}\left(A, r, t\right)\right) = \operatorname{pow}\left(\operatorname{digitBase}\left(r\right), t \cdot \operatorname{actualLyndonCount}\left(A, r\right)\right)\land\forall digits,\operatorname{length}\left(\operatorname{multiScaleWord}\left(r, t, digits\right)\right) = \operatorname{baseLength}\left(A, r\right) \cdot \left(\operatorname{pow}\left(2, t\right) - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection.actual_positivePair_multiScale_central_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, r,t:N, and 2<=r, the selected actual leading differences are linearly independent; every selected pair has two nonempty equal-length words; every digit word agrees with referenceWord below degree r; each degree-r coefficient difference is the indicated sum of digitValue times actualLeadingDifference; the cutoffMagnus digit map is injective; the digit-array cardinality is (2^r)^(t*actualLyndonCount A r); and every digit word has length baseLength A r*(2^t-1).

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection.actual_positivePair_multiScale_central_digits`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitData](CentralDigitData.md)
