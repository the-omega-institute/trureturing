# CentralDigitInjection

## Abstract

Multi-scale central digits are injective with exact length control.

This module combines the private central-coefficient identities with linear independence of the selected actual directions. Its public theorem packages lower-degree agreement, the exact degree-r coordinate formula, injectivity, digit-array cardinality, nonempty equal-length pairs, and exact word length.

**Theorem 1.1 (Full central-digit system from actual pairs).**

$$actualpositivePairmultiScalecentraldigits$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection.actual_positivePair_multiScale_central_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, r,t:N, and 2<=r, the selected actual leading differences are linearly independent; every selected pair has two nonempty equal-length words; every digit word agrees with referenceWord below degree r; each degree-r coefficient difference is the indicated sum of digitValue times actualLeadingDifference; the cutoffMagnus digit map is injective; the digit-array cardinality is (2^r)^(t*actualLyndonCount A r); and every digit word has length baseLength A r*(2^t-1).

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection.actual_positivePair_multiScale_central_digits`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitData](CentralDigitData.md)
