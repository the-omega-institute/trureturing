# CentralDigitWords

## Abstract

Direction-major and scale-minor digits build literal positive words.

This module defines the base-2^r digit arrays, literal powered blocks, complete direction-major and scale-minor words, their all-zero reference word, and the fixed base-length coefficient. These are repository constructions built from the selected actual directions recorded by the preceding owner.

**Definition 1.1 (Degree-dependent digit base).**

$$\forall r,\operatorname{digitBase}\left(r\right) = \operatorname{pow}\left(2, r\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitBase r is 2^r.

**Definition 1.2 (Complete direction-scale digit arrays).**

$$\forall A,r,t,\operatorname{DigitArray}\left(A, r, t\right) = \operatorname{functions}\left(\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right), \operatorname{Fin}\left(t\right), \operatorname{Fin}\left(\operatorname{digitBase}\left(r\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.DigitArray` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

DigitArray A r t is the function space assigning a base-2^r digit to every selected actual direction and every scale below t.

**Definition 1.3 (A direction's encoded natural).**

$$\forall r,t,digits,direction,\operatorname{digitValue}\left(r, t, digits, direction\right) = \operatorname{NatOfDigits}\left(\operatorname{digitBase}\left(r\right), \operatorname{ofFn}\left(\operatorname{Fin}\left(t\right), \operatorname{lambda}\left(scale, \operatorname{nat}\left(\operatorname{apply}\left(digits, direction, scale\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitValue reads the t digits of one direction in base digitBase r using Nat.ofDigits.

**Definition 1.4 (An actual positive-word digit block).**

$$\forall r,direction,scale,digit,\operatorname{digitBlock}\left(r, direction, scale, digit\right) = \operatorname{append}\left(\operatorname{repeatedWord}\left(digit, \operatorname{literalPowerWord}\left(\operatorname{pow}\left(2, scale\right), \operatorname{left}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right)\right), \operatorname{repeatedWord}\left(\operatorname{digitBase}\left(r\right) - 1 - digit, \operatorname{literalPowerWord}\left(\operatorname{pow}\left(2, scale\right), \operatorname{right}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For a selected pair (u,v), scale s, and digit j, digitBlock concatenates j copies of the 2^s literal power of u and digitBase r-1-j copies of the matching power of v.

**Definition 1.5 (The complete multi-scale positive word).**

$$\forall r,t,digits,\operatorname{multiScaleWord}\left(r, t, digits\right) = \operatorname{flatten}\left(\operatorname{ofFn}\left(\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right), \operatorname{lambda}\left(direction, \operatorname{flatten}\left(\operatorname{ofFn}\left(\operatorname{Fin}\left(t\right), \operatorname{lambda}\left(scale, \operatorname{digitBlock}\left(r, direction, scale, \operatorname{apply}\left(digits, direction, scale\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.multiScaleWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

multiScaleWord concatenates every digitBlock in direction-major, scale-minor order; at t=0 the result is the empty word.

**Definition 1.6 (The zero-digit reference word).**

$$\forall r,t,\operatorname{referenceWord}\left(r, t\right) = \operatorname{multiScaleWord}\left(r, t, \operatorname{lambda}\left(direction, \operatorname{lambda}\left(scale, 0\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.referenceWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

referenceWord A r t is multiScaleWord at the all-zero digit array, hence uses the powered v-side in every block.

**Definition 1.7 (Common-length coefficient).**

$$\forall A,r,\operatorname{baseLength}\left(A, r\right) = \left(\operatorname{digitBase}\left(r\right) - 1\right) \cdot \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right), \operatorname{lambda}\left(direction, \operatorname{length}\left(\operatorname{left}\left(\operatorname{positivePairWords}\left(r, \operatorname{selectedDirection}\left(r, direction\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.baseLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

baseLength A r is (2^r-1) times the sum of the selected u-word lengths and is the fixed coefficient in the multi-scale length law.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.DigitArray`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.baseLength`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBase`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBlock`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitValue`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.multiScaleWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.referenceWord`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections](ActualLyndonDirections.md)
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution](../Span/LiteralPowerSubstitution.md)
