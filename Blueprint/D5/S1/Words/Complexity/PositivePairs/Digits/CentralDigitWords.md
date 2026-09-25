# CentralDigitWords

## Abstract

Direction-major and scale-minor digits build literal positive words.

This module defines the base-2^r digit arrays, literal powered blocks, complete direction-major and scale-minor words, their all-zero reference word, and the fixed base-length coefficient. These are repository constructions built from the selected actual directions recorded by the preceding owner.

**Definition 1.1 (Degree-dependent digit base).**

$$digitBase$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitBase r is 2^r.

**Definition 1.2 (Complete direction-scale digit arrays).**

$$DigitArray$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.DigitArray` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

DigitArray A r t is the function space assigning a base-2^r digit to every selected actual direction and every scale below t.

**Definition 1.3 (A direction's encoded natural).**

$$digitValue$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitValue reads the t digits of one direction in base digitBase r using Nat.ofDigits.

**Definition 1.4 (An actual positive-word digit block).**

$$digitBlock$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.digitBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For a selected pair (u,v), scale s, and digit j, digitBlock concatenates j copies of the 2^s literal power of u and digitBase r-1-j copies of the matching power of v.

**Definition 1.5 (The complete multi-scale positive word).**

$$multiScaleWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.multiScaleWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

multiScaleWord concatenates every digitBlock in direction-major, scale-minor order; at t=0 the result is the empty word.

**Definition 1.6 (The zero-digit reference word).**

$$referenceWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords.referenceWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

referenceWord A r t is multiScaleWord at the all-zero digit array, hence uses the powered v-side in every block.

**Definition 1.7 (Common-length coefficient).**

$$baseLength$$

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
