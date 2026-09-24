# Multi-Scale Central Digits from Actual Positive Pairs

## Abstract

Independent directions from the complete actual positive-pair family support injective equal-length multi-scale digit words.

For each length r, ActualLyndonWord is the subtype of actual words of length r that satisfy IsLyndon. The module publicly installs a lifted linear order on this subtype and, for finite A, a Fintype instance obtained by injection into length-r vectors. These two anonymous public instances support the cardinality and deterministic selection below; the digit construction itself is a repository result, not a claim attributed to the cited paper.

**Definition 1.1 (Actual Lyndon words of a fixed length).**

$$ActualLyndonWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.ActualLyndonWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A and r:N, ActualLyndonWord A r is the subtype of lists w with w.length=r and IsLyndon w.

**Definition 1.2 (The actual Lyndon-word count).**

$$actualLyndonCount$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.actualLyndonCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, actualLyndonCount A r is Fintype.card (ActualLyndonWord A r), not an independent proxy parameter.

**Definition 1.3 (Selected independent actual directions).**

$$selectedDirection$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.selectedDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For each r, selectedDirection chooses one PositivePairIndex A r for every element of Fin(actualLyndonCount A r), with the resulting actualLeadingDifference family linearly independent over Q.

**Definition 1.4 (Degree-dependent digit base).**

$$digitBase$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.digitBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitBase r is 2^r.

**Definition 1.5 (Complete direction-scale digit arrays).**

$$DigitArray$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.DigitArray` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

DigitArray A r t is the function space assigning a base-2^r digit to every selected actual direction and every scale below t.

**Definition 1.6 (A direction's encoded natural).**

$$digitValue$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.digitValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

digitValue reads the t digits of one direction in base digitBase r using Nat.ofDigits.

**Definition 1.7 (An actual positive-word digit block).**

$$digitBlock$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.digitBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For a selected pair (u,v), scale s, and digit j, digitBlock concatenates j copies of the 2^s literal power of u and digitBase r-1-j copies of the matching power of v.

**Definition 1.8 (The complete multi-scale positive word).**

$$multiScaleWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.multiScaleWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

multiScaleWord concatenates every digitBlock in direction-major, scale-minor order; at t=0 the result is the empty word.

**Definition 1.9 (The zero-digit reference word).**

$$referenceWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.referenceWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

referenceWord A r t is multiScaleWord at the all-zero digit array, hence uses the powered v-side in every block.

**Definition 1.10 (Common-length coefficient).**

$$baseLength$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairCentralDigits.baseLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

baseLength A r is (2^r-1) times the sum of the selected u-word lengths and is the fixed coefficient in the multi-scale length law.

**Theorem 1.11 (Full central-digit system from actual pairs).**

$$actualpositivePairmultiScalecentraldigits$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairCentralDigits.actual_positivePair_multiScale_central_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, r,t:N, and 2<=r, the selected actual leading differences are linearly independent; every selected pair has two nonempty equal-length words; every digit word agrees with referenceWord below degree r; each degree-r coefficient difference is the indicated sum of digitValue times actualLeadingDifference; the cutoffMagnus digit map is injective; the digit-array cardinality is (2^r)^(t*actualLyndonCount A r); and every digit word has length baseLength A r*(2^t-1).

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.ActualLyndonWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.DigitArray`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.actualLyndonCount`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.actual_positivePair_multiScale_central_digits`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.baseLength`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.digitBase`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.digitBlock`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.digitValue`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.multiScaleWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.referenceWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairCentralDigits.selectedDirection`
- Dependency: [D5/S1/Words/Complexity/PositivePairFullFamilySpan](PositivePairFullFamilySpan.md)
