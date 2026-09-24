# Full Actual Positive-Pair Span

## Abstract

The complete indexed family of actual positive-pair leading differences spans every rationalized Lyndon standard bracket and is stable under literal power substitution.

The classical Lyndon bracket basis motivates the target directions. The new content here is realizability by the complete family of actual recursively generated positive-word pairs, without quotienting duplicate indices.

**Definition 1.1 (Rational homogeneous polynomials).**

$$RationalHomogeneous$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairFullFamilySpan.RationalHomogeneous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

RationalHomogeneous p r means every free word in the coefficient support of p has length r.

**Definition 1.2 (An actual indexed leading difference).**

$$actualLeadingDifference$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairFullFamilySpan.actualLeadingDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, level r, and a PositivePairIndex, actualLeadingDifference lifts the complete degree-r cutoff difference cutoffMagnus(u)-cutoffMagnus(v) to the full rational word algebra.

**Definition 1.3 (Span of the full actual family).**

$$fullFamilySpan$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairFullFamilySpan.fullFamilySpan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

fullFamilySpan A r is the Q-submodule spanned by the range of actualLeadingDifference over every PositivePairIndex A r.

**Theorem 1.4 (Every standard bracket is realized in the span).**

$$everystandardBracketmem$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairFullFamilySpan.every_standardBracket_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A and every word w, the rational coefficient extension of standardBracket w belongs to fullFamilySpan A w.length. The induction uses the actual successor commutator and does not assume an abstract free parameter family.

**Definition 1.5 (Literal letter-power substitution).**

$$literalPowerWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairFullFamilySpan.literalPowerWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

literalPowerWord m source replaces every letter of source by m consecutive copies of that same letter.

**Theorem 1.6 (Power substitution preserves lower data and scales the lead).**

$$literalPowerSubstitutionactualpositivePair$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairFullFamilySpan.literalPowerSubstitution_actual_positivePair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A with decidable equality, m,r, and every actual pair index, powering both pair words multiplies each length by m, preserves equal positive lengths at levels r>=2 when m>0, preserves all scattered counts below r, and scales every degree-r count difference by m^r, including degenerate levels.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.RationalHomogeneous`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.actualLeadingDifference`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.every_standardBracket_mem`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.fullFamilySpan`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.literalPowerSubstitution_actual_positivePair`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairFullFamilySpan.literalPowerWord`
- Dependency: [D5/S1/Words/Complexity/PositivePairWordCoefficients](PositivePairWordCoefficients.md)
