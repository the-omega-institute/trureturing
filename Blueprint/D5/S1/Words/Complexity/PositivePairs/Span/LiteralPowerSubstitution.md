# LiteralPowerSubstitution

## Abstract

Literal power substitution realizes actual positive pairs at controlled degree.

The classical Lyndon bracket basis motivates the target directions. The new content here is realizability by the complete family of actual recursively generated positive-word pairs, without quotienting duplicate indices.

**Definition 1.1 (Literal letter-power substitution).**

$$literalPowerWord$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution.literalPowerWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

literalPowerWord m source replaces every letter of source by m consecutive copies of that same letter.

**Theorem 1.2 (Power substitution preserves lower data and scales the lead).**

$$literalPowerSubstitutionactualpositivePair$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution.literalPowerSubstitution_actual_positivePair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A with decidable equality, m,r, and every actual pair index, powering both pair words multiplies each length by m, preserves equal positive lengths at levels r>=2 when m>0, preserves all scattered counts below r, and scales every degree-r count difference by m^r, including degenerate levels.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution.literalPowerSubstitution_actual_positivePair`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution.literalPowerWord`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan](FullFamilyBracketSpan.md)
