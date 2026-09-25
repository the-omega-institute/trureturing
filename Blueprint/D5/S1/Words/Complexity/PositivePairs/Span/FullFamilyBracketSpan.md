# FullFamilyBracketSpan

## Abstract

Actual full-family differences span every rational Lyndon standard bracket.

The classical Lyndon bracket basis motivates the target directions. The new content here is realizability by the complete family of actual recursively generated positive-word pairs, without quotienting duplicate indices.

**Theorem 1.1 (Every standard bracket is realized in the span).**

$$everystandardBracketmem$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan.every_standardBracket_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A and every word w, the rational coefficient extension of standardBracket w belongs to fullFamilySpan A w.length. The induction uses the actual successor commutator and does not assume an abstract free parameter family.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan.every_standardBracket_mem`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity](FullFamilyHomogeneity.md)
