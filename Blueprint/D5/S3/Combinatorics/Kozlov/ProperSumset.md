# Chained representatives of the literal proper sumset

## Abstract

Every repeated sum of actual proper f-vectors has a chained representative with the same number of summands and with exactly the same vector sum.

**Theorem 1.1 (Unconditional surjectivity onto the proper sumset).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperSumset.proper_sumset_surjOn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperSumset.proper_sumset_surjOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Choose actual downsets for the input tuple. At each degree take a position-first lex segment with the same total number of missing faces. The module shadow bound and nesting show that the shadow of the chosen missing layer fits into the next chosen layer. Complementing these families yields proper downsets because the missing totals at zero and one vanish. A nonempty missing layer in a later position forces a full earlier missing layer, which gives the strict chaining inequality. Each degree's total is preserved by the layer partition identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperSumset.proper_sumset_surjOn`
- Dependency: [D5/S3/Combinatorics/Kozlov/LexPositionShadow](LexPositionShadow.md)
- Dependency: [D5/S3/Combinatorics/Kozlov/ProperModel](ProperModel.md)
