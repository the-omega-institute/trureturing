# All 4096 codewords

## Abstract

The exact full Golay weight enumerator.

**Theorem 1.1 (Complete row certificates).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_row_counts`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_row_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the sixty-four prefix rows contains sixty-four distinct messages. Their actual packed weights are counted by kernel reduction. The separately proved decoding identity ties the packed computation to the polynomial linear code.

**Theorem 1.2 (No other weights).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_weight_choices`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_weight_choices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every message pair has weight zero, eight, twelve, sixteen or twenty-four; there is no sampling or truncation.

**Theorem 1.3 (1 + 759 z^8 + 2576 z^12 + 759 z^16 + z^24).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.exact_weight_enumerator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.exact_weight_enumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite counts are transported through the actual weight identity and summed, giving coefficients one, seven hundred fifty-nine, two thousand five hundred seventy-six, seven hundred fifty-nine and one. Faithful enumeration identifies these with all actual codewords. This is the classical Golay enumerator, not a novelty claim, a moonshine character or a Monster representation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.exact_weight_enumerator`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_row_counts`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.finite_weight_choices`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator](ExplicitGolayEnumerator.md)
