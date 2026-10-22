# Exact integral construction

## Abstract

Explicit Golay-congruence lattice mathematics.

**Theorem 1.1 (Exact corrected congruences).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_iff_congruences`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_iff_congruences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameterization x=m+2y, with m equal to zero or one, is equivalent to common coordinate parity, corrected Golay membership and sum(x)=4m modulo eight.

**Theorem 1.2 (Actual addition closure).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Odd plus odd adds the all-ones carry word. The sum condition is preserved with its exact integer carry.

**Theorem 1.3 (Even integral norm).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_even_squareSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_even_squareSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of integer coordinate squares is divisible by sixteen for every actual member. The normalization is the Euclidean dot product divided by eight.

**Theorem 1.4 (Integral polarization).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_integral_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_integral_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual addition closure and the three divisible square sums imply divisibility of every coordinate dot product by eight.

**Theorem 1.5 (Arbitrary-vector rootlessness).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_minimum_squareSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_minimum_squareSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Odd vectors have twenty-four nonzero coordinates; divisibility by sixteen raises the bound to thirty-two. A nonzero corrected codeword has at least eight odd half-coordinates. With zero corrected codeword, the quarter-coordinates have even total, so their positive square sum is even and at least two. There is no energy or coordinate cutoff.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_add`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_even_squareSum`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_iff_congruences`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_integral_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.member_minimum_squareSum`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeights](ExplicitGolayWeights.md)
