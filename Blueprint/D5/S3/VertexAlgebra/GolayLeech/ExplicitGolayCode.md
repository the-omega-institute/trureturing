# Exact integral construction

## Abstract

Explicit Golay-congruence lattice mathematics.

**Theorem 1.1 (Exact polynomial generator).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.polynomial_generator_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.polynomial_generator_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal generator matrix equals the degree-below-twelve cyclic polynomial construction with exponents 0,1,5,6,7,9,11. Each shifted polynomial has odd weight seven, so its twenty-fourth parity coordinate is one. Every generator equality is checked in the kernel.

**Theorem 1.2 (No duplicate codewords).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.encode_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.encode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The leading twelve coordinates form a triangular matrix with unit diagonal. Its determinant and injectivity identify all messages faithfully.

**Theorem 1.3 (The carry word).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.code_contains_all_ones`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.code_contains_all_ones` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit message produces the all-ones word, which is needed when two odd lattice vectors are added.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.code_contains_all_ones`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.encode_injective`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.polynomial_generator_certificate`
