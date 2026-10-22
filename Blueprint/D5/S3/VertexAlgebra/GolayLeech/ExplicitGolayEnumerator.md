# Faithful finite enumeration

## Abstract

Exact full polynomial Golay weight enumerator.

**Theorem 1.1 (Bitwise representation of the actual linear code).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.packed_encode_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.packed_encode_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding bitwise XOR gives binary addition. The twelve literal packed generators decode to the actual polynomial-generator columns. Induction proves equality with the linear encoding for every message; the packed algorithm is not an assumed numerical oracle.

**Theorem 1.2 (Every actual codeword exactly once).**

Lean statement: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.faithful_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.faithful_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two six-bit integers enumerate the entire twelve-coordinate message space bijectively. Encoding injectivity gives a unique pair for every actual codeword.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.faithful_enumeration`
- Truth anchor: `D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.packed_encode_identity`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeights](ExplicitGolayWeights.md)
