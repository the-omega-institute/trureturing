# Norm-Two Vectors and Ternary Syndromes

## Abstract

A congruent norm-twelve frame reduces norm-two exclusion to short ternary syndromes.

**Theorem 1.1 (A norm-two vector produces a kernel word).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.exists_short_ternary_kernel_word_of_norm_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.exists_short_ternary_kernel_word_of_norm_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pairing coordinates of a norm-two row have squared norm 24 and share one parity. More than 24 odd coordinates would have larger squared norm. Dividing the even coordinates by two gives squared norm 6. Reduction modulo three therefore gives a nonzero word of weight at most six. The frame identity makes its ternary syndrome zero.

**Theorem 1.2 (Injective short syndromes exclude norm two).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.bilinear_ne_two_of_short_syndrome_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.bilinear_ne_two_of_short_syndrome_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition the support of a word of weight at most six into two sets of size at most three. The word is the difference of the two short words obtained by retaining one restriction and negating the other. A nonzero kernel word gives two distinct short words with the same syndrome.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.bilinear_ne_two_of_short_syndrome_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.exists_short_ternary_kernel_word_of_norm_two`
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](../../LatticeGeneratingFieldLocality.md)
