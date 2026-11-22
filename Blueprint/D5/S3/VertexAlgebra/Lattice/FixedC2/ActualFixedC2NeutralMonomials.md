# Neutral Word Reduction in the Fixed Lattice C2 Quotient

## Abstract

The fixed quotient product reduces neutral words by oscillator length.

The lattice data consist of a natural-number rank and a symmetric integral Gram matrix with even diagonal. The actual complex carrier consists of finitely supported charge families of oscillator polynomials.

**Theorem 1.1 (The fixed minus-one mode preserves the fixed C2 span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_product_mem_c2`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_product_mem_c2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commuting the (-1)-mode past a generator's (-2)-mode gives a finite sum of products at indices -3-j with j nonnegative. Translation puts all fixed products at indices at most -2 in the fixed C2 span. Induction on the span gives preservation in the second argument. The vacuum commutator gives commutativity modulo that span, hence preservation in the first argument as well.

**Definition 1.2 (Multiplication descends from the actual minus-one mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixedQuotientProduct`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixedQuotientProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The intrinsic fixed quotient has a complex bilinear product. On two fixed representatives it takes the class of their actual (-1)-product. Preservation of the fixed C2 span in both arguments makes this independent of representatives.

**Theorem 1.3 (The leading word and the contraction terms).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.quadratic_word_length`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.quadratic_word_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual quadratic (-1)-product on a neutral word is a sum of two finitely supported mode expansions. The initial term of the first sum creates both oscillators and gives concatenation. Every other term uses one annihilation followed by one creation and lies in the span of words of the input length. Thus the difference from the concatenated word lies in the complex span of charge-zero words of exactly the input length, for any input word. On the empty word, vacuum creation gives the pair exactly.

**Theorem 1.4 (The length reduction descends to the fixed quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_quadratic_word_length`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_quadratic_word_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An even neutral word is fixed by the sign involution. The quotient product of a pair class with such a word class differs from the concatenated class by a linear combination of neutral classes with two fewer oscillators than the concatenation.

**Theorem 1.5 (A high pair shortens an even neutral word).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.neutral_word_high_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.neutral_word_high_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the even neutral word be a permutation of a chosen pair followed by an even-length remainder. Assume the pair has total index at least seven and its first basis entry has nonzero Gram diagonal. Commutativity of the oscillator polynomials moves the chosen pair to the front. Its class vanishes, so the whole word class lies in the complex span of neutral classes of exactly the remainder's length.

**Theorem 1.6 (The high-pair reduction for the actual Leech lattice).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.leech_neutral_word_high_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.leech_neutral_word_high_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual Leech lattice, positive definiteness of the real Gram matrix gives the nonzero diagonal entry. If an even neutral word is a permutation of a pair of total index at least seven followed by an even-length remainder, its class lies in the complex span of neutral classes of exactly the remainder's length.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixedQuotientProduct`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_product_mem_c2`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.fixed_quadratic_word_length`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.leech_neutral_word_high_pair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.neutral_word_high_pair`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.quadratic_word_length`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic](../ActualLeechHyperbolic.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs](ActualFixedC2NeutralPairs.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra](../NormFourVacuumVertexAlgebra.md)
