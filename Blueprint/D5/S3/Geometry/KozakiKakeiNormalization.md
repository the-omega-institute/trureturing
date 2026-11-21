# Existence and uniqueness of the ordered normal form

## Abstract

The written level equation is precisely the condition for an admissible matrix to have a unique representative in ordered normal form.

**Definition 1.1 (Unit consecutive minors).**

Lean statement: `D5/S3/Geometry/KozakiKakeiNormalization.UnitAdjacent`

*Formalization.* `D5/S3/Geometry/KozakiKakeiNormalization.UnitAdjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each successive pair in linear column order has minor one.

**Theorem 1.2 (A normalized matrix is on the level).**

$$\forall m : \mathbb{N}, \forall Z : \operatorname{Chart}(K,m), 2 \le m \implies \operatorname{Normalized}(m,Z) \implies \operatorname{evenProduct}(Z) = \operatorname{oddProduct}(Z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiNormalization.normalized_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All factors of both written matching products are one.

**Theorem 1.3 (Existence of the ordered representative).**

$$\forall m : \mathbb{N}, \forall Z : \operatorname{Chart}(K,m), 2 \le m \implies \operatorname{Admissible}(Z) \implies \operatorname{evenProduct}(Z) = \operatorname{oddProduct}(Z) \implies (\exists W : \operatorname{Chart}(K,m), \operatorname{Normalized}(m,W) \land \operatorname{MatEquivalent}(W,Z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiNormalization.normalized_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invertible row operation fixes the first two columns. The initial diagonal factors fix the third, and a recurrence sets the remaining consecutive minors to one. The level equation then forces the closing minor to be one.

**Theorem 1.4 (Uniqueness within a matrix class).**

$$\forall m : \mathbb{N}, \forall Z,W : \operatorname{Chart}(K,m), 2 \le m \implies \operatorname{Normalized}(m,Z) \implies \operatorname{Normalized}(m,W) \implies \operatorname{MatEquivalent}(W,Z) \implies W = Z$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiNormalization.normalized_unique_of_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two fixed columns force the left transformation to be diagonal. The third forces its entries to agree, and the consecutive minors determine all remaining column factors.

**Theorem 1.5 (Characterization of normalizable matrices).**

$$\forall m : \mathbb{N}, \forall Z : \operatorname{Chart}(K,m), 2 \le m \implies \operatorname{Admissible}(Z) \implies ((\exists! W : \operatorname{Chart}(K,m), \operatorname{Normalized}(m,W) \land \operatorname{MatEquivalent}(W,Z)) \iff \operatorname{evenProduct}(Z) = \operatorname{oddProduct}(Z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiNormalization.normalized_representative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible matrix, the existence of exactly one normalized equivalent matrix is equivalent to the literal equality of the two determinant products.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiNormalization.UnitAdjacent`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiNormalization.normalized_exists`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiNormalization.normalized_level`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiNormalization.normalized_representative_iff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiNormalization.normalized_unique_of_equiv`
- Dependency: [D5/S3/Geometry/KozakiKakeiMatrixEquiv](KozakiKakeiMatrixEquiv.md)
