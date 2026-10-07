# Simple sections of finite products

## Abstract

A simple section of a finite product occurs in one factor even when its section subgroup is arbitrary.

**Theorem 1.1 (A simple section occurs in a factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts.simple_involves_pi_factor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts.simple_involves_pi_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary simple group A, a finite index type and an arbitrary family of groups, if A is a section of their product, then A is a section of one factor. A section is a surjective image of an arbitrary subgroup; that subgroup need not itself be a product. Induction by adjoining one index uses the simple-section image-or-kernel alternative, and embeds the projection kernel into the new factor. Individual factors need not be finite.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts.simple_involves_pi_factor`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Sections](Sections.md)
