# Derived Coproduct

## Abstract

Actual coproducts in the unbounded derived category of an abelian category with exact sums. This supplies the sum comparison needed by the cellular telescope; no derived solidification is assumed. New proofs, released under the Apache 2.0 license.

**Theorem 1.1 (derived Q preserves Coproduct).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.derivedQ_preservesCoproduct`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.derivedQ_preservesCoproduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The official unbounded derived localization preserves the actual coproduct of complexes whenever sums in the original category are exact. This follows from the proved roof argument, not an assumed property of Q.

**Theorem 1.2 (light Condensed Derived Q preserves Coproduct).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.lightCondensedDerivedQ_preservesCoproduct`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.lightCondensedDerivedQ_preservesCoproduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum theorem applies to the actual protected light condensed category and every small family of unbounded complexes.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.derivedQ_preservesCoproduct`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.lightCondensedDerivedQ_preservesCoproduct`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/Colimits](Colimits.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/ComplexColimit](ComplexColimit.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/KProjectiveCoproduct](KProjectiveCoproduct.md)
- Dependency: [D5/S3/HomologicalAlgebra/Solid/LocalizationCoproduct](LocalizationCoproduct.md)
