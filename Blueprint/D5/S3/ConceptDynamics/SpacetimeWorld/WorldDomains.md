# Dependent Worlds and Typed Images

## Abstract

Explicit world domains preserve coordinate typing and guarded legality.

**Theorem 1.1 (A guard changes the domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.guarded_nonempty_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.guarded_nonempty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Worlds are the actual subtype of a nonempty set of dependent valuations. The restricted domain is nonempty exactly when some original world satisfies the guard. The equivalence of guarded subtypes passes both membership proofs to any partial operation; no value is supplied outside that domain. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.2 (Logical exclusion is a domain restriction).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.world_exclusion_eq_guarded`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.world_exclusion_eq_guarded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

World exclusion removes worlds in the valuation domain. Selection-family exclusion instead removes elements of the native selection space, while contribution complement changes each selected event subset within its retained context. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.3 (Native complement acts on a family by direct image).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.complement_family_readouts`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.complement_family_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Possible readouts use the merged native Context, Selection and q. Applying native complement to a family changes its readout image by background minus readout. Family exclusion instead takes the complement of the set of possible selections. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.4 (Empty constraints are distinct from a zero-valued model).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.incompatible_image_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.incompatible_image_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant zero image on a compatible nonempty domain is the singleton containing zero. The image of the empty domain is empty, and those images differ. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.complement_family_readouts`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.guarded_nonempty_iff`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.incompatible_image_ne_zero`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains.world_exclusion_eq_guarded`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](../Spacetime/ComplementCharge.md)
