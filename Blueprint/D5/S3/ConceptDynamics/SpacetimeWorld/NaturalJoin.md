# Natural Join of Dependent Domains

## Abstract

Natural join is the largest compatible domain and retains extra constraints.

**Theorem 1.1 (Both local restrictions determine the largest domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.naturalJoin_greatest`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.naturalJoin_greatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Valuations live on the union of the name sets. Both restrictions use Mathlib dependent restriction maps into the two local valuation types. Every domain satisfying both membership conditions is a subset of the join. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.2 (Additional constraints remain part of the joint model).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_greatest`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_greatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Intersecting the natural join with an extra set is the largest domain satisfying all three conditions. Disjoint name sets supply no theorem that would remove the extra set. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.3 (Any admissible subdomain is retained exactly).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_realizes`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choosing an admissible subdomain as the extra constraint returns precisely that subdomain. The diagonal witness uses this representation. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_greatest`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_realizes`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.naturalJoin_greatest`
- Dependency: [D5/S3/ConceptDynamics/SpacetimeWorld/WorldDomains](WorldDomains.md)
