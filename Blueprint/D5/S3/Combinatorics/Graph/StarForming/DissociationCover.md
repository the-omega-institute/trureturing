# Dissociation under local covers and square exclusions

## Abstract

Dissociation under local covers and square exclusions

Local injectivity alone pulls back induced maximum degree at most one. Reflection additionally requires explicit global projection-surjectivity. A four-cycle cannot have any three consecutive vertices selected in a dissociation set. The square exclusion is a graph lemma, not a complete weighted-capacity certificate or a theorem equating SF with beta.

**Definition 1.1 (Dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.Dissociates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.Dissociates` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Dissociates {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Theorem 1.2 (dissociates pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociates_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) {selection : Base → Prop} (hdissociates : Dissociates baseAdjacency selection) : Dissociates liftAdjacency (fun vertex => selection (projection vertex)).

**Theorem 1.3 (dissociates of pullback).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_of_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_of_pullback` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociates_of_pullback {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hsurjective : ∀ vertex, ∃ lifted, projection lifted = vertex) {selection : Base → Prop} (hdissociates : Dissociates liftAdjacency (fun vertex => selection (projection vertex))) : Dissociates baseAdjacency selection.

**Theorem 1.4 (dissociates pullback iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociates_pullback_iff {Base Lift : Type} {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop} {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection) (hsurjective : ∀ vertex, ∃ lifted, projection lifted = vertex) {selection : Base → Prop} : Dissociates liftAdjacency (fun vertex => selection (projection vertex)) ↔ Dissociates baseAdjacency selection.

**Theorem 1.5 (four cycle excludes triples).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.four_cycle_excludes_triples`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.four_cycle_excludes_triples` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem four_cycle_excludes_triples {Vertex : Type} {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop} (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hdissociates : Dissociates adjacency selection) (first second third fourth : Vertex) (hfirstThird : first ≠ third) (hsecondFourth : second ≠ fourth) (hfirstSecond : adjacency first second) (hsecondThird : adjacency second third) (hthirdFourth : adjacency third fourth) (hfourthFirst : adjacency fourth first) : ¬ (selection first ∧ selection second ∧ selection third) ∧ ¬ (selection second ∧ selection third ∧ selection fourth) ∧ ¬ (selection third ∧ selection fourth ∧ selection first) ∧ ¬ (selection fourth ∧ selection first ∧ selection second).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.Dissociates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_of_pullback`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.dissociates_pullback_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationCover.four_cycle_excludes_triples`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverPullback](CoverPullback.md)
