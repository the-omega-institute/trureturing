# All actual two-sheeted neighborhood covers are voltage lifts

## Abstract

All actual two-sheeted neighborhood covers are voltage lifts

Local bijectivity forces the two-by-two incidence matrix above each actual base edge to be a permutation matrix. Explicit two-element fibers provide a labeling and hence an actual graph isomorphism to a binary voltage lift. This representation needs neither connectedness nor a preselected labeling. The fiber condition supplies surjectivity separately from the neighborhood-cover predicate.

**Theorem 1.1 (adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.adjacency` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem adjacency (c : CoverPullback.NeighborhoodCover G.Adj H.Adj Prod.fst) (v w : V) (a b : F2) : H.Adj (v,a) (w,b) ↔ G.Adj v w ∧ a+b=sign H v w.

**Theorem 1.2 (representation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.representation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.representation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem representation (K : SimpleGraph U) (c : CoverPullback.NeighborhoodCover G.Adj K.Adj p) (h : ∀ v, Fintype.card {u // p u=v}=2) : ∃ s : Voltage G, Nonempty (K ≃g BinaryLift.graph G s).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation.representation`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BinaryLift](BinaryLift.md)
