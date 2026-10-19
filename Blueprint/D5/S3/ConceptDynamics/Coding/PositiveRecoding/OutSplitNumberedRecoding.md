# Number rectangular edge fibers for the actual outgoing split

## Abstract

Number rectangular edge fibers for the actual outgoing split.

Rect.matrix counts fibers of the endpoint maps and Rect.decode bijects numbered matrix edges with the actual fibers. decode_endpoints and encode_endpoints preserve both endpoints, including empty fibers. For the outgoing split, R records retained partition classes and S records original parallel-edge identities. oldEdgeEquiv and newEdgeEquiv retain both inverse equations.

The rectangular API assumes Fintype A and equivalences I ≃ Fin n, J ≃ Fin m. The outgoing part uses finite V,E,L and DecidableEq V,L; topological path numbering also uses discrete topological E,L. Restricting oldEdgeEquiv and newEdgeEquiv to their endpoint fibers derives cardinality and emptiness consequences by Fintype.card_congr and card_eq_zero_iff, including Fin 0. The anonymous Rect Fintype instance supplies infrastructure. numbered_recoding identifies the original positive (R,S) homeomorphism exactly with outgoing lift.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (decode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode a numbered matrix edge into the actual element of its endpoint fiber, with inverse encoding. Empty fibers remain empty.

**Definition 1.2 (oldEdgeEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldEdgeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Numbering of the actual old edges by RS, not an assumed order match.

**Definition 1.3 (newEdgeEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newEdgeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the ranked SR product edges as actual outgoing-split edges. The equivalence preserves each parallel-edge identity.

**Theorem 1.4 (numbered_recoding).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.numbered_recoding`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.numbered_recoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding the EXISTING numbered positive elementary recoding is exactly the actual outgoing partition lift. There is no shift or inverse substitution.

**Remark 1.5 (endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Record the chosen finite source and target indices of each actual edge. These indices define the rectangular endpoint fibers.

**Remark 1.6 (Fibre).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.Fibre`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.Fibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain all edges with the specified numbered endpoints as a subtype. Its cardinality determines the corresponding matrix coefficient.

**Remark 1.7 (matrix).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.matrix`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count each endpoint fiber. The entries are nonnegative multiplicities, including zero for an empty fiber.

**Remark 1.8 (decode_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decoding a numbered edge preserves its source and target indices. This makes the fiber enumeration compatible with graph incidence.

**Remark 1.9 (encode_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.encode_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.encode_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encoding an actual edge recovers its two chosen endpoint indices. This is the reverse incidence check for the same enumeration.

**Remark 1.10 (oldNumber).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldNumber`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number the original finite vertex type. This is the old coordinate system for the outgoing factorization.

**Remark 1.11 (newNumber).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newNumber`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number the actual outgoing-split vertices with their retained class labels. The class information is preserved in the new coordinates.

**Remark 1.12 (R).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.R`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R half-edges are the retained partition classes themselves.

**Remark 1.13 (S).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.S`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S half-edges are original edges, including every parallel identity.

**Remark 1.14 (rDecode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.rDecode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.rDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode an R half-edge as a retained outgoing class. It joins an old vertex to the corresponding split vertex.

**Remark 1.15 (sDecode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.sDecode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.sDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode an S half-edge as an original edge in the retained class. Its target is the old target vertex.

**Remark 1.16 (old_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.old_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.old_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The RS edge decoding preserves both original numbered endpoints. This identifies the original graph in the factorization.

**Remark 1.17 (new_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.new_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.new_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The SR edge decoding preserves both outgoing-split numbered endpoints. This identifies the new graph in the factorization.

**Remark 1.18 (oldPaths).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldPaths`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number every original history through the old edge equivalence and its endpoint laws. This gives the original side of the positive recoding square.

**Remark 1.19 (newPaths).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newPaths`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number every outgoing-split history through the new edge equivalence and its endpoint laws. This gives the split side of the same square.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.Fibre`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.R`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.S`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.decode_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.encode_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.matrix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newEdgeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newNumber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.newPaths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.new_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.numbered_recoding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldEdgeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldNumber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.oldPaths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.old_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.rDecode`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding.sDecode`
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](../TwoSidedFiniteInduction.md)
