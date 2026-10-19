# Number the actual incoming split and retain its time correction

## Abstract

Number the actual incoming split and retain its time correction.

The incoming R half-edges are original edges ending at their retained incoming class; S half-edges are the retained classes returning to their old vertex. Rect.decode from the outgoing supplier enumerates those rectangular fibers. oldEdgeEquiv and newEdgeEquiv identify the original and split edge carriers with the existing counted RS and SR numbering. Endpoint equations package these as oldRelabel and newRelabel.

The source quantifies finite V,E,L, DecidableEq V,L, graph G and arbitrary label function p : E → L. The history homeomorphisms additionally require discrete topological E and L. numbered_forget is the opposite positive recoding (S,R), with no time shift. numbered_lift is the (R,S) positive recoding followed by literal negative unit translation. It does not use another parallel-edge ranking or assume nonempty endpoint fibers.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (oldEdgeEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldEdgeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the existing ranked RS edges as the original graph edges, retaining both half-edge labels and both inverse equations.

**Definition 1.2 (newEdgeEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newEdgeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the ranked SR edges as actual incoming-split edges. The retained class and original edge determine the complete split edge.

**Definition 1.3 (oldRelabel).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldRelabel`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Package the original vertex numbering and old-edge decoding as a graph relabel. The endpoint laws connect actual histories to the counted RS graph.

**Definition 1.4 (newRelabel).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newRelabel`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Package the incoming-split vertex numbering and new-edge decoding as a graph relabel from the counted SR graph.

**Theorem 1.5 (numbered_forget).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_forget`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_forget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Incoming FORGET is the opposite positive recoding, with no time shift.

**Remark 1.6 (oldNumber).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldNumber`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the existing finite numbering of the original vertices. It supplies the old endpoint coordinates for both rectangular factors.

**Remark 1.7 (newNumber).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newNumber`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number the retained incoming-split vertices, including their class labels. This gives the new endpoint coordinates without collapsing classes.

**Remark 1.8 (R).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.R`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R half-edges are original edges, ending at their incoming label class.

**Remark 1.9 (S).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.S`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S half-edges are retained classes, returning to their old vertex.

**Remark 1.10 (rDecode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.rDecode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.rDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode an R half-edge into its original edge and retained incoming class using the rectangular fiber enumerator.

**Remark 1.11 (sDecode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.sDecode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.sDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode an S half-edge into its retained class and underlying old vertex. This is the complementary half of the incoming factorization.

**Remark 1.12 (old_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.old_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.old_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Old-edge decoding preserves both numbered endpoints. These equations supply the old graph-relabel endpoint proofs.

**Remark 1.13 (new_endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.new_endpoints`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.new_endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

New-edge decoding preserves both incoming-split endpoints. These equations supply the new graph-relabel endpoint proofs.

**Remark 1.14 (counted).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.counted`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.counted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

View the numbered edges of a square count matrix as a directed multigraph. This is the graph adapter used by the path-numbering maps.

**Remark 1.15 (oldPaths).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldPaths`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the inverse old relabel coordinatewise to number every original history as a path in RS. Discrete edge topology supplies the homeomorphism.

**Remark 1.16 (newPaths).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newPaths`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number every incoming-split history as a path in SR through the inverse new relabel. The map keeps the original split-edge data.

**Remark 1.17 (numbered_lift).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_lift`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Incoming LIFT is positive R,S with the necessary -1 correction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.R`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.S`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.counted`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newEdgeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newNumber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newPaths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.newRelabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.new_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_forget`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.numbered_lift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldEdgeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldNumber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldPaths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.oldRelabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.old_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.rDecode`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding.sDecode`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph](FiniteGraphRelabelHomeomorph.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws](NumberedPositiveInverseLaws.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding](OutSplitNumberedRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](../TwoSidedFiniteInduction.md)
