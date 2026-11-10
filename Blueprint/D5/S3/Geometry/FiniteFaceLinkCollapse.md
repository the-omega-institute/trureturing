# Finite collapse geometry

## Abstract

Original-label nonempty-face link collapse preserves ordered pairs, every frame, and the whole antistar fixed set.

The face link, antistar, and current frame all use the same finite original vertex type. A sequence replayed through exact current frames records ordered pairs and every intermediate frame, fixes the whole antistar, and feeds the literal graph residual complex; empty erased faces occur only through AugmentedFace and no ghost vertex is materialized.

**Theorem 1.1 (Exact nonempty face-link membership).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceLink`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceLink` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any K, E and s, s belongs to faceLink K E exactly when s is nonempty, DisjointFrom E s and E union s belongs to K. These are the actual source hypotheses on original labels.

**Theorem 1.2 (Exact antistar membership).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceAntistar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceAntistar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any K, E and s, s belongs to faceAntistar K E exactly when s belongs to K and E is not a subset of s. The equation concerns full faces, with no extra independence or nonemptiness premise on E.

**Theorem 1.3 (Exact current-frame membership).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceFrame`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceFrame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any K, E, M and s, s belongs to faceFrame K E M exactly when s belongs to K and either E is not a subset of s or s minus E is an AugmentedFace of M. The augmented empty face is retained.

**Definition 1.4 (Original-label disjointness).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.DisjointFrom`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.DisjointFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DisjointFrom E s means every x∈E is absent from s; E and s stay finite subsets of the same original V.

**Definition 1.5 (Nonempty face link).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

faceLink K E has faces s satisfying s.Nonempty, DisjointFrom E s, and E∪s∈K. The empty face is excluded from the realization carrier.

**Definition 1.6 (Whole antistar).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

faceAntistar K E has exactly s∈K with E not⊆s. It includes every original component and every face avoiding E.

**Definition 1.7 (Current frame from an augmented link).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

faceFrame K E M has s∈K and either E is not⊆s or AugmentedFace M (s minus E). The augmented empty branch controls an empty erased face combinatorially only.

**Theorem 1.8 (Antistar lies in every frame).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_le_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_le_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

faceAntistar K E ≤ faceFrame K E M.

**Theorem 1.9 (Frame is an original subcomplex).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

faceFrame K E M ≤ K.

**Theorem 1.10 (Initial frame identity).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For hE : E.Nonempty, faceFrame K E (faceLink K E) = K, including the empty erased face only through AugmentedFace.

**Theorem 1.11 (Containing-face frame criterion).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_containing_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_containing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M≤faceLink K E and hs:s∈K, then E⊆s implies s∈faceFrame K E M iff AugmentedFace M (s minus E).

**Theorem 1.12 (Exact intermediate link).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M≤faceLink K E, faceLink (faceFrame K E M) E = M on the original label type.

**Theorem 1.13 (Coface correspondence).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_coface_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_coface_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M≤faceLink K E, P.ambient=M, hs:s∈faceFrame K E M, and hEs:E⊆s, E∪P.lower ⊂ s iff P.lower ⊂ s minus E. The containing-E hypothesis is necessary because every antistar face is retained. This is the exact bridge used by every lifted free pair.

**Theorem 1.14 (Lifted freeness specification).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.lifted_pair_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.lifted_pair_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For hM:M≤faceLink K E, P.ambient=M, hPsub:M≤faceFrame K E M, every s∈faceFrame K E M with E∪P.lower⊂s equals E∪P.upper.

**Theorem 1.15 (Singleton link identity).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

faceLink K {v} = link K v, with the same nonempty original-label faces and v-avoidance.

**Theorem 1.16 (Insertion link identity).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If v∉F, faceLink K (insert v F) = faceLink (link K v) F, preserving the original coordinate carrier.

**Theorem 1.17 (Singleton antistar identity).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

faceAntistar K {v} = deletion K v.

**Theorem 1.18 (Insertion frame decomposition).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F.Nonempty, v∉F, {v}∈K, and M≤faceLink K (insert v F), faceFrame K (insert v F) M = deletion K v ⊔ cone v (faceFrame (link K v) F M). The v∈s branch retains the augmented apex singleton.

**Theorem 1.19 (Insertion antistar decomposition).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F.Nonempty, v∉F, and {v}∈K, faceAntistar K (insert v F) = deletion K v ⊔ cone v (faceAntistar (link K v) F). The singleton erased-face branch is present only because F is nonempty.

**Theorem 1.20 (Singleton frame decomposition).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M≤link K v and {v}∈K, faceFrame K {v} M = deletion K v ⊔ cone v M.

**Definition 1.21 (Original pair transport relation).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.PairLiftedBy`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.PairLiftedBy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PairLiftedBy D v P Q means that P is exactly Pair.liftPairOver Q D v with explicit ambient and Fresh witnesses; the output pair is first and source pair second.

**Theorem 1.22 (Lifted ordered-pair relation).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.pairs_liftOver_forall2`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.pairs_liftOver_forall2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For S:Sequence M N, List.Forall₂ (PairLiftedBy D v) relates (S.liftOver D v hMD hvD).pairs to S.pairs in order.

**Definition 1.23 (Inserted-face pair specification).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.PairUnionSpec`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.PairUnionSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PairUnionSpec E d P Q asserts P.lower=E∪Q.lower, P.apex=Q.apex, and P.upper=E∪Q.upper.

**Definition 1.24 (Singleton face-link collapse).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.singletonFaceCollapse`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.singletonFaceCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singletonFaceCollapse K v d consumes a Sequence on faceLink K {v} and returns the lifted sequence over faceAntistar K {v}; it reuses the original singleton linkCollapseDeletion owner and remains available independently of the general frame replay.

**Definition 1.25 (General face-link collapse).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

faceLinkCollapse K E d hE hEK S replays S with each current ambient equal to faceFrame K E M, adjoining E to both faces of every original pair, and appends the exact final pair with lower E, apex d, and upper E∪{d}. It handles every nonempty E, including singletons, in the original Sequence owner. The output carrier is the exact faceAntistar K E on original labels.

**Theorem 1.26 (Derived terminal label and coface).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.terminal_data`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.terminal_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For S:Sequence (faceLink K E) (vertexComplex d), the source sequence itself proves d∉E and E∪{d}∈K. No ghost-vertex or edge premise is added.

**Theorem 1.27 (Exact pair count).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_pair_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_pair_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For hE:E.Nonempty, hEK:E∈K, and S, (faceLinkCollapse K E d hE hEK S).pairs.length = S.pairs.length + 1. The extra terminal pair is counted exactly.

**Theorem 1.28 (Ordered pair and terminal specification).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_ordered_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_ordered_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist qs q with output pairs = qs ++ [q], List.Forall₂ (PairUnionSpec E d) qs S.pairs, q.lower=E, q.apex=d, and q.upper=E∪{d}. The theorem preserves output/source order and does not replace it by an untracked witness.

**Theorem 1.29 (Exact n+1 frame specification).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_frames`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every i < S.pairs.length+1, the output frame getD i K equals faceFrame K E (S.frames.getD i (faceLink K E)). This quantifies over every intermediate frame, including the terminal frame index.

**Definition 1.30 (Packaged face-link lift result).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.FaceLinkLiftResult`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.FaceLinkLiftResult` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FaceLinkLiftResult stores the actual output Sequence K (faceAntistar K E), derived d-not-in-E and terminal coface, exact pair count, ordered-pair relation, n+1 frame specification, exact link of every source frame, and a homotopy fixed on the whole antistar realization.

**Definition 1.31 (Constructed packaged result).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkLift`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

faceLinkLift builds FaceLinkLiftResult from faceLinkCollapse, terminal_data, pair/frame theorems, faceFrame_link, and Sequence.collapseHomotopy_fixed.

**Theorem 1.32 (Whole antistar fixed).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_faceAntistar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_faceAntistar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For R:FaceLinkLiftResult, every t:I and x:Space K with x.val∈realization(faceAntistar K E) satisfies R.sequence.collapseHomotopy (t,x)=x. The fixed set is the complete realized antistar.

**Theorem 1.33 (Each original deletion lies in the antistar).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.deletion_le_faceAntistar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.deletion_le_faceAntistar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If e∈E, deletion K e ≤ faceAntistar K E as a face-collection inclusion.

**Theorem 1.34 (Whole deletion fixed through actual inclusion).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_whole_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_whole_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For e∈E and x:Space(deletion K e), the same collapse homotopy fixes realizationInclusion (deletion_le K e) x in Space K; deletion_le_faceAntistar he proves that its unchanged coordinates lie in the fixed antistar. This retains disconnected components and all original coordinates.

**Definition 1.35 (Graph residual predicate).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.residualPredicate`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.residualPredicate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a simple graph G and finite face E, residualPredicate G E x means x∉E and x is nonadjacent to every original e∈E.

**Theorem 1.36 (Graph face link as restricted complex).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_faceLink_eq_restricted`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_faceLink_eq_restricted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If E is nonempty and G.IsIndepSet (E:Set V), faceLink of the actual independence complex equals restricted G (residualPredicate G E). The equality is on nonempty original-label finite faces.

**Definition 1.37 (Literal edge residual predicate).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.edgeResidualPredicate`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.edgeResidualPredicate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edgeResidualPredicate G b c x is x≠b, x≠c, ¬G.Adj b x, and ¬G.Adj c x. It keeps the graph consumer on original labels.

**Theorem 1.38 (Pair residual equality).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_residualPredicate_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_residualPredicate_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b≠c, residualPredicate G {b,c} = edgeResidualPredicate G b c as predicates on V.

**Theorem 1.39 (Edge antistar union of whole deletions).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_antistar_union_deletions`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_antistar_union_deletions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any K and b,c, faceAntistar K {b,c} = deletion K b ⊔ deletion K c as an equality of face collections, not merely vertex sets.

**Definition 1.40 (Graph edge consumer).**

Lean statement: `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_edge_faceLinkLift`

*Formalization.* `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_edge_faceLinkLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given b≠c, an independent edge, an actual sequence S on restricted G (edgeResidualPredicate G b c), the edge face in the independence complex, and the exact face-link equality hres, graph_edge_faceLinkLift returns FaceLinkLiftResult for the cast sequence. The only transport is equality cast; no mapHomeomorph invents a combinatorial sequence.

## References

- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.DisjointFrom`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.FaceLinkLiftResult`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.PairLiftedBy`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.PairUnionSpec`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.deletion_le_faceAntistar`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.edgeResidualPredicate`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_antistar_union_deletions`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.edge_residualPredicate_eq`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_insert`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_le_frame`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceAntistar_singleton`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_coface_iff`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_containing_iff`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_insert`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_le`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_link_eq`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceFrame_singleton`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_frames`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_ordered_pairs`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkCollapse_pair_count`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLinkLift`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_insert`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.faceLink_singleton`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_faceAntistar`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.fixed_whole_deletion`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_edge_faceLinkLift`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.graph_faceLink_eq_restricted`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.lifted_pair_spec`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceAntistar`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceFrame`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.mem_faceLink`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.pairs_liftOver_forall2`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.residualPredicate`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.singletonFaceCollapse`
- Truth anchor: `D5/S3/Geometry/FiniteFaceLinkCollapse.terminal_data`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/Models](FiniteComponentClosure/Models.md)
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](FiniteGraphVertexSubstitution.md)
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
