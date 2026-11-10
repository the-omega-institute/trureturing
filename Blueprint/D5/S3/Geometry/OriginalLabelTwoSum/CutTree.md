# CutTree

## Abstract

The literal cut-left/full-right edge-image union is a tree on the explicit infinite-capable carrier.

**Definition 1.1 (Input).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Input`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.2 (Carrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Carrier`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.Carrier. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.3 (cut).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cut. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.4 (qL).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qL. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.5 (qR).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qR. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.6 (qR_a).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_a`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qR_a. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.7 (qR_b).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_b`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qR_b. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.8 (qL_injective).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qL_injective. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.9 (qR_injective).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.qR_injective. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.10 (overlap).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.overlap. qL x = qR y iff x=aL and y=aR, or x=bL and y=bR. Nonterminal right vertices remain distinct even if the original vertex types share names.

**Theorem 1.11 (cover).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cover. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.12 (range_intersection).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.range_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.range_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.range_intersection. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.13 (leftEmbedding).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftEmbedding`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.leftEmbedding. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.14 (rightEmbedding).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightEmbedding`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.rightEmbedding. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.15 (tree).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.tree`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.tree. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.16 (adjacency).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.adjacency. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.17 (edgeSet).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edgeSet`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edgeSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.edgeSet. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.18 (no_loops).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.no_loops`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.no_loops` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.no_loops. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.19 (leftHom).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftHom`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.leftHom. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.20 (rightHom).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightHom`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.rightHom. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Definition 1.21 (predicate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.predicate. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.22 (predicate_qL).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qL`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qL` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.predicate_qL. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.23 (predicate_qR).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qR`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.predicate_qR. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.24 (cut_separated).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cut_separated. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.25 (cut_cover).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cut_cover. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.26 (cut_side_adj).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_side_adj`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_side_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cut_side_adj. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.27 (connected).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.connected`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.connected. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.28 (left_bridge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.left_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.left_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.left_bridge. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.29 (right_bridge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.right_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.right_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.right_bridge. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.30 (isTree).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.isTree`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.isTree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.isTree. The literal mapped cut-left/full-right graph is proved connected and acyclic. Every edge is proved to be a bridge by an original-tree cut predicate. No property of the glued graph is an input.

**Theorem 1.31 (adjacency_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.adjacency_left. Mapped left adjacency is cut-left adjacency, with the additional terminal pair exactly when the original right tree has that terminal edge. This additional edge is stated explicitly.

**Theorem 1.32 (adjacency_right).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.adjacency_right. Mapped right adjacency is exactly original right-tree adjacency; the left cut graph contributes no terminal-terminal edge.

**Theorem 1.33 (cross_edge_ne).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cross_edge_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cross_edge_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.cross_edge_ne. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

**Theorem 1.34 (edge_images_disjoint).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edge_images_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edge_images_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.CutTree.Input.edge_images_disjoint. Input supplies only the original two trees, distinct terminals, and the declared left edge. Carrier is VL plus fresh right interior. The constructed tree is the image of the actual left edge deletion union the entire right tree. Its IsTree proof uses cut predicates and finite walks, with no finite-vertex assumption. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Carrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.Input`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.adjacency_right`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.connected`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cover`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cross_edge_ne`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_cover`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_separated`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.cut_side_adj`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edgeSet`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.edge_images_disjoint`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.isTree`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftEmbedding`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.leftHom`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.left_bridge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.no_loops`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.overlap`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qL`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.predicate_qR`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qL_injective`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_a`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_b`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.qR_injective`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.range_intersection`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightEmbedding`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.rightHom`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.right_bridge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CutTree.tree`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/CutWalk](CutWalk.md)
