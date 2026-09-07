# Rooted Vertex Classification

## Abstract

Actual rooted vertex equivalences preserve branch codes and are classified by them.

**Theorem 1.1 (Actual rooted equivalences preserve branch codes).**

$$\begin{gathered}u, v \operatorname{universes},\\{}\forall Y: \operatorname{Type}_{u}, Z: \operatorname{Type}_{v},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\\{}\forall f: Y \to Y, g: Z \to Z,\\{}\forall r: Y, s: Z,\\{}\forall e: \operatorname{RootedVertexEquiv}\left(f, g, r, s\right), \operatorname{branchCode}\left(f, r\right)=\operatorname{branchCode}\left(g, s\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/TransientTrees/RootedVertexClassification.branch_code_eq_of_rooted_vertex_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Descendant and RootedVertexEquiv are the existing original-vertex definitions. The latter stores an actual equivalence of descendant subtypes, its two inverse laws, the distinguished root equality, and preservation and reflection of internal TransientChild edges.

Fix the given equivalence on its original carriers. Every descendant's complete child fiber is transported using this equivalence and its inverse. Well-founded induction proves branch-code equality at every descendant and its image. Multiset transport retains all occurrences, including repeated identical child branches. Specialization at the root gives the displayed equality.

**Theorem 1.2 (Branch codes classify actual rooted vertices).**

$$\begin{gathered}u, v \operatorname{universes},\\{}\forall Y: \operatorname{Type}_{u}, Z: \operatorname{Type}_{v},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\\{}\forall f: Y \to Y, g: Z \to Z,\\{}\forall r: Y, s: Z,\\{}\operatorname{Nonempty}\left(\operatorname{RootedVertexEquiv}\left(f, g, r, s\right)\right) \iff \operatorname{branchCode}\left(f, r\right)=\operatorname{branchCode}\left(g, s\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/TransientTrees/RootedVertexClassification.rooted_vertex_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication is the preceding invariant transport theorem. The reverse implication directly uses the existing reconstruction theorem rooted_vertex_equiv_of_branch_code_eq. The carrier universes and finiteness instances are independent; ambient cardinalities may differ.

Roots may be transient or periodic. A transient root's outgoing update may leave its descendant carrier, so this classification concerns the internal child relation. Global update conjugacy, directed cycle rotation, component multiplicities, actual depth truncation and naturality, cardinal-depth sufficiency, and compatible-family reconstruction remain separate obligations. The finite-realization domain of an unrestricted compatible family remains unresolved.

## References

- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexClassification.branch_code_eq_of_rooted_vertex_equiv`
- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexClassification.rooted_vertex_classification`
- Dependency: [D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction](RootedVertexReconstruction.md)
