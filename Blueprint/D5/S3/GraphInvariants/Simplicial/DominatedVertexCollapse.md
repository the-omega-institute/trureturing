# Relative dominated-vertex collapse

## Abstract

Deleting a dominated vertex of a finite simplicial complex is a relative collapse.

**Definition 1.1 (Deleting a simplex).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.deletion`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.deletion` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Deletion, free pairs and elementary simplicial collapses in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

The deletion of a finite vertex set consists of the original faces that do not contain that set. Faces are nonempty finite sets. Deleting a singleton therefore retains exactly the faces avoiding its vertex.

**Definition 1.2 (A free face and its unique proper coface).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.IsFreePair`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.IsFreePair` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Deletion, free pairs and elementary simplicial collapses in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

Both faces belong to the complex, the lower face is properly contained in the upper face, and every face containing the lower one equals one of these two. Thus removing the pair leaves a subcomplex.

**Definition 1.3 (One elementary collapse).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.ElementaryCollapsesTo`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.ElementaryCollapsesTo` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Deletion, free pairs and elementary simplicial collapses in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

There is a free pair whose lower-face deletion is exactly the endpoint. The four definitions follow TauCetiProject/TauCeti at revision 64bb4d871548995899dee90beda88b787fafe27d, in LinkStar, ElementaryCollapse and Collapse/Basic. The Tau Ceti contributors' Apache 2.0 license is retained in docs/reports/polarization-suppliers/tauceti-LICENSE.txt.

**Definition 1.4 (Finite collapse sequences).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.CollapsesTo`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.CollapsesTo` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Deletion, free pairs and elementary simplicial collapses in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

The reflexive transitive closure of elementary collapse allows a finite sequence of moves, including the empty sequence.

**Theorem 1.5 (A dominated vertex can be deleted by elementary collapses).**

$$\forall V : Type, [\operatorname{DecidableEq}(V)] \forall K : \operatorname{PreAbstractSimplicialComplex}(V), (\operatorname{Finite}(\operatorname{faces}(K))) \Rightarrow \forall v : V, \forall w : V, (v \neq w) \Rightarrow (\forall A : \operatorname{Finset}(V), (A \in K) \Rightarrow (v \in A) \Rightarrow \operatorname{insert}(w, A) \in K) \Rightarrow \operatorname{CollapsesTo}(K, \operatorname{deletion}(K, \{v\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.collapsesTo_deletion_of_vertex_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient vertex type is arbitrary, and only the face family is finite. Distinct vertices v and w satisfy domination when adjoining w to every face containing v gives another face. No face containing v is required to exist; the empty complex and an absent v give an empty collapse sequence.

Among faces containing v and avoiding w, choose an inclusion maximal face A. A coface avoiding w equals A by maximality. A coface containing w has a nonempty face obtained by erasing w; maximality identifies that face with A. Thus the only proper coface is the face obtained by adjoining w.

Deleting this free pair preserves domination and preserves the final deletion of v. The number of faces strictly decreases, so induction supplies a finite sequence. If no eligible face remains, even the singleton at v is absent. Every face avoiding v survives every move.

For the independence complex of the path on N plus three vertices, with N at least one, use the one-based labels v equal to N plus one and w equal to N plus three. A face containing v avoids N plus two, the only neighbour of w, so the domination condition holds. On Fin of N plus three the same labels are N and N plus two. This gives the collapse to the exact deletion of v. Identifying that deletion with a join, transferring collapse to geometric realization, and deriving suspension and the classification by residue modulo three are separate assertions. The empty geometric realization is distinct from the empty probability pattern, and no physical operation follows from the combinatorial statement.

## References

- Truth anchor: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.CollapsesTo`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.ElementaryCollapsesTo`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.IsFreePair`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.collapsesTo_deletion_of_vertex_domination`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.deletion`
