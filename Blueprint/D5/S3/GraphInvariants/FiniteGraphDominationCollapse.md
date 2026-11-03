# Finite graph domination and elementary collapse

## Abstract

Simultaneous domination gives finite elementary collapses of the original labelled independence complex.

**Definition 1.1 (A codimension-one free pair).**

Lean statement: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.ElementaryCollapse`

*Formalization.* `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.ElementaryCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any vertex type V with decidable equality and pre-abstract complexes K,L on V, ElementaryCollapse(K,L) means that there are a nonempty finite face sigma of K and a vertex a absent from sigma, such that insert(a,sigma) is a face of K, every proper coface of sigma in K equals insert(a,sigma), and for every tau, tau is in L exactly when it is in K and equals neither of those two faces. The upper face has exactly one more vertex. Both complexes use nonempty faces and may omit ambient singleton faces.

**Definition 1.2 (Finite collapse sequences).**

Lean statement: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.Collapses`

*Formalization.* `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.Collapses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any decidable vertex type V, Collapses is Relation.ReflTransGen of ElementaryCollapse on PreAbstractSimplicialComplex V. Thus every sequence is finite, with the reflexive case allowing zero steps.

**Theorem 1.3 (Simultaneous open-neighborhood domination).**

Lean statement: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.domination_collapses`

*Proof.* Machine-checked in Lean as `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.domination_collapses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe u, finite type V : Type u with decidable equality, simple graph G on V, vertex a and finite set D of vertices, assume a is not in D and the open neighborhood of a is contained in that of each d in D. Then the underlying pre-abstract independence complex of G collapses to FiniteGraphVertexSubstitution.restricted(G, fun x => x not in D), on the original carrier V. No ordering or independence of D is assumed. The case D empty is the reflexive sequence.

Pair every independent face meeting D and omitting a with its insertion of a. If an edge from a reached a vertex of such a face, domination would give an edge from a deleted vertex already in the face; independence and looplessness exclude this, so the upper face is independent. Erasing a from an upper face still leaves a vertex of D and hence a nonempty lower face. The pairs are disjoint and exhaust exactly the faces meeting D.

At each stage keep a valid current pre-abstract complex and the finite family of remaining lower faces. Choose a lower face of maximum cardinality. A surviving proper coface cannot avoid a, since it would be a larger lower face; after erasing a, the same argument makes any coface containing a its designated upper face. Deleting exactly this pair preserves downward closure: a surviving face containing a deleted lower face would have to be the deleted upper face. Strong induction on the finite remaining family terminates after erasing one pair per step. The final face equality is the original-carrier restricted complex.

Elementary simplicial collapse and the domination argument are classical; no novelty is claimed. The source discussion C-28.8 and C-28.L in AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS gives a path free-coface deletion argument and cites Ehrenborg and Hetyei, The topology of the independence complex, European Journal of Combinatorics 27 (2006), 906-923, DOI 10.1016/j.ejc.2005.04.010, Section 2 and its path results. That discussion supplies motivation and classical attribution; it does not state this arbitrary simultaneous-deletion theorem. The present conclusion asserts the combinatorial collapse sequence, without a realization or forest classification.

## References

- Truth anchor: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.Collapses`
- Truth anchor: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.ElementaryCollapse`
- Truth anchor: `D5/S3/GraphInvariants/FiniteGraphDominationCollapse.domination_collapses`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](../Geometry/FiniteGraphVertexSubstitution.md)
