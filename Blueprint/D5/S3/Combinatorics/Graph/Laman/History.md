# The complete finite Henneberg characterization

## Abstract

Let V be any finite vertex type in any universe and G a simple graph on V. The additive Laman counts characterize an actual finite list of legal Henneberg moves starting with K2. No embedding or geometric placement is required.

**Definition 1.1 (Canonical graph states).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/History.State`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/History.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ruth Haas, David Orden, Günter Rote, Francisco Santos, Brigitte Servatius, Herman Servatius, Diane Souvaine, Ileana Streinu, Walter Whiteley (2003). *Planar Minimally Rigid Graphs and Pseudo-Triangulations*. DOI: [10.1016/j.comgeo.2004.07.003](https://doi.org/10.1016/j.comgeo.2004.07.003). URL: <https://arxiv.org/abs/math/0307347v1>.

*Commentary.*

A state is a natural number n together with a simple graph on Fin n. There is no upper bound on n. Any graph on a finite type, in any universe, is transported to such a state by its finite enumeration isomorphism.

**Definition 1.2 (The initial edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/History.base`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/History.base` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ruth Haas, David Orden, Günter Rote, Francisco Santos, Brigitte Servatius, Herman Servatius, Diane Souvaine, Ileana Streinu, Walter Whiteley (2003). *Planar Minimally Rigid Graphs and Pseudo-Triangulations*. DOI: [10.1016/j.comgeo.2004.07.003](https://doi.org/10.1016/j.comgeo.2004.07.003). URL: <https://arxiv.org/abs/math/0307347v1>.

*Commentary.*

The base state is n=2 with the complete graph on Fin 2. The reflexive relation closure admits this graph with zero moves.

**Definition 1.3 (Independently guarded legal operations).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/History.Legal`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/History.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ruth Haas, David Orden, Günter Rote, Francisco Santos, Brigitte Servatius, Herman Servatius, Diane Souvaine, Ileana Streinu, Walter Whiteley (2003). *Planar Minimally Rigid Graphs and Pseudo-Triangulations*. DOI: [10.1016/j.comgeo.2004.07.003](https://doi.org/10.1016/j.comgeo.2004.07.003). URL: <https://arxiv.org/abs/math/0307347v1>.

*Commentary.*

A legal step s to t has either two distinct old vertices a,b and an isomorphism from typeI(s.graph,a,b) to t.graph, or three old vertices a,b,c with an actual edge ab, a!=b, c!=a, c!=b and an isomorphism from typeII(s.graph,a,b,c) to t.graph. Legality does not mention Laman counts. Composing Option.some with the isomorphism gives an injective old-vertex embedding. The image of none is the unique fresh vertex, because every Option value is either none or some old vertex. Type I preserves every old adjacency and joins precisely the two selected old vertices. Type II deletes precisely the selected actual edge, preserves every other old adjacency, and joins precisely the three selected old vertices. These conclusions follow from the exhaustive Option adjacency equations of the move definitions.

**Definition 1.4 (An actual finite legal list).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/History.HasHistory`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/History.HasHistory` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ruth Haas, David Orden, Günter Rote, Francisco Santos, Brigitte Servatius, Herman Servatius, Diane Souvaine, Ileana Streinu, Walter Whiteley (2003). *Planar Minimally Rigid Graphs and Pseudo-Triangulations*. DOI: [10.1016/j.comgeo.2004.07.003](https://doi.org/10.1016/j.comgeo.2004.07.003). URL: <https://arxiv.org/abs/math/0307347v1>.

*Commentary.*

HasHistory G means there is a finite list l of canonical states such that base::l is a Legal chain and G is isomorphic to its last graph. For l empty, that endpoint is base itself. No history is assumed in the counting-to-history direction.

**Theorem 1.5 (Laman counts if and only if a finite legal history exists).**

$$\forall V \in Type,\; [\operatorname{Finite}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; ((\operatorname{edgeCount}\left(G\right) + 3 = 2 \cdot \operatorname{card}\left(V\right)) \land (\forall S \in \operatorname{Set}\left(V\right),\; (2 \le \operatorname{card}\left(S\right)) \Rightarrow (\operatorname{edgeCount}\left(\operatorname{induce}\left(G, S\right)\right) + 3 \le 2 \cdot \operatorname{card}\left(S\right)))) \Leftrightarrow (\exists l \in \operatorname{List}\left(State\right),\; (\operatorname{IsChain}\left(Legal, \operatorname{Cons}\left(base, l\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{GraphIso}\left(G, \operatorname{graph}\left(\operatorname{Last}\left(\operatorname{Cons}\left(base, l\right)\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/History.laman_iff_history` (`✓ std3`). ∎

*Citation.* Ruth Haas, David Orden, Günter Rote, Francisco Santos, Brigitte Servatius, Herman Servatius, Diane Souvaine, Ileana Streinu, Walter Whiteley (2003). *Planar Minimally Rigid Graphs and Pseudo-Triangulations*. DOI: [10.1016/j.comgeo.2004.07.003](https://doi.org/10.1016/j.comgeo.2004.07.003). URL: <https://arxiv.org/abs/math/0307347v1>.

*Commentary.*

Write e(G) for the number of unordered edges, card(V) for the finite vertex count, and G[S] for the induced graph on S. The left side requires e(G)+3=2 card(V) and, for every S with card(S)>=2, e(G[S])+3<=2 card(S). The equality already forces at least two vertices, so the Lean statement also covers the empty and singleton vertex types without an extra hypothesis.

Completeness uses strong induction on the actual vertex cardinality. At cardinality two, tightness identifies G with K2. Otherwise the credited safe-repair theorem supplies a degree-two deletion or a degree-three deletion with a safe actual nonedge bridge. Both smaller graphs are Laman. The induction hypothesis supplies their actual histories; reconstruction identifies G with the corresponding Option operation. Transport the smaller endpoint through its graph isomorphism, append the guarded legal step, and enumerate the new finite vertex type by Fin. The strict subtype cardinality decrease proves termination. The standard reflexive-transitive-closure/list-chain theorem then produces the required finite list.

Soundness starts from the Laman K2 base and propagates the count invariant along the actual legal chain. Type I preservation and the credited Type II proof of every induced-subset inequality handle the two step cases; endpoint isomorphism transports the result back to G. The final conversion between finite subsets and arbitrary induced vertex sets preserves their exact edge counts. This is the known general Henneberg characterization; the receiving contribution is a complete finite-history construction from the credited repair and preservation proof source.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/History.HasHistory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/History.Legal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/History.State`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/History.base`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/History.laman_iff_history`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Moves](Moves.md)
