# Spanning cycles in semicomplete directed relations

## Abstract

Spanning cycles in semicomplete directed relations

**Theorem 1.1 (A change of orientation gives an insertion edge).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall D \in \operatorname{Relation}\left(V\right),\; \forall c \in V,\; \forall x \in V,\; \forall l \in \operatorname{List}\left(V\right),\; \left(\left(\forall v \in V,\; v \in \operatorname{cons}\left(c, l\right) \Rightarrow \left(\operatorname{apply}\left(D, v, x\right) \lor \operatorname{apply}\left(D, x, v\right)\right)\right) \land \left(\left(\exists v \in V,\; v \in \operatorname{cons}\left(c, l\right) \land \operatorname{apply}\left(D, v, x\right)\right) \land \left(\exists v \in V,\; v \in \operatorname{cons}\left(c, l\right) \land \operatorname{apply}\left(D, x, v\right)\right)\right)\right) \Rightarrow \left(\exists p \in \operatorname{List}\left(V\right),\; \exists u \in V,\; \exists v \in V,\; \exists s \in \operatorname{List}\left(V\right),\; \operatorname{append}\left(\operatorname{cons}\left(c, l\right), \operatorname{singleton}\left(c\right)\right) = \operatorname{append}\left(p, \operatorname{cons}\left(u, \operatorname{cons}\left(v, s\right)\right)\right) \land \left(\operatorname{apply}\left(D, u, x\right) \land \operatorname{apply}\left(D, x, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.cyclic_insertion` (`✓ std3`). ∎

*Citation.* Jørgen Bang-Jensen and Gregory Gutin (2009). *Digraphs — Theory, Algorithms and Applications*. DOI: [10.1007/978-1-84800-998-1](https://doi.org/10.1007/978-1-84800-998-1). URL: <https://link.springer.com/book/10.1007/978-1-84800-998-1>.

*Commentary.*

For the cyclic list c::l, suppose every vertex is comparable with x, and there are both incoming and outgoing arcs at x. Then a consecutive cyclic pair u,v satisfies D(u,x) and D(x,v). No simplicity or irreflexivity is needed for this split.

**Theorem 1.2 (Outside vertices have a uniform orientation).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall D \in \operatorname{Relation}\left(V\right),\; \forall c \in V,\; \forall x \in V,\; \forall l \in \operatorname{List}\left(V\right),\; \left(\left(\forall v \in V,\; v \in \operatorname{cons}\left(c, l\right) \Rightarrow \left(\operatorname{apply}\left(D, v, x\right) \lor \operatorname{apply}\left(D, x, v\right)\right)\right) \land \left(\neg \left(\exists p \in \operatorname{List}\left(V\right),\; \exists u \in V,\; \exists v \in V,\; \exists s \in \operatorname{List}\left(V\right),\; \operatorname{append}\left(\operatorname{cons}\left(c, l\right), \operatorname{singleton}\left(c\right)\right) = \operatorname{append}\left(p, \operatorname{cons}\left(u, \operatorname{cons}\left(v, s\right)\right)\right) \land \left(\operatorname{apply}\left(D, u, x\right) \land \operatorname{apply}\left(D, x, v\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall v \in V,\; v \in \operatorname{cons}\left(c, l\right) \Rightarrow \left(\operatorname{apply}\left(D, v, x\right) \land \left(\neg \operatorname{apply}\left(D, x, v\right)\right)\right)\right) \lor \left(\forall v \in V,\; v \in \operatorname{cons}\left(c, l\right) \Rightarrow \left(\operatorname{apply}\left(D, x, v\right) \land \left(\neg \operatorname{apply}\left(D, v, x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.outside_uniform_of_no_insertion` (`✓ std3`). ∎

*Citation.* Jørgen Bang-Jensen and Gregory Gutin (2009). *Digraphs — Theory, Algorithms and Applications*. DOI: [10.1007/978-1-84800-998-1](https://doi.org/10.1007/978-1-84800-998-1). URL: <https://link.springer.com/book/10.1007/978-1-84800-998-1>.

*Commentary.*

If there is no such insertion edge, comparability forces every vertex of the cyclic list to point to x with every reverse arc absent, or forces x to point to every vertex with every reverse arc absent. Reciprocal arcs are allowed by the ambient relation; the absent directions are consequences of failed insertion.

**Theorem 1.3 (A simple spanning directed cycle through any vertex).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{DecidableEq}\left(V\right)], \forall S \in \operatorname{Finset}\left(V\right),\; \forall D \in \operatorname{Relation}\left(V\right),\; \forall a \in V,\; \left(\left(\forall s \in V,\; \forall t \in V,\; \operatorname{apply}\left(D, s, t\right) \Rightarrow \left(s \in S \land t \in S\right)\right) \land \left(2 \le \operatorname{card}\left(S\right) \land \left(\left(\forall s \in V,\; \forall t \in V,\; \left(s \in S \land \left(t \in S \land s \ne t\right)\right) \Rightarrow \left(\operatorname{apply}\left(D, s, t\right) \lor \operatorname{apply}\left(D, t, s\right)\right)\right) \land \left(\left(\forall s \in V,\; \forall t \in V,\; \left(s \in S \land t \in S\right) \Rightarrow \operatorname{ReflTransGen}\left(D, s, t\right)\right) \land a \in S\right)\right)\right)\right) \Rightarrow \left(\exists l \in \operatorname{List}\left(V\right),\; \operatorname{Nodup}\left(\operatorname{cons}\left(a, l\right)\right) \land \left(\operatorname{toFinset}\left(\operatorname{cons}\left(a, l\right)\right) = S \land \left(2 \le \operatorname{length}\left(\operatorname{cons}\left(a, l\right)\right) \land \operatorname{IsChain}\left(D, \operatorname{append}\left(\operatorname{cons}\left(a, l\right), \operatorname{singleton}\left(a\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.finite_semicomplete_hamilton` (`✓ std3`). ∎

*Citation.* Jørgen Bang-Jensen and Gregory Gutin (2009). *Digraphs — Theory, Algorithms and Applications*. DOI: [10.1007/978-1-84800-998-1](https://doi.org/10.1007/978-1-84800-998-1). URL: <https://link.springer.com/book/10.1007/978-1-84800-998-1>.

*Commentary.*

S is a finite vertex set of size at least two. Every D arc has both endpoints in S. Distinct vertices of S are comparable, and every ordered pair is joined by an actual ReflTransGen D path. The result enumerates every vertex exactly once and closes by one further occurrence of the specified a. Directed two-cycles and arbitrary reciprocal arcs are included.

Erase loops from a return path to obtain an initial simple cycle. Maximize its length among the finitely bounded simple cycles. A one-vertex insertion would increase that length. The uniform-orientation lemma therefore partitions outside vertices into receiving and sending classes. Strong connectivity gives a first exit from the cycle and then an actual receiving-to-sending outside arc. Splicing those two distinct outside vertices into a cycle edge increases the length. Thus the maximal cycle spans S; literal rotation places a first.

The original-coordinate port construction applies this theorem to the reverse of its actual blue-target arc relation. The longest-cycle argument is classical; this presentation makes no graph-theory novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.cyclic_insertion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.finite_semicomplete_hamilton`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.outside_uniform_of_no_insertion`
