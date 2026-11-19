# Unique directed path order of a component

## Abstract

Each weak component of a finite acyclic partial permutation has a unique exhaustive directed path enumeration, including isolated singletons.

**Theorem 1.1 (Consecutive indices are exactly the directed edges).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall E \in \operatorname{Relation}\left(V\right),\; \left(\operatorname{RightUnique}\left(E\right) \land \left(\operatorname{LeftUnique}\left(E\right) \land \operatorname{Acyclic}\left(E\right)\right)\right) \Rightarrow \left(\forall A \in \operatorname{Component}\left(E\right),\; \exists e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right), \operatorname{ComponentFiber}\left(E, A\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right),\; \operatorname{E}\left(\operatorname{value}\left(\operatorname{apply}\left(e, i\right)\right), \operatorname{value}\left(\operatorname{apply}\left(e, j\right)\right)\right) \Leftrightarrow \operatorname{add}\left(\operatorname{val}\left(i\right), 1\right) = \operatorname{val}\left(j\right)\right) \land \left(\forall f \in \operatorname{Equiv}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right), \operatorname{ComponentFiber}\left(E, A\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{ComponentFiber}\left(E, A\right)\right)\right),\; \operatorname{E}\left(\operatorname{value}\left(\operatorname{apply}\left(f, i\right)\right), \operatorname{value}\left(\operatorname{apply}\left(f, j\right)\right)\right) \Leftrightarrow \operatorname{add}\left(\operatorname{val}\left(i\right), 1\right) = \operatorname{val}\left(j\right)\right) \Rightarrow f = e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/DirectedForestPathOrder.component_path_order` (`✓ std3`). ∎

*Citation.* Boaz Tsaban (2003). *Permutation graphs, fast forward permutations, and sampling the cycle structure of a permutation*. DOI: [10.1016/S0196-6774(03)00017-8](https://doi.org/10.1016/S0196-6774(03)00017-8).

*Commentary.*

Let V be any finite type. Let E be right-unique, meaning at most one outgoing neighbor, and left-unique, meaning at most one incoming neighbor. Acyclic means that Relation.TransGen E is irreflexive. For every A in Component E, the fiber is literally the subtype {x : V // Quotient.mk (EqvGen.setoid E) x = A}, with no supplied path data or chosen representative. There exists a unique equivalence e from Fin(Nat.card(ComponentFiber E A)) onto that fiber such that E (e i).val (e j).val holds if and only if i.val+1=j.val, for all i and j. The formula expands unique existence as existence together with equality of every competing enumeration.

The equivalence exhausts the actual component and repeats no vertex. No lower bound on the number of components is assumed. An isolated component has a one-point fiber, its unique enumeration, and no consecutive indices, hence no edge. The empty ambient carrier has no component A.

The proof reuses DirectedForestCompletion.full_cycle_completion_equiv only to select the already-proved tail of A and its membership, then applies the original path_to_tail lemma to both actual vertices. Reversing those paths and using Mathlib's total_of_right_unique with LeftUnique E as right uniqueness of swap E makes directed reachability total on the fiber. Acyclicity and transitivity make it a strict total order. Mathlib's monoEquivOfFin supplies its increasing finite enumeration.

An E-edge cannot skip an intermediate reachability position. The first edge of any path from its source is the prescribed successor by right uniqueness; an intermediate path back to the edge's target would then form a nonempty directed cycle. Conversely, split a path between consecutive order positions at its first edge. Its first successor belongs to the same actual fiber. If it differed from the target, its index would lie strictly between consecutive natural numbers. This proves both directions of exact adjacency.

For uniqueness, compose a competing path enumeration with the inverse of the constructed one. Each consecutive pair maps to a consecutive pair by their two adjacency laws. Mathlib's Fin.strictMono_iff_lt_succ and StrictMono.eq_id show that this self-map of the finite linear order is the identity, hence the two equivalences agree.

This formalizes the directed path-component clause of the classical partial-permutation picture in Tsaban, Section 1, Lemma 1.1, pages 107–108. The citation supplies mathematical lineage; no literature priority is claimed. Counts and probability laws are separate conclusions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/DirectedForestPathOrder.component_path_order`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion](DirectedForestCompletion.md)
