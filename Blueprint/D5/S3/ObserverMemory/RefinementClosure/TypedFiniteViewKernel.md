# Typed finite path views and stable refinement

## Abstract

Typed partial labelled path views refine to full behavior at any plateau.

The types, their state and readout spaces, the named edges between types, and each edge's label space are arbitrary. Each edge responds partially with a label and a state of its target type. An absent response is illegality, not an extra state. No finiteness, decidable equality, or totality assumption is imposed.

A path is a composable word of named edges in execution order. Its response is absent if any edge is illegal; otherwise it contains the complete ordered tuple of edge labels and the terminal typed readout. The finite view records responses to every path up to its depth, including every prefix and the empty path. The complete behavior records all finite paths. Both retain the starting type as a separate tag.

The refinement relation is defined independently: depth zero requires equal type tags and roots; the next depth additionally requires simultaneous legality for every named outgoing edge and, when legal, equal labels and successors related at the preceding depth.

**Theorem 1.1 (Finite views, intersection, and permanent stability).**

$$(\forall I: Type, (\forall Edge: I \to \left(I \to Type\right), (\forall Label: (\forall i, j: I, \operatorname{Edge}\left(i, j\right) \to Type), (\forall S, O: I \to Type, (\forall q: (\forall i: I, \operatorname{S}\left(i\right) \to \operatorname{O}\left(i\right)), (\forall step: (\forall i, j: I, (\forall e: \operatorname{Edge}\left(i, j\right), \operatorname{S}\left(i\right) \to \operatorname{Option}\left((\operatorname{Label}\left(e\right) \times \operatorname{S}\left(j\right))\right))), (\forall n: \mathbb{N}, (\forall s, t: \Sigma i: I, \operatorname{S}\left(i\right), \operatorname{E}\left(Label, q, step, n, s, t\right) \Leftrightarrow \operatorname{finiteView}\left(Label, q, step, n, s\right)=\operatorname{finiteView}\left(Label, q, step, n, t\right))) \land\\{}(\forall n: \mathbb{N}, (\forall s, t: \Sigma i: I, \operatorname{S}\left(i\right), \operatorname{E}\left(Label, q, step, (n+1), s, t\right) \Rightarrow \operatorname{E}\left(Label, q, step, n, s, t\right))) \land\\{}(\operatorname{behaviorKernel}\left(Label, q, step\right)=(\lambda s, t: \Sigma i: I, \operatorname{S}\left(i\right) \mapsto (\forall n: \mathbb{N}, \operatorname{E}\left(Label, q, step, n, s, t\right)))) \land\\{}(\forall n: \mathbb{N}, (\operatorname{E}\left(Label, q, step, n\right)=\operatorname{E}\left(Label, q, step, (n+1)\right)) \Rightarrow (\operatorname{E}\left(Label, q, step, n\right)=\operatorname{behaviorKernel}\left(Label, q, step\right) \land (\forall k: \mathbb{N}, \operatorname{E}\left(Label, q, step, (n+k)\right)=\operatorname{E}\left(Label, q, step, n\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.typed_finite_view_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the full disjoint union of states, refinement at any depth is exactly equality of the corresponding finite views. Each next relation is contained in the previous one, and equality of complete behavior is their intersection.

If two consecutive refinement relations coincide at one depth, that relation already equals the complete behavior kernel. Every later relation equals it as well. This is a conditional stability certificate and does not assert that a plateau exists.

Induction on depth splits nonempty paths at their first edge. One-edge responses recover legality and the first label; removing that label from longer responses recovers every successor path response. Restricting lengths gives descent, and each finite path belongs to its own length bound. Equality of consecutive relations propagates through the recurrence, so the path characterization identifies the plateau with complete behavior.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.typed_finite_view_kernel`
