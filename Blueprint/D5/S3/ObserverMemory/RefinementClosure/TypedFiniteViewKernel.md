# Typed finite path views and stable refinement

## Abstract

Typed partial labelled path views refine to full behavior at any plateau.

The types, their state and readout spaces, the named edges between types, and each edge's label space are arbitrary. Each edge responds partially with a label and a state of its target type. An absent response is illegality, not an extra state. No finiteness, decidable equality, or totality assumption is imposed.

A path is a composable word of named edges in execution order. Its response is absent if any edge is illegal; otherwise it contains the complete ordered tuple of edge labels and the terminal typed readout. The finite view records responses to every path up to its depth, including every prefix and the empty path. The complete behavior records all finite paths. Both retain the starting type as a separate tag.

The refinement relation is defined independently: depth zero requires equal type tags and roots; the next depth additionally requires simultaneous legality for every named outgoing edge and, when legal, equal labels and successors related at the preceding depth.

For a complete response contract, an alternative trace retains the readout at every cut. Its empty trace is the current readout. At a nonempty word it pairs that readout with an absent tag if the first operation is illegal, or with the actual first record and the recursively obtained suffix trace when the operation is legal. Thus an illegal suffix keeps the earlier readouts and records and stops at the first missing transition. A continuing failure remains a legal transition with its failure and reason in the record. Terminal outcomes are represented by declared terminal types on which all operations are absent. Operation parameters remain part of the named edge. Readouts and records retain every source, permission, archive and calibration field required by the fixed contract. Omitting a field in a later projection does not erase a record already retained by that contract.

Equality of these complete traces for all finite words is exactly equality of complete behavior here. In one direction, erase the earlier cut readouts from each trace to obtain the successful label tuple and terminal readout, or absence. In the other direction, use the finite refinement relation at the word's length: its root equality gives the first cut, its one-step clause gives simultaneous legality and the same record, and its successor clause gives the remaining trace. The outer type tag is retained in both presentations. No bound on state fibers, word length or branching is needed.

Take the quotient separately in each actual state fiber by this complete response equality, and then take the disjoint typed union. A partial named operation descends by mapping a legal successor to its quotient class and retaining its actual record. The refinement clause proves that this partial map is independent of the representative, including whether it is absent. A graph arrow consists of a legal name at the source residual and its determined target residual. Different names remain different arrows, even when their endpoints coincide.

Every such arrow lifts from every actual representative of its source residual, with the same record and the stipulated successor class. Induction on a composable graph word therefore lifts the whole word from one fixed initial representative, keeping an actual intermediate state at every prefix. The state images are the original fibers; the trace tuples are outputs of these states, with no assumption that independently possible record fields can be jointly realized. Empty fibers are allowed, and the chosen initial state supplies the inhabited starting fiber.

This response correspondence supplies a representative-independent legal graph. It places no finiteness or recurrence condition on that graph and gives no cycle criterion for reconstructing the chronological word from a final residual and an additive duration. Duration must itself descend, either because it is a declared record field or by a separate hypothesis with one common unit and calibration.

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
