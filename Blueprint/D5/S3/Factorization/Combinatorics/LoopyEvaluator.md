# The Concrete Loopy Evaluator

## Abstract

A concrete labelled evaluator realizes the ordinary Loopy polynomial and its source recursion laws.

A pending edge is an ordered endpoint pair used to encode an undirected edge occurrence. The edge list retains parallel occurrences. A self-pair is a pending loop, and the separate accumulator stores loops already consumed by the recursion. The definitions below all belong to this source module even though Lean uses the shared LoopyDegreeSequence namespace.

**Definition 1.1 (Pending edge occurrences).**

$$Edge = Nat \times Nat$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

Edge is Nat x Nat. The two coordinates are endpoint labels; orientation is representation data, not graph data.

**Definition 1.2 (The ordinary Loopy polynomial ring).**

$$LoopyPolynomial = \operatorname{MvPolynomial}\left(Nat, \operatorname{Polynomial}\left(Int\right)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.LoopyPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

LoopyPolynomial is the multivariate polynomial ring, indexed by natural loop counts, over univariate integer polynomials in the deletion variable.

**Definition 1.3 (Valid finite graph encodings).**

$$\operatorname{Valid}\left(V, E, ell\right) = (\forall e \in E, (\operatorname{fst}\left(e\right) \in V) \land (\operatorname{snd}\left(e\right) \in V)) \land (\forall v, (\neg v \in V) \Rightarrow (\operatorname{ell}\left(v\right) = 0))$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

Valid V E ell says that both endpoints of every occurrence in E lie in V and that ell is zero outside V. It imposes no simplicity, connectedness, nonemptiness or looplessness condition.

**Definition 1.4 (Contract one endpoint label).**

$$\operatorname{contractVertex}\left(a, b, v\right) = if v = b then a else v$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

contractVertex a b sends b to a and fixes every other label.

**Definition 1.5 (Contract a pending occurrence).**

$$\operatorname{contractEdge}\left(a, b, e\right) = (\operatorname{contractVertex}\left(a, b, \operatorname{fst}\left(e\right)\right), \operatorname{contractVertex}\left(a, b, \operatorname{snd}\left(e\right)\right))$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

contractEdge applies contractVertex a b to both endpoints, so remaining parallel copies and loops are transported occurrence by occurrence.

**Definition 1.6 (Accumulate one pending loop).**

$$\operatorname{addLoop}\left(ell, a\right) = \operatorname{update}\left(ell, a, \operatorname{ell}\left(a\right) + 1\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.addLoop` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

addLoop ell a updates only coordinate a from ell(a) to ell(a)+1.

**Definition 1.7 (Merge loop data during contraction).**

$$\operatorname{contractLoops}\left(ell, a, b, v\right) = if v=a then \operatorname{ell}\left(a\right) + \operatorname{ell}\left(b\right) + 1 else if v=b then 0 else \operatorname{ell}\left(v\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractLoops` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

contractLoops ell a b puts ell(a)+ell(b)+1 at a, puts zero at discarded label b, and fixes all other coordinates. The added one retains the selected nonloop edge occurrence as a loop.

**Definition 1.8 (Relabel one pending occurrence).**

$$\operatorname{relabelEdge}\left(f, e\right) = (\operatorname{f}\left(\operatorname{fst}\left(e\right)\right), \operatorname{f}\left(\operatorname{snd}\left(e\right)\right))$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.relabelEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

relabelEdge transports both endpoints along an ambient permutation.

**Definition 1.9 (Relabel accumulated loops).**

$$\operatorname{relabelLoops}\left(f, ell, v\right) = \operatorname{ell}\left(f^{-1}\left(v\right)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.relabelLoops` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

relabelLoops transports the accumulator contravariantly along the same permutation.

**Definition 1.10 (Combine disjoint loop accumulators).**

$$\operatorname{unionLoops}\left(ellone, elltwo, v\right) = \operatorname{ellone}\left(v\right) + \operatorname{elltwo}\left(v\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.unionLoops` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

unionLoops is pointwise addition; Valid and disjointness ensure that it represents the disjoint union.

**Definition 1.11 (Deletion-contraction on occurrences).**

$$\operatorname{loopyAux}\left(V, nil, ell\right) = \prod_{v \in V} \operatorname{X}\left(\operatorname{ell}\left(v\right)\right), \operatorname{loopyAux}\left(V, \operatorname{cons}\left((a, b), E\right), ell\right) = if a=b then \operatorname{loopyAux}\left(V, E, \operatorname{addLoop}\left(ell, a\right)\right) else \operatorname{loopyAux}\left(\operatorname{erase}\left(V, b\right), \operatorname{map}\left(\operatorname{contractEdge}\left(a, b\right), E\right), \operatorname{contractLoops}\left(ell, a, b\right)\right) + \operatorname{C}\left(t\right) \cdot \operatorname{loopyAux}\left(V, E, ell\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopyAux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

With no pending edges, loopyAux is the product over all retained vertices of x indexed by the accumulated loop count, including x_0 for an isolate. A pending loop is moved into the accumulator. A selected nonloop contributes the sum of its contraction branch and t times its deletion branch; contraction erases the second vertex and retains the selected occurrence as an accumulated loop.

**Definition 1.12 (The concrete ordinary Loopy evaluator).**

$$\operatorname{loopy}\left(V, E, ell\right) = \operatorname{loopyAux}\left(V, E, ell\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

loopy is loopyAux with the same finite carrier, occurrence list and loop accumulator; its default accumulator is identically zero.

**Theorem 1.13 (Representation independence and the seven evaluator laws).**

$$(\forall f: \operatorname{EquivPerm}\left(Nat\right), \forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \operatorname{loopy}\left(\operatorname{map}\left(\operatorname{toEmbedding}\left(f\right), V\right), \operatorname{map}\left(\operatorname{relabelEdge}\left(f\right), E\right), \operatorname{relabelLoops}\left(f, ell\right)\right) = \operatorname{loopy}\left(V, E, ell\right)) \land ((\forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \forall a: Nat, \forall b: Nat, (\operatorname{Valid}\left(V, \operatorname{cons}\left((a, b), E\right), ell\right)) \Rightarrow (\operatorname{loopy}\left(V, \operatorname{cons}\left((a, b), E\right), ell\right) = \operatorname{loopy}\left(V, \operatorname{cons}\left((b, a), E\right), ell\right))) \land ((\forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \forall e: Edge, \forall f: Edge, (\operatorname{Valid}\left(V, \operatorname{cons}\left(e, \operatorname{cons}\left(f, E\right)\right), ell\right)) \Rightarrow (\operatorname{loopy}\left(V, \operatorname{cons}\left(e, \operatorname{cons}\left(f, E\right)\right), ell\right) = \operatorname{loopy}\left(V, \operatorname{cons}\left(f, \operatorname{cons}\left(e, E\right)\right), ell\right))) \land ((\forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \forall a: Nat, \operatorname{loopy}\left(V, \operatorname{cons}\left((a, a), E\right), ell\right) = \operatorname{loopy}\left(V, E, \operatorname{addLoop}\left(ell, a\right)\right)) \land ((\forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall Eprime: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, (\operatorname{Perm}\left(E, Eprime\right)) \Rightarrow ((\operatorname{Valid}\left(V, E, ell\right)) \Rightarrow (\operatorname{loopy}\left(V, E, ell\right) = \operatorname{loopy}\left(V, Eprime, ell\right)))) \land ((\forall V: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall R: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \forall e: Edge, (\operatorname{Perm}\left(E, \operatorname{cons}\left(e, R\right)\right)) \Rightarrow ((\operatorname{Valid}\left(V, E, ell\right)) \Rightarrow (\operatorname{loopy}\left(V, E, ell\right) = if \operatorname{fst}\left(e\right)=\operatorname{snd}\left(e\right) then \operatorname{loopy}\left(V, R, \operatorname{addLoop}\left(ell, \operatorname{fst}\left(e\right)\right)\right) else \operatorname{loopy}\left(\operatorname{erase}\left(V, \operatorname{snd}\left(e\right)\right), \operatorname{map}\left(\operatorname{contractEdge}\left(\operatorname{fst}\left(e\right), \operatorname{snd}\left(e\right)\right), R\right), \operatorname{contractLoops}\left(ell, \operatorname{fst}\left(e\right), \operatorname{snd}\left(e\right)\right)\right) + \operatorname{C}\left(t\right) \cdot \operatorname{loopy}\left(V, R, ell\right)))) \land (\forall Vone: \operatorname{Finset}\left(Nat\right), \forall Vtwo: \operatorname{Finset}\left(Nat\right), \forall Eone: \operatorname{List}\left(Edge\right), \forall Etwo: \operatorname{List}\left(Edge\right), \forall ellone: Nat \to Nat, \forall elltwo: Nat \to Nat, (\operatorname{Disjoint}\left(Vone, Vtwo\right)) \Rightarrow ((\operatorname{Valid}\left(Vone, Eone, ellone\right)) \Rightarrow ((\operatorname{Valid}\left(Vtwo, Etwo, elltwo\right)) \Rightarrow (\operatorname{loopyAux}\left(\operatorname{union}\left(Vone, Vtwo\right), \operatorname{append}\left(Eone, Etwo\right), \operatorname{unionLoops}\left(ellone, elltwo\right)\right) = \operatorname{loopyAux}\left(Vone, Eone, ellone\right) \cdot \operatorname{loopyAux}\left(Vtwo, Etwo, elltwo\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

The seven visible clauses are: permutation relabelling invariance; endpoint-orientation invariance under Valid; adjacent occurrence exchange under Valid; pending-loop transfer; invariance under any list permutation under Valid; the arbitrary selected-occurrence loop/deletion-contraction recurrence; and multiplication on disjoint unions. These clauses formalize Definition 1.1 and Proposition 2.1 in the labelled list representation. The proof of their representation bridge is repository-derived.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.Edge`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.LoopyPolynomial`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.Valid`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.addLoop`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractEdge`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractLoops`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.contractVertex`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopyAux`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy_spec`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.relabelEdge`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.relabelLoops`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyEvaluator.unionLoops`
