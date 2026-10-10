# Canonical Carry Embedding and Boundary Completeness

## Abstract

Canonical binary digits embed every positive normalized real law into the original carry graph.

All labels belong to Fin m. The integer prefix at depth d is floor(2^d p(i)); the next digit is the depth-(d+1) prefix minus twice the depth-d prefix. Indicator takes the integer value one when its argument holds and zero otherwise. State, Action, Legal, successor, IsRootPath, anchorValue and pathCost are the original carry-graph objects. The function cost is the dyadic residual tail sum. Natural powers and cardinalities in integer state fields use their canonical integer casts.

**Definition 1.1 (Floor states).**

$$(\forall m: \mathbb{N}, (\forall p: (\operatorname{Fin}\left(m\right) \to \mathbb{R}), (\forall k: \operatorname{Fin}\left(m\right), (\forall d: \mathbb{N}, \operatorname{canonicalState}\left(p, k, d\right) = (2^{d} - \sum_{i \in \operatorname{Fin}\left(m\right)}\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor, \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{indicator}\left(\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor = \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate is the integer dyadic residual. The second counts the labels with the same floor prefix as label k, including k itself.

**Definition 1.2 (Canonical digit actions).**

$$(\forall m: \mathbb{N}, (\forall p: (\operatorname{Fin}\left(m\right) \to \mathbb{R}), (\forall k: \operatorname{Fin}\left(m\right), (\forall d: \mathbb{N}, \operatorname{canonicalAction}\left(p, k, d\right) = (\lfloor2^{d + 1} \cdot \operatorname{p}\left(k\right)\rfloor - 2 \cdot \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor, \operatorname{if}\left(\lfloor2^{d + 1} \cdot \operatorname{p}\left(k\right)\rfloor - 2 \cdot \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor = 1, 0, \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{if}\left(\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor = \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor, \lfloor2^{d + 1} \cdot \operatorname{p}\left(i\right)\rfloor - 2 \cdot \lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor, 0\right)\right), \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{if}\left(\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor = \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor, 0, \lfloor2^{d + 1} \cdot \operatorname{p}\left(i\right)\rfloor - 2 \cdot \lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchor digit determines the action row. For an anchor zero, h counts the one-digits in the equality group; for an anchor one, h is zero. The coordinate c counts the one-digits outside that group.

**Definition 1.3 (One common-law path).**

$$(\forall m: \mathbb{N}, (\forall p: (\operatorname{Fin}\left(m\right) \to \mathbb{R}), (\forall k: \operatorname{Fin}\left(m\right), \operatorname{canonicalPath}\left(p, k\right) = ((d \mapsto \operatorname{canonicalState}\left(p, k, d\right)), (d \mapsto \operatorname{canonicalAction}\left(p, k, d\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path consists of the floor state and digit action at each natural depth, both computed from the same real vector and the same anchor label.

**Theorem 1.4 (All real laws and both boundaries).**

$$(\forall m: \mathbb{N}, (2 \le m \to ((\forall s: State, (\operatorname{IsState}\left(m, s\right) \to (\exists a: Action, \operatorname{Legal}\left(m, s, a\right)))) \land (\forall s: State, (\forall a: Action, (\operatorname{Legal}\left(m, s, a\right) \to (\operatorname{r}\left(s\right) = 0 \to (\operatorname{b}\left(a\right) = 0 \land \operatorname{h}\left(a\right) = 0 \land \operatorname{c}\left(a\right) = 0 \land \operatorname{successor}\left(s, a\right) = s))))) \land (\forall s: State, (\forall a: Action, (\operatorname{Legal}\left(m, s, a\right) \to (\operatorname{e}\left(s\right) = 1 \to \operatorname{h}\left(a\right) = 0)))) \land (\forall p: (\operatorname{Fin}\left(m\right) \to \mathbb{R}), ((\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \to (\sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(i\right) = 1 \to (\exists k: \operatorname{Fin}\left(m\right), ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(k\right) \le \operatorname{p}\left(i\right)) \land (\exists gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \land \operatorname{anchorValue}\left(gamma\right) = \operatorname{p}\left(k\right) \land \operatorname{anchorValue}\left(gamma\right) = \operatorname{sInf}\left(\operatorname{range}\left(p\right)\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{cost}\left(p\right) \land (\forall d: \mathbb{N}, \operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right) = 2^{d} - \sum_{i \in \operatorname{Fin}\left(m\right)}\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor) \land (\forall d: \mathbb{N}, \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) = \operatorname{card}\left(\{i \in \operatorname{Fin}\left(m\right)\mid\lfloor2^{d} \cdot \operatorname{p}\left(i\right)\rfloor = \lfloor2^{d} \cdot \operatorname{p}\left(k\right)\rfloor\}\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

For every m at least two, every state has a legal action. At zero residual the only legal action has b=h=c=0 and returns to the same state; all subsequent residual charges vanish. If the equality group has one label then h=0 for every legal action.

Every strictly positive normalized real vector has a smallest coordinate k. Its canonical path starts at (1,m), preserves that minimum as its anchor value, has exactly the dyadic cost, and retains the displayed floor residual and equality-group size at every depth. The same k and the same path work for all depths.

A positive prefix difference cannot return to zero after doubling and adding the next digit difference. If the anchor digit is one, every still-equal label also has digit one. If the anchor digit is zero, exactly the still-equal labels with digit one depart. These facts give e(d+1)=e(d)-h(d), while the complete column digit count gives the residual successor. Floor bounds give legal states and action ranges. The canonical binary series recovers the anchor mass; the cost equality follows term by term from the residual identity.

Terminating binary coordinates, ties for the smallest mass and noncomputable real vectors are included. No rationality, distinctness or effective-computation assumption is imposed. Lumbroso's presentation of Knuth-Yao DDG supplies background for the existing dyadic cost expression; the carry-graph embedding is the present mathematical relation. Existence of the infinite path gives no finite effective algorithm for arbitrary real input.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.canonicalState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding](../CarryGraphEmbedding.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](../OptimalLawStrictSlope.md)
