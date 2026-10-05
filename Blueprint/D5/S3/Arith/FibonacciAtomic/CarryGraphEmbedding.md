# Canonical Embedding in the Original Carry Graph

## Abstract

Positive real laws enter the original bounded carry graph with exact minimum-anchor and tail-cost values.

**Definition 1.1 (State coordinates).**

$$State = (\mathbb{Z}, \mathbb{Z})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state has integer fields r and e. The graph bounds are imposed by IsState; raw coordinate pairs need not obey them.

**Definition 1.2 (Column parameters).**

$$Action = (\mathbb{Z}, \mathbb{Z}, \mathbb{Z})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An action has integer fields b, h and c, in that order. Its bit is b, h counts departures from the anchor equality group, and c counts larger-prefix labels taking a one.

**Definition 1.3 (Bounded graph states).**

$$(\forall m: \mathbb{N}, (\forall s: State, \operatorname{IsState}\left(m, s\right) \iff (0 \le \operatorname{r}\left(s\right) \land \operatorname{r}\left(s\right) \le m - 1 \land 1 \le \operatorname{e}\left(s\right) \land \operatorname{e}\left(s\right) \le m)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer pair with residual width between zero and m-1 and equality-group size between one and m belongs to the graph.

**Definition 1.4 (Root).**

$$(\forall m: \mathbb{N}, \operatorname{root}\left(m\right) = (1, m))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For m at least two the root is a graph state: one continuing cylinder and all m labels equal at depth zero.

**Definition 1.5 (One-label count).**

$$(\forall s: State, (\forall a: Action, ((\operatorname{b}\left(a\right) = 1 \Rightarrow \operatorname{ones}\left(s, a\right) = \operatorname{e}\left(s\right) + \operatorname{c}\left(a\right)) \land (\operatorname{b}\left(a\right) \neq 1 \Rightarrow \operatorname{ones}\left(s, a\right) = \operatorname{h}\left(a\right) + \operatorname{c}\left(a\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.ones` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-bit row emits e+c one-labels. Every other raw bit value uses h+c; legal actions restrict the bit to zero or one.

**Definition 1.6 (Successor).**

$$(\forall s: State, (\forall a: Action, \operatorname{successor}\left(s, a\right) = (2 \operatorname{r}\left(s\right) - \operatorname{ones}\left(s, a\right), \operatorname{e}\left(s\right) - \operatorname{h}\left(a\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor subtracts the column's one-label count from twice the residual and removes h labels from the equality group.

**Definition 1.7 (Two legal action rows).**

$$(\forall m: \mathbb{N}, (\forall s: State, (\forall a: Action, \operatorname{Legal}\left(m, s, a\right) \iff (\operatorname{IsState}\left(m, s\right) \land ((\operatorname{b}\left(a\right) = 1 \land \operatorname{h}\left(a\right) = 0 \land 0 \le \operatorname{c}\left(a\right) \land \operatorname{c}\left(a\right) \le m - \operatorname{e}\left(s\right)) \lor (\operatorname{b}\left(a\right) = 0 \land 0 \le \operatorname{h}\left(a\right) \land \operatorname{h}\left(a\right) \le \operatorname{e}\left(s\right) - 1 \land 0 \le \operatorname{c}\left(a\right) \land \operatorname{c}\left(a\right) \le m - \operatorname{e}\left(s\right))) \land \operatorname{IsState}\left(m, \operatorname{successor}\left(s, a\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A legal action satisfies exactly one displayed bit row and has a bounded successor. The equality-group bounds on the successor also follow from the row's inequalities; writing them explicitly identifies both endpoints as graph states.

**Definition 1.8 (Infinite columns).**

$$Path = (\mathbb{N} \to State, \mathbb{N} \to Action)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path carries two sequences, state and action. Index d names the state at depth d and the action producing the next bit at depth d+1.

**Definition 1.9 (Legal root paths).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, \operatorname{IsRootPath}\left(m, gamma\right) \iff (\operatorname{state}\left(gamma, 0\right) = \operatorname{root}\left(m\right) \land (\forall d: \mathbb{N}, (\operatorname{Legal}\left(m, \operatorname{state}\left(gamma, d\right), \operatorname{action}\left(gamma, d\right)\right) \land \operatorname{state}\left(gamma, d + 1\right) = \operatorname{successor}\left(\operatorname{state}\left(gamma, d\right), \operatorname{action}\left(gamma, d\right)\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsRootPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every column has a legal action and its recorded next state is that action's successor, starting from the root.

**Definition 1.10 (Anchor series).**

$$(\forall gamma: Path, \operatorname{anchorValue}\left(gamma\right) = \sum_{d \in \mathbb{N}}\frac{\operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right)}{2^{d + 1}})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.anchorValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchor value is the real infinite sum of column bits, with column zero weighted by one half. This convention includes terminating binary expansions. An unsummable real series on an arbitrary raw path has the totalized value zero.

**Definition 1.11 (Residual tail cost).**

$$(\forall gamma: Path, \operatorname{pathCost}\left(gamma\right) = \sum_{d \in \mathbb{N}}\frac{\operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right)}{2^{d}})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.pathCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost is the real infinite sum of normalized residual widths, including the depth-zero term. These whole-column quantities do not charge r separate reads in a machine step. An unsummable series on a raw path has the totalized value zero.

**Theorem 1.12 (Complete canonical embedding).**

$$(\forall m: \mathbb{N}, (2 \le m \Rightarrow ((\forall s: State, (\operatorname{IsState}\left(m, s\right) \Rightarrow (\exists a: Action, \operatorname{Legal}\left(m, s, a\right)))) \land (\forall s: State, (\forall a: Action, (\operatorname{r}\left(s\right) = 0 \Rightarrow (\operatorname{Legal}\left(m, s, a\right) \Rightarrow (\operatorname{b}\left(a\right) = 0 \land \operatorname{h}\left(a\right) = 0 \land \operatorname{c}\left(a\right) = 0 \land \operatorname{successor}\left(s, a\right) = s))))) \land (\forall s: State, (\forall a: Action, (\operatorname{e}\left(s\right) = 1 \Rightarrow (\operatorname{Legal}\left(m, s, a\right) \Rightarrow \operatorname{h}\left(a\right) = 0)))) \land (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, ((\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \Rightarrow (\sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(i\right) = 1 \Rightarrow (\forall k: \operatorname{Fin}\left(m\right), ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(k\right) \le \operatorname{p}\left(i\right)) \Rightarrow (\exists gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \land (\forall d: \mathbb{N}, \operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right) = \operatorname{R}\left(p, d\right)) \land (\forall d: \mathbb{N}, \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) = \operatorname{card}\left(\{i \in \operatorname{Fin}\left(m\right)\mid\left\lfloor2^{d} \operatorname{p}\left(i\right)\right\rfloor = \left\lfloor2^{d} \operatorname{p}\left(k\right)\right\rfloor\}\right)) \land (\forall d: \mathbb{N}, \operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right) = \left\lfloor2^{d + 1} \operatorname{p}\left(k\right)\right\rfloor - 2 \left\lfloor2^{d} \operatorname{p}\left(k\right)\right\rfloor) \land \operatorname{anchorValue}\left(gamma\right) = \operatorname{p}\left(k\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{L}\left(p\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=2, each graph state has a legal action. At residual zero the only legal action has b=h=c=0 and leaves the state fixed. At equality-group size one every legal action has h=0.

Let p be any strictly positive real probability vector, and choose any index k minimizing p. Write n(i,d)=floor(2^d p(i)) and a(i,d)=n(i,d+1)-2n(i,d). The path has r(d)=R(p,d), e(d) equal to the number of indices with n(i,d)=n(k,d), and anchor bit a(k,d). Its anchor value is p(k), hence the smallest probability, and its tail cost is the existing dyadic cost L(p). No rationality, distinctness or computability hypothesis is used.

Minimum-prefix monotonicity and the zero-or-one digit bounds show that a label with strictly larger old prefix has strictly larger next prefix. Equal-prefix labels taking a different bit therefore leave permanently. When the anchor bit is one, minimum-prefix order forces every equal-prefix label to take one. When it is zero, fewer than e equal-prefix labels depart because the anchor stays. Counting these departures and the larger-prefix one-labels gives exactly the two legal action rows. The floor remainder bounds supply the residual interval, and the canonical binary expansion reconstructs the minimum atom.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsRootPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Legal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Path`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.State`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.anchorValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.ones`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.pathCost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.successor`
- Dependency: [D5/S1/Digit/RadixFloorDigit](../../../S1/Digit/RadixFloorDigit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
