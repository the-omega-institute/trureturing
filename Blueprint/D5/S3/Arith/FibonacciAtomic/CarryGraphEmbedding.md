# Original Carry Graph and Fixed Tree Layers

## Abstract

Bounded carry states and fixed label intervals determine exact continuing and stopping tree layers.

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

**Definition 1.12 (Fixed labels).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, (\forall i: \operatorname{Fin}\left(m\right), i \in \operatorname{labelSet}\left(m, gamma, d\right) \iff ((\operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right) = 1 \land i < \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) + \operatorname{c}\left(\operatorname{action}\left(gamma, d\right)\right)) \lor (\operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right) \neq 1 \land \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) - \operatorname{h}\left(\operatorname{action}\left(gamma, d\right)\right) \le i \land i < \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) + \operatorname{c}\left(\operatorname{action}\left(gamma, d\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.labelSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices are zero-based. On an anchor-one column the selected labels start at zero. On an anchor-zero column they start at e-h and stop before e+c.

**Definition 1.13 (Ordered children).**

$$(\forall words: \operatorname{List}\left(\operatorname{List}\left(Bool\right)\right), \operatorname{children}\left(words\right) = \operatorname{flatMap}\left((w \mapsto [\operatorname{append}\left(w, [false]\right), \operatorname{append}\left(w, [true]\right)]), words\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.children` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each word contributes first its false child and then its true child, preserving parent order.

**Definition 1.14 (Continuing words).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, \operatorname{continuing}\left(m, gamma, d + 1\right) = \operatorname{drop}\left(\operatorname{length}\left(\operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right)\right), \operatorname{children}\left(\operatorname{continuing}\left(m, gamma, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.continuing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth zero consists of the empty word. Every later level expands the continuing parents and removes the initial children assigned to labels.

**Definition 1.15 (Labelled stopping words).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, \operatorname{stopping}\left(m, gamma, d\right) = \operatorname{zip}\left(\operatorname{children}\left(\operatorname{continuing}\left(m, gamma, d\right)\right), \operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.stopping` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected initial children are paired with the increasing output labels. The zip has the shorter of the two input lengths.

**Theorem 1.16 (Exact continuing and stopping layers).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \Rightarrow ((\forall d: \mathbb{N}, \operatorname{length}\left(\operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right)\right) = \operatorname{ones}\left(\operatorname{state}\left(gamma, d\right), \operatorname{action}\left(gamma, d\right)\right)) \land (\forall d: \mathbb{N}, (\operatorname{length}\left(\operatorname{continuing}\left(m, gamma, d\right)\right) = \operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right) \land \operatorname{Nodup}\left(\operatorname{continuing}\left(m, gamma, d\right)\right) \land (\forall w: \operatorname{List}\left(Bool\right), (w \in \operatorname{continuing}\left(m, gamma, d\right) \Rightarrow \operatorname{length}\left(w\right) = d)))) \land (\forall d: \mathbb{N}, (\operatorname{map}\left(snd, \operatorname{stopping}\left(m, gamma, d\right)\right) = \operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right) \land \operatorname{Nodup}\left(\operatorname{stopping}\left(m, gamma, d\right)\right) \land (\forall w: \operatorname{Product}\left(\operatorname{List}\left(Bool\right), \operatorname{Fin}\left(m\right)\right), (w \in \operatorname{stopping}\left(m, gamma, d\right) \Rightarrow \operatorname{length}\left(\operatorname{fst}\left(w\right)\right) = d + 1))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.tree_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m and legal root path, the number of selected labels is the column's one-label count. At depth d the continuing list has exactly r(d) distinct words, each of length d. The stopping list pairs distinct words of length d+1 with every selected label in increasing order.

The label interval has e+c entries on an anchor-one column and h+c entries on an anchor-zero column. Doubling the continuing parents and removing that interval leaves exactly the successor residual width. Induction also preserves distinctness and word length. The scan and fair-bit law use these exact tree layers.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsRootPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.IsState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Legal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.Path`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.State`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.anchorValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.children`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.continuing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.labelSet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.ones`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.pathCost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.stopping`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.successor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.tree_layers`
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
