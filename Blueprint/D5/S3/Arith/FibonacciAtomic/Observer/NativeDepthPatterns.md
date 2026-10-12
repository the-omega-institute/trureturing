# NativeDepthPatterns

## Abstract

NativeDepthPatterns

**Theorem 1.1 (Originally present subtree transport).**

$$\forall n: Nat, (\forall a: Address, (\forall u, t: Source, ((\operatorname{subtree}\left(a, u\right) = \operatorname{some}\left(t\right)) \implies (\operatorname{subtree}\left(a, \operatorname{iterate}\left(substitution, n, u\right)\right) = \operatorname{some}\left(\operatorname{iterate}\left(substitution, n, t\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.original_present_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epoch, an originally present subtree is transported to its iterated native substitution at the same original address. There is no unconditional Option.map law at originally absent addresses; substitution can create physical descendants below original leaves.

**Theorem 1.2 (All-epoch original-prefix locality).**

$$\forall n: Nat, (\forall s: Address, (\forall u, v: Source, ((\forall a: Address, ((\operatorname{length}\left(a\right) \leq \operatorname{length}\left(s\right)) \implies (\operatorname{readout}\left(a, u\right) = \operatorname{readout}\left(a, v\right)))) \implies (\operatorname{readout}\left(s, \operatorname{iterate}\left(substitution, n, u\right)\right) = \operatorname{readout}\left(s, \operatorname{iterate}\left(substitution, n, v\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.original_prefix_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SLH.74.7 holds for every natural epoch, including zero, and every physical address, including addresses originally absent and later born. The proof follows the original path, then evolves the first original leaf. Pair preservation directly applies Function.Semiconj₂.iterate.

**Definition 1.3 (Finite reached-frontier patterns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Pattern`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Pattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero depth the whole source is one hole. At positive depth an original leaf terminates the branch, while an original pair exposes two shallower patterns. The recursive Fintype instance enumerates precisely these finite possibilities.

**Definition 1.4 (Actual frontier variable positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Frontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Frontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unit supplies the reached depth-zero position. An early leaf supplies the empty type. An ordered pair supplies the disjoint sum of its child frontiers. Thus names are positions, not values and not a hidden inequality requirement.

**Definition 1.5 (Unrestricted native fillings).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.fill`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.fill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every variable receives an arbitrary finite nonempty Boolean free tree. Different positions may receive the same tree. No finite tree universe or source-size bound is imposed.

**Definition 1.6 (Unique decomposition and reconstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.depthEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.depthEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence constructs the unique pattern and its actual frontier subtrees, with inverse fill. This retains every filling and every original tree, including zero variables.

**Theorem 1.7 (All and only reached depth positions).**

$$\forall d: Nat, (\forall p: \operatorname{Pattern}\left(d\right), ((\forall x: \operatorname{Frontier}\left(p\right), (\operatorname{length}\left(\operatorname{frontierAddress}\left(p, x\right)\right) = d)) \land (\forall f: \operatorname{Frontier}\left(p\right) \to Source, (\forall x: \operatorname{Frontier}\left(p\right), (\operatorname{subtree}\left(\operatorname{frontierAddress}\left(p, x\right), \operatorname{fill}\left(p, f\right)\right) = \operatorname{some}\left(\operatorname{f}\left(x\right)\right)))) \land (\forall f: \operatorname{Frontier}\left(p\right) \to Source, (\forall a: Address, ((\operatorname{length}\left(a\right) = d) \implies ((\operatorname{isSome}\left(\operatorname{subtree}\left(a, \operatorname{fill}\left(p, f\right)\right)\right)) \iff (\exists x: \operatorname{Frontier}\left(p\right), (\operatorname{frontierAddress}\left(p, x\right) = a))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.frontier_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each frontier name has address length d and recovers its assigned actual subtree. Conversely, at every length-d address, presence after filling is equivalent to that address naming a frontier variable. Early original leaves remain absence guards.

**Definition 1.8 (Complete mixed-epoch history).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Consistent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Consistent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each listed event uses the actual iterated substitution and four-valued reply. Repeated events remain conjuncts, and absent replies have the native presence guard. Inconsistent lists remain valid inputs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Consistent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.Pattern`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.depthEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.frontier_geometry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.original_prefix_locality`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.original_present_transport`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder](ActualCutPartitionDecoder.md)
