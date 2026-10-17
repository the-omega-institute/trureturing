# Native scanner frontiers

## Abstract

Actual cursors remain meaningful during independent source substitution.

The source register is an arbitrary finite ordered binary tree. A writer event substitutes every leaf while leaving the observer's whole configuration unchanged. An observer event executes one actual read, one private instruction or the separate Return. The schedule may interleave these events at every instruction.

**Definition 1.1 (Two existing positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairPresent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairPresent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a relative cursor z, both positions Lz and Rz have nonabsent replies in the current source.

**Definition 1.2 (Two branch positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairBranch`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both positions Lz and Rz are current branches. Either common child extends the relative cursor to two existing positions.

**Definition 1.3 (A saved reply under substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Saved`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Saved` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A saved reply is nonabsent, and a saved branch still denotes a branch at its original address. A saved leaf label need not equal the current reply.

**Definition 1.4 (Empty guard-search workspace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.GuardFresh`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.GuardFresh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The candidate row and comparison operand are empty, and all three reply latches are absent. The guard address and finite control are separate fields.

**Definition 1.5 (Concrete phase conditions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Frontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Frontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Guard search reads an existing address and descends only after a branch. Comparison phases distinguish the left and right base cells, existing paired positions, saved replies and branch positions before descent. An upward cursor may name a completed subtree whose leaves have since grown. Cleanup records the regions and latches already cleared; reset reaches an empty guard address before starting the next search. The error control numbered ninety nine is excluded.

**Definition 1.6 (The whole configuration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Safe`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Safe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry and ready configurations satisfy the condition. An active configuration satisfies exactly its current source dependent frontier condition.

**Theorem 1.7 (Every actual prefix has a valid frontier).**

$$\forall u: \operatorname{Source}, (\forall s: \operatorname{Nat} \to \operatorname{Bool}, (\forall n: \operatorname{Nat}, (\operatorname{Safe}\left(\operatorname{source}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right), \operatorname{config}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right)\right) \land (\forall q: \operatorname{Bool}, (\forall r: \operatorname{Work}, ((\operatorname{config}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right) = \operatorname{active}\left(q, r\right)) \implies (\operatorname{control}\left(r\right) \neq 99)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.reachable_scan_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source, schedule and finite prefix, the actual register and configuration satisfy Safe. Every active configuration therefore has control different from ninety nine. The induction follows actual writer and observer events. Existing addresses and branches survive substitution. The comparison can descend only through two saved branches; upward retraction exposes a parent branch before the sibling switch.

**Definition 1.8 (A finite stationary comparison continuation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.ScanFinishes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.ScanFinishes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The current whole configuration has a finite update-free continuation to an active Work configuration at control eight. The continuation composes with every subsequent returning execution. It preserves the actual current source; it imposes no bound on tree size, cursor length or earlier interference.

**Definition 1.9 (A finite stationary return).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Halts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Halts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is an update-free legal execution from the whole current configuration to a state at its separate Return. The finite word and end state are proof-side witnesses.

**Theorem 1.10 (Resuming every reachable comparison phase).**

$$\forall u: \operatorname{Source}, (\forall s: \operatorname{Nat} \to \operatorname{Bool}, (\forall n: \operatorname{Nat}, (\operatorname{Safe}\left(\operatorname{source}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right), \operatorname{config}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right)\right) \land (\forall q: \operatorname{Bool}, (\forall r: \operatorname{Work}, ((\operatorname{config}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right) = \operatorname{active}\left(q, r\right)) \implies ((\operatorname{control}\left(r\right) \in [20,21,22,23,24,26,27,28,31]) \implies \operatorname{ScanFinishes}\left(\operatorname{source}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right), \operatorname{active}\left(q, r\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.reachable_scan_frontier_progress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite actual prefix has a safe frontier. If its control is twenty, twenty one, twenty two, twenty three, twenty four, twenty six, twenty seven, twenty eight or thirty one, its comparison resumes to control eight on the actual current source. A saved branch remains an actual branch after substitution, so an interrupted read pair can safely finish its decision. The stationary equal and unequal subtree scans handle each pending subtree. Reverse induction on the cursor handles upward retraction and the next right sibling. This conclusion concerns the comparison phase; guard search, validation, retry and final handoff are separate phases.

**Theorem 1.11 (Return under every finite active interference schedule).**

$$\forall u: \operatorname{Source}, (\forall s: \operatorname{Nat} \to \operatorname{Bool}, (\operatorname{Finite}\left(\{n:\operatorname{Nat} \Vert \operatorname{apply}\left(s, n\right) = \operatorname{true} \land \operatorname{returned}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right) = \operatorname{false}\}\right) \implies (\exists m:\operatorname{Nat}, \operatorname{returned}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), m\right)\right) = \operatorname{true})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.finite_interference_terminates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every initial finite source and every active event schedule, finiteness of writer events before Return implies that Return occurs. After the last such update, the proof continues from the actual interrupted configuration. It finishes any pending comparison, guard search, body, validation or cleanup. A failed validation executes the original row, operand and guard retraction loops before a fresh attempt on the stationary source. That attempt validates and returns. In this active event model, finite writer interference already ensures that pending observer events execute; no idle events or runtime bound are supplied to the observer.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.GuardFresh`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Halts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairBranch`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.PairPresent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Safe`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.Saved`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.ScanFinishes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.finite_interference_terminates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.reachable_scan_frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.reachable_scan_frontier_progress`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA](../NativeSelectedRA.md)
