# Selected-cut cell machine and root-source support

## Abstract

NativeSelectedRA

**Definition 1.1 (Four-bit cells).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Cell`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence alphabet is Fin 16. Addresses are Boolean words, with false denoting L and true denoting R.

**Definition 1.2 (Constant complete root row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootBytes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootBytes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four cells 0,3,4,5 denote H, semicolon, exterior end and row end. The hole address is empty and its single partition class needs no off-diagonal bit.

**Definition 1.3 (Two-hole exterior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkPrefix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight cells 6,0,1,3,0,2,3,4 denote B, H L semicolon, H R semicolon and exterior end. The next cell is the sole off-diagonal partition bit and the last is row end.

**Definition 1.4 (Literal blocking exterior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.leafBytes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.leafBytes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cell for alpha is 7 and that for beta is 8. A literal leaf exterior is followed by exterior end and row end. Its empty hole partition needs no pair bit.

**Definition 1.5 (Private cell configuration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Work`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Work` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Work contains finite control in Fin 100, the guard address, the comparison operand, the candidate row and three reply latches. All address strings and row cells are explicit finite sequences.

**Definition 1.6 (Common private entry configuration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.emptyWork`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.emptyWork` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guard and operand are empty, the candidate has no cells and each reply latch is absent. Control starts at the root guard Read.

**Definition 1.7 (Entry, active work and ready boundary).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.State`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common entry contains no source information. Active stores the selected cut bit and Work. Ready stores the cut bit and row alone; it contains no Work, initial reply, attempt count or execution archive.

**Definition 1.8 (The selected cut).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cut`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True denotes the singleton root address. False denotes the two addresses L and R. The cut bit retained at Ready is the output cut itself.

**Definition 1.9 (One-cell retraction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pop`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pop removes the last cell of a finite region, leaving an empty region empty.

**Definition 1.10 (The last address letter).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lastBit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lastBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lastBit reads the last letter and returns false for an empty word.

**Definition 1.11 (Changing the operand base).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.switch`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.switch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

switch changes the first operand letter and leaves its relative suffix unchanged. The first letter selects L or R and is protected from relative traversal retraction.

**Definition 1.12 (Finite control change).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.go`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.go` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

go replaces the finite program counter and preserves every sequence and reply latch.

**Definition 1.13 (Candidate append).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.put`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.put` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

put appends one row cell and installs the indicated finite control.

**Definition 1.14 (Four concrete Read continuations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.PrivateInstruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.PrivateInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Private instruction data contain a literal address and four Work successors, one local Work successor, or private completion. Private completion is not outer Return.

**Definition 1.15 (Private local instruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.localInstruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.localInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This constructor records one local successor.

**Definition 1.16 (Literal Read instruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.receipt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.receipt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

receipt materializes its address and the alpha, beta, branch and absent continuation configurations.

**Definition 1.17 (Selected rereading acquisition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.privateStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.privateStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guard follows L after each branch until a leaf. The root cut writes its constant row. The two-child cut writes a literal root leaf or its two marked holes, then compares both hidden subtrees by relative preorder. Equal branches descend; equal leaves advance past completed subtrees; a mismatch appends false. The guard is reread at control 25. A changed reply clears the candidate and private data before retry. Acceptance retracts operand and guard cells, clears every reply latch and hands off the row.

**Definition 1.18 (Reply continuation selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.follow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.follow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

follow chooses the corresponding one of the four stored Work configurations.

**Definition 1.19 (Private continuation and outer control).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lift`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reads and local instructions preserve the selected output cut. Private completion produces a local transition to Ready with the existing row region.

**Definition 1.20 (One fixed source-blind transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.step`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry Reads the root and selects the root cut exactly for an alpha reply. Active executes privateStep and Ready emits the sole outer Return. No source, epoch, update bound or schedule is an argument of step.

**Definition 1.21 (Cut observation for the control invariant).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.selected`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proof-side observation is none at Entry and the selected cut bit at Active and Ready.

**Definition 1.22 (Independent writer bursts during cleanup).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanupTiming`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanupTiming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cleanupTiming n sigma contains n local events followed by one Return. Its event at index i has sigma i updates immediately before it. Sigma is a mathematical schedule annotation and is not a producer input.

**Theorem 1.23 (Every scheduled cleanup returns the whole ready state).**

$$\forall q: Bool, (\forall w: Work, (\forall sigma: Nat \to Nat, (\forall U: Source, (\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{active}\left(q, \operatorname{go}\left(40, w\right)\right), U, \operatorname{expand}\left(\operatorname{cleanupTiming}\left(\operatorname{length}\left(\operatorname{operand}\left(w\right)\right) + \operatorname{length}\left(\operatorname{guardPath}\left(w\right)\right) + 6, sigma\right)\right), \operatorname{ready}\left(q, \operatorname{row}\left(w\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanup_every_schedule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cleanup has operand length plus guard length plus six local events. Induction on the two lengths accounts for every cell retraction. Four final events reset the reply latches and hand off the row; two further events leave the exhausted retraction phases. Independent updates change only the source register, so arbitrary finite bursts may precede each local event and the separate Return. The entire terminal cell configuration is Ready q row.

**Definition 1.24 (Proof-side execution world).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.World`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.World` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

World pairs the observer configuration with the independently updated authentic source register and the external Return flag. Neither the source nor this flag is an argument of step or privateStep.

**Definition 1.25 (One actual event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.worldEvent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.worldEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A writer event applies substitution only to the authentic source. An observer event executes exactly step: a local successor, the authentic reply at its materialized address, or the separate Return. The returned execution world is absorbing.

**Definition 1.26 (An active execution schedule).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.trajectory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.trajectory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural index enumerates actual writer or observer events. Each event acts on the preceding complete world; idle waiting is excluded.

**Theorem 1.27 (The actual continuation of an event prefix).**

$$\forall s: Nat \to Bool, (\forall w: World, (\forall m: Nat, (\forall k: Nat, (\operatorname{trajectory}\left(s, w, m + k\right) = \operatorname{trajectory}\left(\operatorname{shift}\left(s, m\right), \operatorname{trajectory}\left(s, w, m\right), k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.trajectory_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every event schedule, whole initial world and natural m and k, the prefix of length m plus k is the shifted schedule's prefix of length k from the actual world at m. In the formula shift s m maps i to s applied to m plus i.

**Definition 1.28 (Every pending observer step executes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Progressing`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Progressing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every active index n where Return has not occurred, some observer event occurs at an index m at least n. No progress is required after Return.

**Theorem 1.29 (Cleanup returns on every progressing schedule).**

$$\forall q: Bool, (\forall w: Work, (\forall schedule: Nat \to Bool, (\forall U: Source, ((\operatorname{Progressing}\left(schedule, \operatorname{World}\left(\operatorname{active}\left(q, \operatorname{go}\left(40, w\right)\right), U, \operatorname{false}\left(\right)\right)\right)) \implies (\exists m: Nat, ((\operatorname{returned}\left(\operatorname{trajectory}\left(schedule, \operatorname{World}\left(\operatorname{active}\left(q, \operatorname{go}\left(40, w\right)\right), U, \operatorname{false}\left(\right)\right), m\right)\right) = \operatorname{true}\left(\right)) \land (\operatorname{config}\left(\operatorname{trajectory}\left(schedule, \operatorname{World}\left(\operatorname{active}\left(q, \operatorname{go}\left(40, w\right)\right), U, \operatorname{false}\left(\right)\right), m\right)\right) = \operatorname{ready}\left(q, \operatorname{row}\left(w\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanup_progressing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A progressing pending call has a first observer event after each of its finite prefixes. Before that event only writer updates occur and the private configuration is unchanged. Each local cleanup step therefore executes after a finite writer prefix. Induction on the counted cleanup sequence reaches Ready and its separate Return on every such schedule. No bound on interference, final source or schedule is supplied to the producer; this cleanup conclusion needs no finite-interference premise.

**Definition 1.30 (The root candidate phase).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootCandidate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootCandidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root phase appends H, semicolon, exterior end and row end in four successive cell events, after one control event. It preserves its guard and private reply latches.

**Definition 1.31 (Actual post-selection witnesses).**

$$\forall j: Nat, ((\operatorname{PostSelectionWitness}\left(j\right)) \iff (\exists g: Address, (\exists ell: Reply, (\exists a: Word, ((\neg (\operatorname{update}\left(\right) \in a)) \land (((ell = \operatorname{alpha}\left(\right)) \lor (ell = \operatorname{beta}\left(\right))) \land ((\operatorname{readout}\left(g, \operatorname{iterate}\left(\operatorname{substitution}\left(\right), j, \operatorname{of}\left(\operatorname{true}\left(\right)\right)\right)\right) = ell) \land (\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), \operatorname{of}\left(\operatorname{true}\left(\right)\right), \operatorname{cons}\left(\operatorname{observer}\left(\operatorname{read}\left(\operatorname{nil}\left(\right), \operatorname{alpha}\left(\right)\right)\right), \operatorname{append}\left(\operatorname{replicate}\left(j, \operatorname{update}\left(\right)\right), \operatorname{append}\left(a, \operatorname{cons}\left(\operatorname{observer}\left(\operatorname{read}\left(g, ell\right)\right), \operatorname{expand}\left(\operatorname{cleanupTiming}\left(\operatorname{length}\left(g\right) + 6, \operatorname{zeroSchedule}\left(\right)\right)\right)\right)\right)\right)\right), \operatorname{ready}\left(\operatorname{true}\left(\right), \operatorname{rootBytes}\left(\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.PostSelectionWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first Read is alpha at invocation alpha. Exactly j independent updates then occur before the quiescent acquisition prefix a. The final guard Read has its authentic leaf reply at the jth iterate of alpha. The displayed cleanup has zero bursts and ends in a separate Return. No guard or prefix is retained in the ready configuration. In the displayed formula zeroSchedule is the constant function with value zero.

**Theorem 1.32 (Exact root support and the blocked beta witness).**

$$(\forall u: Source, ((\exists h: Word, (\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), u, h, \operatorname{ready}\left(\operatorname{true}\left(\right), \operatorname{rootBytes}\left(\right)\right)\right))) \iff (u = \operatorname{of}\left(\operatorname{true}\left(\right)\right)))) \land ((\forall j: Nat, (\operatorname{PostSelectionWitness}\left(j\right))) \land ((\exists h: Word, ((\neg (\operatorname{update}\left(\right) \in h)) \land ((\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), \operatorname{of}\left(\operatorname{false}\left(\right)\right), h, \operatorname{ready}\left(\operatorname{false}\left(\right), \operatorname{leafBytes}\left(\operatorname{false}\left(\right)\right)\right)\right)) \land ((\operatorname{literalRecord}\left(\operatorname{cut}\left(\operatorname{false}\left(\right)\right), \operatorname{of}\left(\operatorname{false}\left(\right)\right)\right) = \operatorname{pair}\left(\operatorname{of}\left(\operatorname{inl}\left(\operatorname{false}\left(\right)\right)\right), \operatorname{emptyset}\left(\right)\right)) \land (\forall p: Address, ((p \in \operatorname{cut}\left(\operatorname{false}\left(\right)\right)) \implies ((\operatorname{IsPrefix}\left(\operatorname{nil}\left(\right), p\right)) \land ((p \neq \operatorname{nil}\left(\right)) \land (\operatorname{subtree}\left(p, \operatorname{of}\left(\operatorname{false}\left(\right)\right)\right) = \operatorname{none}\left(\right)))))))))) \land ((\forall h: Word, (\forall row: \operatorname{List}\left(Cell\right), (\neg (\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), \operatorname{of}\left(\operatorname{false}\left(\right)\right), h, \operatorname{ready}\left(\operatorname{true}\left(\right), row\right)\right))))) \land ((\forall u: Source, (\forall j: Nat, (\operatorname{literalRecord}\left(\operatorname{singleton}\left(\operatorname{nil}\left(\right)\right), \operatorname{iterate}\left(\operatorname{substitution}\left(\right), j, u\right)\right) = \operatorname{rootLabel}\left(\right)))) \land (\forall u: Source, (\forall h: Word, (\forall row: \operatorname{List}\left(Cell\right), ((\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), u, h, \operatorname{ready}\left(\operatorname{true}\left(\right), row\right)\right)) \implies (\exists tail: Word, (h = \operatorname{cons}\left(\operatorname{observer}\left(\operatorname{read}\left(\operatorname{nil}\left(\right), \operatorname{alpha}\left(\right)\right)\right), tail\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.selected_root_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut choice persists through every local step, Read and independent update. A root-selected return therefore requires an alpha first reply. No substitution image is alpha, so no update preceded that Read and the invocation source was alpha. The raw history starts with that alpha Read itself, with no preceding update. Conversely, a left-spine induction constructs the guard search on every finite source. Appending the constant root candidate, its validation and cleanup gives a witness after any supplied number j of post-selection updates. A quiescent beta invocation takes the two-address branch and returns the literal beta exterior with no holes. Its root beta leaf blocks both L and R. The same code cannot return any root-selected state from beta, although the semantic root row agrees for every finite source at every epoch.

**Definition 1.33 (A finite stationary prefix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Continues`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Continues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Continues U c d means that every returning execution from d on U can be preceded by a finite update-free word to give an execution from c on that same source. The prefix is proof-side data and is not retained by the machine.

**Theorem 1.34 (A stationary guard reaches an actual leaf).**

$$\forall U: Source, (\forall T: Source, (\forall q: Bool, (\forall p: Address, ((\forall z: Address, (\operatorname{readout}\left(\operatorname{append}\left(p, z\right), U\right) = \operatorname{readout}\left(z, T\right))) \implies (\exists g: Address, (\exists ell: Reply, (((ell = \operatorname{alpha}\left(\right)) \lor (ell = \operatorname{beta}\left(\right))) \land ((\operatorname{readout}\left(g, U\right) = ell) \land (\operatorname{Continues}\left(U, \operatorname{active}\left(q, \operatorname{guardEntry}\left(p\right)\right), \operatorname{active}\left(q, \operatorname{guardExit}\left(g, ell\right)\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.guard_search` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual read map at p is the complete finite tree T. In the formula guardEntry p is emptyWork with guardPath p, and guardExit g ell is emptyWork with control three, guardPath g and guardReply ell. Left-spine induction produces an alpha or beta reply at its actual materialized address g. A finite update-free prefix reaches control three with this guard address and reply, empty row and operand, and absent comparison latches.

**Definition 1.35 (Relative comparison entry).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairStart`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Control is twenty and the operand is L followed by the relative cursor z. All other Work fields are preserved.

**Definition 1.36 (Relative comparison exit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairDone`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairDone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Control is twenty seven and the operand is R followed by z. Both comparison latches contain the supplied leaf reply; all other regions are preserved.

**Definition 1.37 (Rightmost leaf label).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rightLeafReply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rightLeafReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Follow right children in a finite subtree until a leaf, and return its alpha or beta label.

**Theorem 1.38 (An equal stationary subtree scan).**

$$\forall U: Source, (\forall T: Source, (\forall w: Work, (\forall z: Address, ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{false}\left(\right), \operatorname{append}\left(z, a\right)\right), U\right) = \operatorname{readout}\left(a, T\right))) \implies ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{true}\left(\right), \operatorname{append}\left(z, a\right)\right), U\right) = \operatorname{readout}\left(a, T\right))) \implies (\operatorname{Continues}\left(U, \operatorname{active}\left(\operatorname{false}\left(\right), \operatorname{pairStart}\left(w, z\right)\right), \operatorname{active}\left(\operatorname{false}\left(\right), \operatorname{pairDone}\left(w, z, \operatorname{rightLeafReply}\left(T\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_equal_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every relative offset the two materialized base positions read the same supplied finite subtree T. The actual comparison from pairStart finishes at pairDone with the rightmost leaf label of T. Its finite stationary prefix composes with every later legal execution.

**Theorem 1.39 (An unequal stationary subtree scan).**

$$\forall U: Source, (\forall A: Source, (\forall B: Source, (\forall w: Work, (\forall z: Address, ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{false}\left(\right), \operatorname{append}\left(z, a\right)\right), U\right) = \operatorname{readout}\left(a, A\right))) \implies ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{true}\left(\right), \operatorname{append}\left(z, a\right)\right), U\right) = \operatorname{readout}\left(a, B\right))) \implies ((A \neq B) \implies (\exists v: Work, ((\operatorname{pc}\left(v\right) = 29) \land ((\operatorname{row}\left(v\right) = \operatorname{row}\left(w\right)) \land ((\operatorname{guardPath}\left(v\right) = \operatorname{guardPath}\left(w\right)) \land ((\operatorname{guardReply}\left(v\right) = \operatorname{guardReply}\left(w\right)) \land (\operatorname{Continues}\left(U, \operatorname{active}\left(\operatorname{false}\left(\right), \operatorname{pairStart}\left(w, z\right)\right), \operatorname{active}\left(\operatorname{false}\left(\right), v\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_unequal_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two actual read maps supply different finite subtrees. The comparison reaches control twenty nine while preserving the candidate row, guard address and guard reply. The equality test follows ordered children and reaches the first mismatch after any equal preceding subtree.

**Theorem 1.40 (Completion of a root comparison).**

$$\forall U: Source, (\forall A: Source, (\forall B: Source, (\forall w: Work, ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{false}\left(\right), a\right), U\right) = \operatorname{readout}\left(a, A\right))) \implies ((\forall a: Address, (\operatorname{readout}\left(\operatorname{cons}\left(\operatorname{true}\left(\right), a\right), U\right) = \operatorname{readout}\left(a, B\right))) \implies (\exists v: Work, ((\operatorname{pc}\left(v\right) = 8) \land ((\operatorname{row}\left(v\right) = \operatorname{append}\left(\operatorname{row}\left(w\right), \operatorname{cons}\left(\operatorname{ite}\left(A = B, 10, 9\right), \operatorname{nil}\left(\right)\right)\right)) \land ((\operatorname{guardPath}\left(v\right) = \operatorname{guardPath}\left(w\right)) \land ((\operatorname{guardReply}\left(v\right) = \operatorname{guardReply}\left(w\right)) \land (\operatorname{Continues}\left(U, \operatorname{active}\left(\operatorname{false}\left(\right), \operatorname{pairStart}\left(w, \operatorname{nil}\left(\right)\right)\right), \operatorname{active}\left(\operatorname{false}\left(\right), v\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting with the relative cursor empty, the comparison reaches control eight and appends ten exactly when the two supplied actual subtrees are equal, and nine otherwise. The guard address and saved guard reply are preserved.

**Definition 1.41 (Complete two-hole row meaning).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkRecord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exterior has holes L and R with their full native addresses. The partition contains both diagonal pairs; its bit specifies both off-diagonal memberships, so false retains both disequalities.

**Theorem 1.42 (Quiescent acquisition of both partition signs).**

$$\forall A: Source, (\forall B: Source, (\exists h: Word, ((\neg (\operatorname{update}\left(\right) \in h)) \land ((\operatorname{Run}\left(\operatorname{step}\left(\right), \operatorname{entry}\left(\right), \operatorname{mul}\left(A, B\right), h, \operatorname{ready}\left(\operatorname{false}\left(\right), \operatorname{append}\left(\operatorname{forkPrefix}\left(\right), \operatorname{cons}\left(\operatorname{ite}\left(A = B, 10, 9\right), \operatorname{cons}\left(5, \operatorname{nil}\left(\right)\right)\right)\right)\right)\right)) \land (\operatorname{literalRecord}\left(\operatorname{cut}\left(\operatorname{false}\left(\right)\right), \operatorname{mul}\left(A, B\right)\right) = \operatorname{forkRecord}\left(\operatorname{decide}\left(A = B\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.quiescent_two_hole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A structural induction follows the actual relative preorder comparison. Equal branches descend into their left children, advance to the right children and retract completed paths. Equal leaves finish their subtrees. Unequal constructors reach the mismatch phase immediately; equal left subtrees followed by unequal right subtrees do so after the left traversal. The candidate contains exactly the two marked holes and the resulting equality or disequality bit. The same invocation searches its root guard, writes every exterior cell, performs the comparison, validates the saved guard, clears the private regions and Returns from Ready.

These statements concern the explicit cell-transition model. They establish root support, actual quiescent acquisition for both cuts and scheduled cleanup. They do not establish all-return correctness of the two-hole comparison, universal finite-interference liveness of acquisition, or a finite-bit realization accounting for binary heads, extents, capacities and permissions. A realization with additional accessible state must include that state and its paid cleanup.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Cell`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Continues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.PostSelectionWitness`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.PrivateInstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Progressing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.State`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.Work`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.World`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanupTiming`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanup_every_schedule`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cleanup_progressing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.cut`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.emptyWork`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.follow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.forkRecord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.go`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.guard_search`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lastBit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.leafBytes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.lift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.localInstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairDone`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pairStart`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_complete`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_equal_scan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pair_unequal_scan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.pop`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.privateStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.put`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.quiescent_two_hole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.receipt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rightLeafReply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootBytes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.rootCandidate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.selected`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.selected_root_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.step`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.switch`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.trajectory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.trajectory_add`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.worldEvent`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber](NativeFiveHoleFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution](NativeIndependentExecution.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates](../SourceCoordinates/IntrinsicSubstitutionCoordinates.md)
