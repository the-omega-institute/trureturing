# Independent writer execution and native constraints

## Abstract

NativeIndependentExecution

**Definition 1.1 (Source-blind observer microsteps).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Op`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Op` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transition delta receives only the accessible configuration C. It produces one local successor, one fully materialized literal address with four continuations, or Return. A local calculation can take arbitrarily many such steps. Return hands off the whole current configuration, including all accessible control and storage distinctions represented by C.

**Definition 1.2 (All observer events).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.ObserverEvent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.ObserverEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite event word retains every local microstep, each literal address and supplied four-valued reply, and a separate Return.

**Definition 1.3 (Independent updates and observer events).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Event`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Event` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An active event is one writer substitution or one observer event. Idle waiting and unobservable writer bookkeeping are outside this word.

**Definition 1.4 (Finite active raw words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Word`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Word is the chronological list of all active events, with no quotient by update placement.

**Definition 1.5 (Burst annotated skeletons).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.TimedWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.TimedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each observer event carries the finite number of writer substitutions immediately preceding it. These counts are unbounded natural numbers and are mathematical annotations, never observer inputs.

**Definition 1.6 (Insertion of independent writer bursts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.expand`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

expand inserts each finite burst before its observer event. It includes updates before the first event, every local step, every Read and the separate Return.

**Definition 1.7 (Actual program transitions with hypothetical replies).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Skeleton`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Skeleton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A skeleton starts at the supplied accessible configuration and follows delta one microstep at a time. Reads may receive any of the four replies. The final event is Return with exactly b as the entire accessible configuration. Burst annotations do not influence the source-blind program transitions.

**Definition 1.8 (Separately defined actual execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Run`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Run carries one actual source register. An independent update applies native substitution without inspecting or changing observer control. A local step changes control only. A Read requires the actual readout at its literal address and follows the corresponding continuation. Return ends the active word and delivers the current whole configuration.

**Definition 1.9 (One finite formula for an erased skeleton).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.constraint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.constraint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

constraint i traverses only the observer event list, using original coordinate i at that event and incrementing the coordinate after every event. Each Read contributes its finite native navigation formula; the remaining events contribute no tree condition. All occurrences preserve one original source. The formula is independent of the supplied epoch values and burst counts.

**Definition 1.10 (Exact mathematical event counts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Chronology`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Chronology` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Chronology e i t eta states that each event coordinate equals the preceding epoch plus that event's finite burst. It retains counts at local steps and Return, even though those events add no tree equation.

**Definition 1.11 (Finite nondecreasing epoch vectors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Ordered`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Ordered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ordered e i events eta requires the first supplied epoch to be at least e and each later epoch to be at least its predecessor. It constrains only the finite event list and has no common bound.

**Definition 1.12 (Chronological difference insertion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.retime`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.retime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

retime replaces burst annotations by consecutive differences of the supplied event epochs. Its initial difference uses e. Nondecreasing epochs make each difference exact in the natural numbers.

**Definition 1.13 (Recovery of every update placement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.erase`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.erase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

erase removes writer events and counts each maximal update burst immediately preceding the next observer event. A legal returning word has no unassigned trailing update burst.

**Theorem 1.14 (Exact insertion of a finite independent burst).**

$$\forall C: Type, (\forall delta: C \to \operatorname{Op}\left(C\right), (\forall k: Nat, (\forall c: C, (\forall U: Source, (\forall t: Word, (\forall b: C, ((\operatorname{Run}\left(delta, c, U, \operatorname{append}\left(\operatorname{replicate}\left(k, \operatorname{update}\left(\right)\right), t\right), b\right)) \iff (\operatorname{Run}\left(delta, c, \operatorname{iterate}\left(substitution, k, U\right), t, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.updates_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A burst of k genuine writer substitutions before the supplied suffix is equivalent to starting that same suffix at the kth iterate. All observer configurations, the complete suffix word and the whole returned configuration are preserved. The burst count is a mathematical annotation, not an observer input.

**Theorem 1.15 (Native constraints realize every chronological schedule).**

$$\forall C: Type, (\forall delta: C \to \operatorname{Op}\left(C\right), (\forall c: C, (\forall b: C, (\forall t: TimedWord, ((\operatorname{Skeleton}\left(delta, c, t, b\right)) \implies (\forall u: Source, (\forall e: Nat, (\forall i: Nat, (\forall eta: Nat \to Nat, (\forall x: Nat \to Source, ((\operatorname{Ordered}\left(e, i, \operatorname{map}\left(snd, t\right), eta\right)) \implies ((\operatorname{Holds}\left(u, eta, x, \operatorname{constraint}\left(i, \operatorname{map}\left(snd, t\right)\right)\right)) \iff (\operatorname{Run}\left(delta, c, \operatorname{iterate}\left(substitution, e, u\right), \operatorname{expand}\left(\operatorname{retime}\left(e, i, \operatorname{map}\left(snd, t\right), eta\right)\right), b\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.chronological_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite source-blind skeleton and every supplied nondecreasing epoch vector satisfy this equivalence. Native formula satisfaction constructs an actual independent-writer execution by successive difference insertion. Conversely, the actual execution supplies every literal Read equation. Induction preserves the same original u, all adaptive local states, each materialized address and the exact whole terminal b. No liveness premise is used.

**Theorem 1.16 (Exact active histories and all projections).**

$$\forall C: Type, (\forall delta: C \to \operatorname{Op}\left(C\right), (\forall c: C, (\forall b: C, (\forall u: Source, (\forall x: Nat \to Source, ((\forall t: TimedWord, (\operatorname{erase}\left(\operatorname{expand}\left(t\right)\right) = t)) \land (\forall h: Word, ((\operatorname{Run}\left(delta, c, u, h, b\right)) \iff (\exists t: TimedWord, (\exists eta: Nat \to Nat, ((\operatorname{Skeleton}\left(delta, c, t, b\right)) \land (\operatorname{Chronology}\left(0, 0, t, eta\right)) \land (\operatorname{Holds}\left(u, eta, x, \operatorname{constraint}\left(0, \operatorname{map}\left(snd, t\right)\right)\right)) \land (\operatorname{expand}\left(t\right) = h) \land (\operatorname{erase}\left(h\right) = t)))))) \land (\forall D: Type, (\forall pi: TimedWord \to D, (\forall d: D, ((\exists h: Word, ((\operatorname{Run}\left(delta, c, u, h, b\right)) \land (\operatorname{pi}\left(\operatorname{erase}\left(h\right)\right) = d))) \iff (\exists t: TimedWord, (\exists eta: Nat \to Nat, ((\operatorname{Skeleton}\left(delta, c, t, b\right)) \land (\operatorname{Chronology}\left(0, 0, t, eta\right)) \land (\operatorname{Holds}\left(u, eta, x, \operatorname{constraint}\left(0, \operatorname{map}\left(snd, t\right)\right)\right)) \land (\operatorname{pi}\left(t\right) = d))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.native_history_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erasure after insertion recovers every burst annotated word. Every legal finite returning execution is exactly the expansion of a skeleton satisfying its native formula at chronological counts, and conversely. Equality retains placement relative to all local steps and Return. The final clause gives every projection pi of this recovered word: a constant projection gives the source fiber; selecting cumulative event counts at fixed or finitely specified roles gives the source and designated epoch relation. Different possible schedules are not assertions about the authenticated actual past.

**Definition 1.17 (Finitely encoded microstep instructions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Instruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Instruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An instruction is a local successor control, a literal address with four successor controls, or Return. Every natural control encodes an entire accessible finite configuration, without a uniform size bound.

**Definition 1.18 (Four acquired-reply successors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.continuation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four finite controls are selected in the order alpha, beta, branch and absent. This selection uses only the actual acquired reply.

**Definition 1.19 (Operational meaning of finite instructions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.instruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.instruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read instructions materialize their literal address and all four control successors; local instructions change control; Return preserves the whole terminal control.

**Definition 1.20 (Finite recursive code for each microstep).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.EffectiveProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.EffectiveProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A program supplies finite partial-recursive code, its total instruction function and an all-control realization equation. One evaluation computes one observer microstep. Divergent sequences of local steps are not replaced by a total next-external-action oracle.

**Definition 1.21 (Bounded recursive-code decoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.evalInstruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.evalInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite code evaluation either supplies a decoded finite instruction or yields no result at the supplied fuel. Increasing fuel eventually supplies the realized instruction at every individual control.

**Definition 1.22 (The complete reply alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.replies`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.replies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite list contains alpha, beta, branch and absent, each once.

**Definition 1.23 (Finite exploration with two bounds).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.enumerate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.enumerate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evaluator fuel bounds the recursive-code evaluation at each microstep, while depth bounds the number of observer events explored. Every Read explores all four continuations. Return emits the exact whole control. Every invocation is finite, including those exploring a branch that has infinitely many local steps.

**Definition 1.24 (Zero-burst representation of an erased word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.untimed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.untimed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

untimed marks each observer event with a zero burst. These markers describe the source-blind skeleton; retime supplies the actual chronological writer bursts.

**Theorem 1.25 (Code exploration and exact native execution).**

$$\forall P: EffectiveProgram, (\forall c: Nat, (\forall b: Nat, (\forall w: \operatorname{List}\left(ObserverEvent\right), ((\exists fuel: Nat, (\exists n: Nat, ((w, b) \in \operatorname{enumerate}\left(\operatorname{code}\left(P\right), fuel, n, c\right)))) \iff ((\operatorname{Skeleton}\left(\operatorname{transition}\left(P\right), c, \operatorname{untimed}\left(w\right), b\right)) \land (\forall u: Source, (\forall eta: Nat \to Nat, (\forall x: Nat \to Source, ((\operatorname{Ordered}\left(0, 0, w, eta\right)) \implies ((\operatorname{Holds}\left(u, eta, x, \operatorname{constraint}\left(0, w\right)\right)) \iff (\operatorname{Run}\left(\operatorname{transition}\left(P\right), c, u, \operatorname{expand}\left(\operatorname{retime}\left(0, 0, w, eta\right)\right), b\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.effective_native_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The union over evaluator fuel and microstep depth contains exactly the source-blind returning skeletons. Every one has the native constraint semantics at every chronological epoch vector. Soundness follows each decoded instruction; completeness bounds the finitely many code computations on a returning skeleton. Finite depth prevents a divergent hypothetical branch from blocking exploration of another branch. The entire terminal control b is preserved.

In these formulas map snd t is t.map Prod.snd, iterate is Function.iterate, and Holds is Formula.Holds with its formula argument last. The variable eta assigns natural exponents to event coordinates. Pi may retain any mathematical projection of the recovered burst annotated word.

The operational results quantify arbitrary control types and source-blind transition functions. The code-based extension gives an executable, sound and complete bounded exploration on naturally encoded controls. Formal partial-recursive encoding theorems for this exploration and the native formula generator are separate statements and are not asserted here. A different finite-string configuration representation requires its instruction realization equation; mere encodability does not supply it.

No supplemental row or comparison assertion is attached to these constraints. Such assertions require separate soundness proofs about actual acquisition events. Formula satisfaction cannot make an incorrect producer's retained assertions true.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Chronology`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.EffectiveProgram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Event`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Instruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.ObserverEvent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Op`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Ordered`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Skeleton`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.TimedWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.Word`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.chronological_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.constraint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.continuation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.effective_native_correspondence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.enumerate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.erase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.evalInstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.expand`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.instruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.native_history_correspondence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.replies`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.retime`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.untimed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.updates_iff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints](NativeLiteralPathConstraints.md)
