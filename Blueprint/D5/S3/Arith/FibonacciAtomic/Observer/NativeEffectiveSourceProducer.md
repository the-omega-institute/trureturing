# Effective Original Source Acquisition

## Abstract

A single partial-recursive original selector acquires every finite source on its unchanged original register and returns a lossless numeric syntax name.

**Definition 1.1 (Ordered syntax names).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceName`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alpha leaf has name zero and the beta leaf has name one. A binary source with child names m and n has name Nat.pair(m,n)+2. Names describe the labelled ordered syntax tree, rather than any evaluation of that tree. Injectivity follows by separating leaf names from branch names and using the inverse of Nat.pair recursively.

**Definition 1.2 (Semantic recovery of the entire source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceDecoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder returns the unique finite Source with the supplied name when one exists, and none otherwise. This inverse is defined by classical choice. Its exact inverse law on returned names is proved, but no effective Source-valued decoder is asserted or used by the selector.

**Definition 1.3 (Numeric acquired workspace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.NumericControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.NumericControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Visit stores an address and a stack of pending right addresses or already acquired left-child names. Deliver stores an acquired name and the same stack. The standard primitive-codable sums, products and lists encode this workspace as a natural number. nameControl is a proof-side correspondence from the existing source producer's control; it is never an unknown-source argument to the program.

**Definition 1.4 (One common initialization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.initialWorkspace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.initialWorkspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The workspace is the encoding of Visit at the empty root address with an empty stack. It is fixed independently of the original source, common input and retained acquired history.

**Definition 1.5 (One numeric producer instruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.numericTick`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.numericTick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A visit yields an OriginalAction read at its literal address, with four encoded continuations. Alpha and beta construct their numeric leaf names; branch schedules the left address and saves the right address. An absent reply uses the alpha continuation, although source traversal never requires it. Deliver with a pending address switches to that address and saves the acquired name; deliver with a saved left name combines the two numeric names. Deliver with an empty stack stops. Invalid workspace encodings use the fixed initial control. This instruction function is computable and receives only a natural-number workspace.

**Definition 1.6 (Certified first return).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.selectWorkspace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.selectWorkspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PFun.fix advances numericTick through its local continuation instructions until the next read or stop. The primitive-recursive sum, list, pairing and encoding operations give a computable numericTick, and Partrec.fix supplies the actual partial-recursive first-return certificate. A numeric local instruction corresponds to one genuine sourceControl local instruction under nameControl; first-return equality forwards selection across that instruction. There is no truth oracle and no uniform finite local-step bound.

**Definition 1.7 (The fixed original effective service).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceService`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The OriginalEffectiveService Nat selector applies selectWorkspace to the accessible workspace projection of OriginalState. The same selector is used for every original source. Common input, epoch and acquired history are retained by the original transition semantics, while this selector ignores them. The effective field is a proved Partrec certificate, not an assumption about a boundary oracle.

**Definition 1.8 (Actual original transitions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.OriginalTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.OriginalTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A read transition requires membership of the selected OriginalAction, obtains the reply from readout of the actual current register, and appends its epoch, address and numeric reply code to the retained acquired history. An update transition would advance epoch and substitute the register. For sourceService no update action belongs to any selector value, including away from reached states, so every reachable original transition preserves common input, epoch and register.

**Definition 1.9 (Ordered external acquisition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.externalTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.externalTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The external trace maps the existing acquisitionTrace to epoch-zero read events in precisely its original order. It contains neither producer local-step markers nor evaluator local-step markers. The producer's full productionTrace remains available separately, with both genuine local actions at every branch.

**Definition 1.10 (The complete sourcewise contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.FullSourceAcquisition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.FullSourceAcquisition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For output o, original U, common input i and retained acquired history H, this proposition requires the Partrec selector certificate, an actual OriginalRun from initialState(i,H) on U with externalTrace(U) and output o, and sourceDecoder(o)=some U. It also requires a reached stopping original state whose input is i, epoch is zero and acquired history is exactly H followed by acquisitionTrace(U) encoded as actual read events. Every reached original state preserves i, epoch zero and register U. Separately, the genuine native producer Run returns U with its full productionTrace, appends that full trace to any prior native log, and provides a finite source-free Replay for every prefix of the acquired reply word, with the exact trace prefix and terminal-boundary criterion. The native paid-read list equals the epoch-zero-tagged acquisitionTrace; its addresses are exactly nodes(U), have no duplicates, and its length is nodes(U).length. These native read events correspond one for one and in order to externalTrace(U). Every reached native producer configuration retains epoch zero and register U. Finally, for every producer control c, numericTick(workspace(c)) equals nameInstruction(sourceControl(c)): local successors have the corresponding numeric workspace, reads have all four corresponding numeric continuations, and stops have the acquired syntax name. This is an instruction correspondence, with no assertion about a chosen evaluator's microsteps. The original acquired history and the producer's full native log are distinct representations: local producer actions occur in the latter, while only acquired external events occur in the former.

**Theorem 1.11 (All finite originals under one selector).**

$$\forall i: Nat, (\forall H: \operatorname{List}\left(OriginalEvent\right), (\forall U: Source, (\operatorname{FullSourceAcquisition}\left(\operatorname{sourceName}\left(U\right), U, i, H\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.effective_source_producer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Source satisfies FullSourceAcquisition with its sourceName, for every common input and every retained initial acquired history. The proof directly uses NativeFullSourceProducer.native_source_producer for actual traversal and once-per-node acquisition. Induction on that supplied Run transports its visits, local instructions and stop to the numeric first-return selector; an enriched read execution retains the final acquired state. The original transition relation's read rule and the impossibility of any selected update establish stationary epoch and register. The existing reached_prefix_replay theorem retains the producer's complete local segments independently of the projected OriginalRun trace.

This result proves sourcewise termination and certified Partrec selection with growing finite workspace and output. It supplies no uniform controller size, time, memory or read bound, physical implementation or erasure, or evaluator microstep equality with sourceControl. No explicitly chosen computational Nat.Partrec.Code with an all-state OriginalCodeRealization equation is supplied here. The existing compiler can be applied directly when such a genuine realization is provided; the selector certificate alone does not install an evaluator program.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.FullSourceAcquisition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.NumericControl`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.OriginalTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.effective_source_producer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.externalTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.initialWorkspace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.numericTick`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.selectWorkspace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceDecoder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceName`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.sourceService`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer](NativeFullSourceProducer.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective](NativeSerialEffective.md)
