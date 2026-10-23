# Finite passive service realization

## Abstract

Finite passive controllers as effective original services with their complete paid traces

A total passive history controller is unfolded through a finite number of Read nodes. Each actual reply has its own explicit continuation. Preorder flattening replaces those continuations by absolute natural workspace indices and preencoded outputs. The installed original selector is total list lookup followed by an explicit common default. The Partrec proof uses pinned computable list lookup and option defaults. No source, source size, equality port, timing input or old source-dependent workspace enters installation.

**Definition 1.1 (unfold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.unfold`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.unfold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The depth counts reads. Even at depth zero an immediate Stop retains its original complete output. A Read beyond the bound receives the common fallback. The realization theorem shows that fallback never changes an actual terminating path whose paid trace length is within the bound.

**Definition 1.2 (flatten).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.flatten`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.flatten` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every Read instruction contains the actual address and four natural continuations in alpha, beta, branch, absent order. Every Stop instruction contains its complete output. Child sublists are placed at the accumulated preorder offsets. No repeated physical query is removed.

**Definition 1.3 (materialize).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materialize`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materialize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The controller, output encoder, fallback, bound and common starting paid history determine a finite instruction list. All four reply branches are unfolded, including branches without a source witness. This construction enumerates reply words rather than sampling the source domain.

**Definition 1.4 (tableService).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.tableService`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.tableService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original selector returns Part.some of the workspace-indexed list entry, with a common Stop default. It is Partrec for every explicit installed table. This theorem about an installed table does not establish uniform computability of an infinite family of installations.

**Definition 1.5 (executeTable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.executeTable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.executeTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This executable first-order interpreter performs the original Read and update transitions on one register, carries the common input and the full chronological record, and returns at its first Stop. Tables produced by materialize use only Read and Stop. The realization theorem also proves exact interpreter execution and its final common input, stationary epoch and complete appended read record.

**Theorem 1.6 (bounded_passive_realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.bounded_passive_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.bounded_passive_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The passive executor uses the actual readout of one arbitrary finite source register. Its terminating trace and raw bound imply an OriginalRun of the generated table at any certified starting epoch, with arbitrary common input and prior original record. Physical addresses, actual replies, duplicates and chronology are preserved. The exact read list, answer word and raw count are retained, and the interpreter terminates with the complete output. Native statement: theorem bounded_passive_realization {L O : Type} [Primcodable O] (π : PaidHistory → Sum Address L) (enc : L → O) (fallback : O) (K fuel : Nat) (h : PaidHistory) (input N : Nat) (prior : List OriginalEvent) (r : Source) (t : PaidHistory) (o : L) (run : execute readout π fuel h r = some (t, o)) (bound : t.length ≤ K) : let table := materialize π enc fallback K h OriginalRun (tableService table fallback) (input,0,N,prior) r (paidTrace N t) (enc o) ∧ (∃ final : OriginalState, executeTable table fallback fuel (input,0,N,prior) r = some (paidTrace N t,final,enc o) ∧ final.input = input ∧ final.epoch = N ∧ final.history = prior ++ recordReads N t) ∧ reads (paidTrace N t) = t.map (fun a => (N,a.1,a.2)) ∧ answers (paidTrace N t) = t.map Sigma.snd ∧ (answers (paidTrace N t)).length = t.length

**Definition 1.7 (materializeWholeRow).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materializeWholeRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materializeWholeRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This concrete source-free materializer applies NativeWholeRowService.compileService and controller to old, Q, H and N, unfolds at NativeWholeRowPlan.K0, converts each whole literal record through recordRow, and preencodes its complete canonical row by NativeSerialDepth.rowWord. K0 depends on old, Q and H alone; N changes the physical addresses. A base source witness can be used inside a correctness proof to identify the actual old row, but is never an argument of this executable compiler. Uniform Computable evidence for the complete encoded common-input family remains separate from the verified Partrec selector for each installed table.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.bounded_passive_realization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.executeTable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.flatten`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materialize`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.materializeWholeRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.tableService`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.unfold`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](NativeSerialDepth.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective](NativeSerialEffective.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService](NativeWholeRowService.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](../../../ConceptDynamics/Experiment/PassivePolicyNormalization.md)
