# NativeWholeRowService

## Abstract

Native finite whole-row criterion and lawful source fibers

NativeWholeRowPlan supplies the exhaustive ground-binding criterion, paid query plans, record reconstruction and their correctness proofs. This module imports that complete API. twoPhaseController, compileService and controller use a single chronological paid reply history and return once. two_phase_execution proves continuous execution; stationary_cell_service combines the criterion, exact record and budget with that execution; stationary_whole_fiber_service extends correctness to every source in the complete retained-row/history fiber. The concrete groundBindingInput application is described in NativeWholeRowPlan with its unconditional all-source, all-epoch scope and formal K0(input) bound. Original serial-update inclusion, U8 and resource optimality remain outside these stationary results.

**Definition 1.1 (compileService).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.compileService`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.compileService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only common retained inputs and the certified epoch enter preprocessing. The first list acquires all original replies below the fixed depth, and the selected second list probes every genuine ground binding. The program performs one continuous run with one final absorbing return of the complete record. stationary_cell_service proves correctness and the uniform raw budget of this very controller; stationary_whole_fiber_service extends that result to all sources with the same complete old row and literal history. Incomplete transcript lengths and failed cell checks return a fixed common leaf record.

**Definition 1.2 (controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.controller`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selector uses the compiled common program and newly paid chronological replies. No unknown source, subtree, valuation, fiber witness or source identity is a runtime input.

**Theorem 1.3 (two phase execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.two_phase_execution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.two_phase_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete native statement is retained with its exact quantified scope and all premises. Native statement: theorem two_phase_execution {L : Type} (first : List Address) (second : Hist (fun _ : Address => Reply) → List Address) (finish : Hist (fun _ : Address => Reply) → L) (u : Source) : let one := listTrace first u let two := listTrace (second one) u execute readout (twoPhaseController first second finish) (first.length + (second one).length + 1) [] u = some (one ++ two,finish (one ++ two)) ∧ (one ++ two).length = first.length + (second one).length ∧ (one ++ two).map Sigma.fst = first ++ second one

**Theorem 1.4 (stationary cell service).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_cell_service`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_cell_service` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual compiled controller terminates on every lawful filling of every feasible admitted cell, returning the entire original literal record with at most K0 raw reads. Native statement: theorem stationary_cell_service {C : LiteralRow} (Q : CutSet) (H : History) (hQ : CutPrefixFree Q) (good : (analyze C Q H).passes = true) (η : Patterns C (requiredDepth Q H)) (feasibleCell : feasible η H = true) (v : Variables η → Source) (legal : Diseq (delta η) v) (N : Nat) : let program := compileService C Q H N let u := evaluate v (wholeTerm η) ∃ fuel trace, execute readout (controller program) fuel [] (substitution^[N] u) = some (trace,literalRecord Q u) ∧ trace.length ≤ K0 C Q H

**Theorem 1.5 (stationary whole fiber service).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_whole_fiber_service`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_whole_fiber_service` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact native history-cell/source equivalence lifts the controller result to every source in the complete retained-row/history fiber. All old disequalities, repeated class occurrences and absent-cut guards remain present. This stationary execute result does not establish the unpublished original serial-service inclusion or U8. Native statement: theorem stationary_whole_fiber_service (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q) (base : Source) (H : History) (good : (analyze (canonicalRow P base) Q H).passes = true) (N : Nat) (u : Source) (old : canonicalRow P u = canonicalRow P base) (history : NativeDepthPatterns.Consistent H u) : ∃ fuel trace, execute readout (controller (compileService (canonicalRow P base) Q H N)) fuel [] (substitution^[N] u) = some (trace,literalRecord Q u) ∧ trace.length ≤ K0 (canonicalRow P base) Q H

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.compileService`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_cell_service`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_whole_fiber_service`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.two_phase_execution`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan](NativeWholeRowPlan.md)
