# Original Completion Phase Replay

## Abstract

Original controller phases are replayed from coarse histories, resetting only the local history at phase boundaries.

The phase observation contains the current route history, or the selected verifier, remaining literal leaf requests and verifier history, or the acquisition history. It discards previous phases' histories. The chronological first-occurrence raw cache remains the compiler's separate persistent decoder.

**Definition 1.1 (Original phase observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.PhaseLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.PhaseLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Route, verifier and acquisition observations retain their respective local coarse histories; malformed histories have one fixed default observation.

**Definition 1.2 (Original verifier replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.verifyPhase`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.verifyPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replay verifyController on quotient representatives. A successful leaf comparison advances the residual leaf list, and the first mismatch starts acquisition on the fresh unconsumed suffix.

**Definition 1.3 (Original route replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.routePhase`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.routePhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replay compileRaw on the coarse route. At its exit, the selected verifier or acquisition begins with an empty local history.

**Definition 1.4 (Finite actual phase alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phaseAlphabet`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phaseAlphabet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of all bounded-source terminal coarse prefixes under the original phase parser.

**Definition 1.5 (Installed phase observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.observerPhase`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.observerPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every retained compiler row carries its parsed original phase; the absorbing sink carries the fixed malformed label.

**Theorem 1.6 (Original action and phase replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phase_replay_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phase_replay_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive source budget and an original Strategy with the exact compileRaw/controllerPolicy policy equation, the parser computes the original action on every coarse history. It preserves the original route exit and verifier-failure resets. A route label is exactly the route-local consumed history. A verifier label identifies the same selected prototype, decomposes the initial requests into consumed addresses and the residual list, and retains exactly the consumed matching reports in its local history; a nonempty residual has exhausted the available input. Every actual compiled prefix carries its original local phase observation in the finite phase alphabet, and its parsed action equals the original strategy action. The statement does not replace phase labels with the full global history.

The finite prescribed-prefix checker, explicit route/verifier/acquisition horizon, and the marked and unmarked minimum-price formulas are separate obligations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.PhaseLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.observerPhase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phaseAlphabet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.phase_replay_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.routePhase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.verifyPhase`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler](ActualExactTraceCompiler.md)
