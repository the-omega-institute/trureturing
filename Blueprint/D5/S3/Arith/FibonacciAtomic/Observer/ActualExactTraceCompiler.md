# Exact Finite Trace Compiler

## Abstract

Repeated logical requests retain full control history while raw caches use chronological first occurrences.

The raw and coarse first-occurrence folds commute with kappa_hist. A repeated hit therefore keeps its stored raw branch or absent value, even for a contradictory supplied raw response. The exact carrier keeps every compatible cache lift over each first coarse history and one absorbing sink.

**Definition 1.1 (Coarse first-occurrence update).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.coarseCacheUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.coarseCacheUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A repeated logical address keeps its existing coarse value; a miss appends the new coarse report.

**Definition 1.2 (Raw first-occurrence fold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstRaw`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chronological cacheUpdate fold over a raw logical history.

**Definition 1.3 (Coarse first-occurrence fold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstCoarse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstCoarse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corresponding chronological fold over coarse reports.

**Definition 1.4 (Exact row decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactRowDecoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactRowDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A compiler row decodes the compatible first-occurrence cache indexed by its full logical history.

**Definition 1.5 (Exact row extension).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAppendRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAppendRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A retained logical extension packs its updated raw cache into the extended first coarse fiber.

**Definition 1.6 (Exact compiler action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Control reads the full logical coarse history and the sink halts false.

**Definition 1.7 (Exact compiler transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A query extends the full history when retained and otherwise enters the absorbing sink.

**Definition 1.8 (Strategy prefix carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPrefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPrefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite union of all coarse prefixes of the original terminal traces over the allowed source domain.

**Theorem 1.9 (Original actual prefix belongs to the compiler carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_prefix_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_prefix_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N, Strategy pi, allowed source U and raw history h prefixing terminal(pi,U).trace, kappa_hist(h) belongs to strategyPrefixes(N,pi). This preserves the original literal addresses, repetitions and coarse chronological order.

**Definition 1.10 (Strategy carrier cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyStateCard`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyStateCard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact state count obtained from the strategy prefix carrier and compatible first-cache fibers.

**Theorem 1.11 (Strategy state cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strategy-indexed exact carrier has the stated finite cardinality.

**Definition 1.12 (Exact finite observer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactObserver`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite carrier supplies an input-independent empty row, full-history coarse control and the first-occurrence raw decoder.

**Definition 1.13 (Replay continuation contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ReplayStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ReplayStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every requested extension from a specified original horizon prefix remains a retained coarse prefix and an original horizon prefix.

**Definition 1.14 (Exact history index).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite carrier index for each retained coarse control history.

**Definition 1.15 (Exact cache row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A control history paired with every compatible first-coarse raw cache lift.

**Definition 1.16 (Exact state carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row carrier plus one absorbing unit sink.

**Definition 1.17 (Exact cardinality expression).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactStateCard`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactStateCard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum of compatible cache fiber cardinalities plus the sink.

**Definition 1.18 (Coarse strategy policy).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPolicy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the original strategy on the fixed coarse-history representative.

**Definition 1.19 (Strategy-indexed observer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyObserver`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Instantiate the exact finite observer on all allowed terminal coarse prefixes.

Strategy-indexed replay, exact terminal runs and admissibility assume a positive source bound and an original strategy policy that factors through kappa_hist. Sourcewise replay and run statements range over the allowed sources at that bound.

**Theorem 1.20 (Strategy prefix cache replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_actual_prefix_replay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_actual_prefix_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual prefixes of the strategy-indexed observer carry the original full coarse history and first-write raw cache.

**Definition 1.21 (Coarse control projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Forget cache lifts while retaining full logical coarse control or the sink.

**Theorem 1.22 (All-history ghost safety).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exact_all_history_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exact_all_history_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal coarse response histories have equal actions, including contradictory repeats and post-halt reports.

**Theorem 1.23 (Exact terminal run).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_exact_run`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_exact_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled observer realizes the original terminal trace and output bit.

**Theorem 1.24 (Finite observer admissibility).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strategy-indexed observer satisfies the original bounded finite observer contract.

**Theorem 1.25 (Exact state bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A literal support and horizon bound controls the exact compatible-cache state count.

The exact state count is one plus the sum of 2 to the number of distinct coarse-none addresses over retained full logical prefixes. The general bound uses the number of allowed sources, an explicitly supplied trace horizon and an explicitly supplied literal support. The route-specific horizon, original phase labels and minimum-price formulas are separate obligations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ExactState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.ReplayStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.coarseCacheUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactAppendRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactControl`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactObserver`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactRowDecoder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactStateCard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exactTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.exact_all_history_factorization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstCoarse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.firstRaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyObserver`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPolicy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyPrefixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategyStateCard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_actual_prefix_replay`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_admissible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_exact_run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_prefix_mem`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.strategy_state_card_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](../ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination](../ActualFiniteObserverAbsentElimination.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber](ActualAcquisitionCacheFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization](ActualObserverAbsorbingNormalization.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPairReach](ActualObserverPairReach.md)
