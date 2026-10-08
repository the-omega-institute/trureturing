# Native Finite Observer and Bounded Raw Absence

## Abstract

Complete finite nominal observers retain the original raw semantics; every address beyond the native leaf budget is absent, also on truthful cache hits.

**Definition 1.1 (Ordered raw reports).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.RawHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.RawHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Histories are chronological literal-address and four-response pairs. Order and repetitions remain. The source is the original nonempty FreeMagma Bool, addresses are List Bool, and positivity is membership in the third native substitution image.

**Definition 1.2 (Original bounded sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Allowed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Allowed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Allowed(N,U) means that the native source has at most N leaves. This domain retains every original shape and label.

**Definition 1.3 (Bounded node addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Q_N`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Q_N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_N contains exactly the words of length at most N minus one. Every literal word remains an original legal request.

**Definition 1.4 (Same-source cache truth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.CacheTruth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.CacheTruth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every stored raw report agrees with readout at its literal address in the same immutable source.

**Definition 1.5 (Truthful hits and source misses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.queryReply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.queryReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An exact address hit returns its stored raw report. Only an address miss reads the original source.

**Definition 1.6 (First-occurrence update).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.cacheUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.cacheUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A hit preserves the entire ordered cache. A miss appends exactly the queried address and raw response; it neither infers nor overwrites entries.

**Definition 1.7 (Complete nominal rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Observer`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Observer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite carrier E, the observer has a source-independent initial row e0, action, four-response transition and ordered raw cache decoder. The initial row witnesses nonemptiness. Decoded addresses have no duplicates at every nominal row, including unreachable rows. The finite carrier contains every dynamic distinction.

**Definition 1.8 (Absorbing response step).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.barStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.barStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A query row takes its raw-response transition. A halt row remains fixed for every raw response, independently of its transition table.

**Definition 1.9 (Response-word action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.responseState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.responseState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fold the absorbing step over the raw reply word from an arbitrary nominal row.

**Definition 1.10 (All-history state).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fold only the raw responses from e0. Reported address labels are ignored even on impossible, inconsistent or unreachable histories.

**Definition 1.11 (All-history action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return the action of the final absorbing row after the complete response fold.

**Definition 1.12 (Actual external trace prefixes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.ActualPrefix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.ActualPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual prefix begins at e0 and extends by the row's literal query and its hit-or-miss raw reply. The trace is an external record and supplies no additional controller memory.

**Definition 1.13 (Sourcewise finite runs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Run`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite inductive run follows those exact query transitions until an original halt, retaining every repeat and hit in order. No uniform fuel, clock, jump log or acyclic-row restriction is assumed.

**Definition 1.14 (Actual cache premises).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Legal`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial decoded cache is empty. At every actual prefix its entries are true of the same source and each query successor decodes to exactly the first-occurrence update. Truth and update are not imposed on arbitrary counterfactual rows.

**Definition 1.15 (Original complete bounded contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Admissible`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N is at least one. On every allowed source the observer is legal and has a finite run returning true exactly for the original third-substitution Positive target. Its action factors through the existing coarse history map on all finite histories. Nominal states are retained in full; no source port or canonical controller is installed.

**Theorem 1.16 (Actual prefixes realize folds and exact raw caches).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, (\forall e: E, (\forall h: RawHistory, (((\operatorname{Legal}\left(M, U\right)) \land (\operatorname{ActualPrefix}\left(M, U, e, h\right))) \implies ((\operatorname{historyState}\left(M, h\right) = e) \land ((\operatorname{decoder}\left(M, e\right) = \operatorname{foldl}\left((cache: RawHistory \mapsto (a: \operatorname{Sigma}\left(\operatorname{const}\left(Address, Reply\right)\right) \mapsto \operatorname{cacheUpdate}\left(cache, \operatorname{fst}\left(a\right), \operatorname{snd}\left(a\right)\right))), [], h\right)) \land (\operatorname{CacheTruth}\left(h, U\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.actualPrefix_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a legal observer on a fixed original source, every actual prefix ends at the row obtained by folding its raw replies with absorbing barStep. The decoded cache equals the chronological fold of cacheUpdate from the empty list, so repeated addresses retain their first entry and new addresses append in order. Every report in the external trace is true of that same source. Induction over chronological prefix extension uses the exact decoded-cache update law; an exact hit is true by cache truth and a miss is the original source readout.

**Theorem 1.17 (Head and tail runs extend chronological prefixes).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, (\forall e, f: E, (\forall t, h: RawHistory, (\forall b: Bool, (((\operatorname{Run}\left(M, U, e, t, f, b\right)) \land (\operatorname{ActualPrefix}\left(M, U, e, h\right))) \implies ((\operatorname{ActualPrefix}\left(M, U, f, \operatorname{append}\left(h, t\right)\right)) \land (\operatorname{action}\left(M, f\right) = \operatorname{inr}\left(b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.run_from_actualPrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A run from the row of any existing actual prefix extends that prefix by its entire ordered trace and ends at a halt row with its stated output bit. Induction on the run appends each current report to the prefix before extending through the tail; list append associativity aligns this chronological construction with head and tail execution. No legality or termination bound is needed for this correspondence.

**Theorem 1.18 (Unique finite trace, final row and output).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, (\forall e, f, g: E, (\forall t, s: RawHistory, (\forall b, c: Bool, (((\operatorname{Run}\left(M, U, e, t, f, b\right)) \land (\operatorname{Run}\left(M, U, e, s, g, c\right))) \implies ((t = s) \land ((f = g) \land (b = c)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.run_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two finite runs from the same nominal row on the same immutable original source have equal traces, final rows and output bits. Induction on one run compares the other run's first constructor. Query and halt actions cannot coincide; two query actions have the same literal address and therefore the same decoded-cache reply and successor. The tail induction then gives equality of the complete ordered traces and outputs.

**Theorem 1.19 (Every admissible actual run has the original semantics).**

$$\forall N: Nat, (\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, (\forall t: RawHistory, (\forall f: E, (\forall b: Bool, (((\operatorname{Admissible}\left(N, M\right)) \land ((\operatorname{Allowed}\left(N, U\right)) \land (\operatorname{Run}\left(M, U, \operatorname{e0}\left(M\right), t, f, b\right)))) \implies ((\operatorname{ActualPrefix}\left(M, U, f, t\right)) \land ((\operatorname{historyState}\left(M, t\right) = f) \land ((\operatorname{action}\left(M, f\right) = \operatorname{inr}\left(b\right)) \land ((\operatorname{historyAction}\left(M, t\right) = \operatorname{inr}\left(b\right)) \land ((\operatorname{decoder}\left(M, f\right) = \operatorname{foldl}\left((cache: RawHistory \mapsto (a: \operatorname{Sigma}\left(\operatorname{const}\left(Address, Reply\right)\right) \mapsto \operatorname{cacheUpdate}\left(cache, \operatorname{fst}\left(a\right), \operatorname{snd}\left(a\right)\right))), [], t\right)) \land ((\operatorname{CacheTruth}\left(\operatorname{decoder}\left(M, f\right), U\right)) \land ((\operatorname{CacheTruth}\left(t, U\right)) \land ((b = true) \iff (\operatorname{Positive}\left(U\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.admissible_run_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original allowed source and every run from e0 of an admissible observer, the final row is an actual prefix row and is exactly historyState of the run trace. Its action and historyAction both halt with the run's bit. Its decoded cache is exactly the first-occurrence cacheUpdate fold from the empty list, and both this cache and every external trace report are true of the same original source. The output is true exactly for Positive of that source. Run extension and actual-prefix semantics establish the trace and cache conclusions. Admissible supplies existence of a correct run; finite-run uniqueness transfers its correct bit to the arbitrary run under consideration. No correspondence or correctness premise for that particular run is assumed.

**Theorem 1.20 (Native subtree leaf-count geometry).**

$$\forall U, T: Source, (\forall q: Address, ((\operatorname{subtree}\left(q, U\right) = \operatorname{some}\left(T\right)) \implies (\operatorname{length}\left(q\right)+\operatorname{length}\left(T\right) \le \operatorname{length}\left(U\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.subtree_leaf_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge on a native subtree path leaves a nonempty sibling subtree. Induction on the original FreeMagma tree bounds address length plus retained subtree leaf count by the original leaf count.

**Theorem 1.21 (Raw absence beyond the budget, including cache hits).**

$$\forall N: Nat, (\forall U: Source, (\forall q: Address, (((\operatorname{Allowed}\left(N, U\right)) \land (\neg \operatorname{member}\left(q, Q_{N}\right))) \implies ((\operatorname{readout}\left(q, U\right) = absent) \land (\forall cache: RawHistory, ((\operatorname{CacheTruth}\left(cache, U\right)) \implies ((\operatorname{queryReply}\left(cache, q, U\right) = absent) \land (\forall a: \operatorname{Sigma}\left(\operatorname{const}\left(Address, Reply\right)\right), (((\operatorname{member}\left(a, cache\right)) \land (\operatorname{fst}\left(a\right) = q)) \implies (\operatorname{snd}\left(a\right) = absent))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.outside_Q_N_absent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every allowed original source and every word outside Q_N, the subtree is missing: otherwise its positive leaf count contradicts the native path bound. The existing readout/subtree supplier then yields raw absent. A truthful ordered cache returns that same raw absent on a miss or a hit, and every stored entry at that address is raw absent.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.ActualPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Admissible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Allowed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.CacheTruth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Legal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Observer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Q_N`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.RawHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.Run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.actualPrefix_semantics`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.admissible_run_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.barStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.cacheUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.historyState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.outside_Q_N_absent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.queryReply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.responseState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.run_deterministic`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.run_from_actualPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.subtree_leaf_count`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory](ActualCoarseReadoutHistory.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](ActualLeafHistoryRigidity.md)
