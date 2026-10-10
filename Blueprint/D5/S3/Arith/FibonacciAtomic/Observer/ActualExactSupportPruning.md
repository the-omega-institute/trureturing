# Exact Support Pruning and Nominal Table Coverage

## Abstract

Exact actual-support pruning retains every nominal state and transports each actual prefix into a complete finite table.

The actual source budget and the finite literal-address packing envelope are separate parameters. Queries outside the actual support become false halts; nominal caches are filtered without altering stored raw replies or order. Actual state visits, reports, cache values and actions remain unchanged. The original paired relation proves coarse factorization for the new total history semantics, including impossible histories.

**Definition 1.1 (Actual literal support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ActualSupport`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ActualSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every query made at an actual prefix belongs to the specified finite set. This condition does not restrict unreachable rows.

**Definition 1.2 (Raw cache projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportCache`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportCache` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter only by literal address membership, preserving chronology and four-valued replies.

**Definition 1.3 (Supported row action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain halt rows and supported query rows; replace other queries by false halts.

**Definition 1.4 (Pruned complete observer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportObserver`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete nominal carrier and raw successor table are retained, with projected actions and caches.

**Definition 1.5 (Exact pruning contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.SupportPruningContract`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.SupportPruningContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two observers have exactly the same actual prefixes and rows; actual actions, caches and finite runs are preserved, and admissibility remains valid.

**Theorem 1.6 (Exact actual-support pruning).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.support_pruning_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.support_pruning_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible observer whose actual requests lie in the specified support satisfies the exact pruning contract. State observations transported by the identity retain their actual values.

**Definition 1.7 (Finite packing envelope).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportWidth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One plus the maximum address length in the finite support; it is independent of the source budget.

**Definition 1.8 (Prescribed trace support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prescribedSupport`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prescribedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the distinct literal addresses in all prescribed terminal traces on the original bounded source domain.

**Definition 1.9 (Prescribed raw runs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ExactTraces`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ExactTraces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each allowed source has the prescribed full raw trace and terminal bit. Additional phase observations are not part of this predicate.

**Theorem 1.10 (Actual prefix has its terminating tail).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prefix_run_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prefix_run_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original observer M and immutable U, an ActualPrefix(M,U,e,h) and Run(M,U,e0,t,f,b) supply a raw suffix s with Run(M,U,e,s,f,b) and h appended to s equal to t. No legality assumption or counterfactual prefix is used.

**Theorem 1.11 (All exact competitors have finite tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.exact_competitor_table_coverage`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.exact_competitor_table_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible exact-trace competitor has a native table on its full nominal cardinality with Qπ-only actions and caches. Under the state bijection it preserves all actual prefixes, actions and caches, the prescribed complete raw traces, and admissibility for the original source budget. This is representation of every competitor, not a quotient of one selected behavior table.

This result supplies support pruning and nominal table coverage. It does not provide the original compileRaw phase-label parser, finite prescribed-prefix acceptance checks, the explicit route/verifier/acquisition horizon, or the marked and unmarked minimum and price formulas.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ActualSupport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.ExactTraces`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.SupportPruningContract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.exact_competitor_table_coverage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prefix_run_tail`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.prescribedSupport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportCache`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportObserver`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.supportWidth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.support_pruning_contract`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable](ActualObserverFiniteTable.md)
