# Finite History Canonical Tree

## Abstract

Pointwise finite termination on a finite candidate set yields an exact canonical passive tree preserving complete histories, labels, zero-error singleton fibres, and rational weighted query counts.

**Theorem 1.1 (Exact finite-history policy/tree correspondence).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree.finite_history_canonical_tree`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree.finite_history_canonical_tree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W, Q, Y and L be the independent state, query, dependent response and terminal-label types. A readout is read(q) : W -> Y(q), and a deterministic policy maps every dependent history Hist(Y) to either a query or a terminal label. Execution reads one fixed state throughout, records every query/response pair, and may repeat queries.

For a finite candidate set C, assume only pointwise termination: each x in C has some fuel n, complete history t and label l with execute read policy n [] x = some (t,l). Then a finite supremum of those witnesses supplies N. Every n >= N unfolds the existing boundedTree operation far enough to reproduce each successful run exactly, with the same full history, length, terminal action and label.

At the reproduced history, the existing candidates predicate is exactly the candidates executing the same complete history and label at the supplied fuel. For every rational weight function mu and every trace/label assignment witnessed by successful executions on all candidates, the canonical weighted sum of history lengths equals the original weighted sum. If every completed run is decoded correctly, every canonical candidate fibre is a singleton and canonical transcripts are injective on C.

The result assumes no common input horizon, no finiteness of Q or the response alphabets, and no termination outside C. It retains repetitions and full terminal labels. In the circular deletion specialization it is only the generic finite policy prerequisite; insertion gaps, pair fibres, third-deletion separation and the expected-cost optimum remain separate results.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree.finite_history_canonical_tree`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost](../../Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.md)
