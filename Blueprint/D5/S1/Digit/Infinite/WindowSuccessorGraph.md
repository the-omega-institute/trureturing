# Successor Graphs of Finite Legal Digit Windows

## Abstract

Successor Graphs of Finite Legal Digit Windows.

**Theorem 1.1 (The exact window successor graph).**

Lean statement: `D5/S1/Digit/Infinite/WindowSuccessorGraph.window_successor_graph`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/WindowSuccessorGraph.window_successor_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive window length L, Fibonacci values identify the observed successor graph with the increment cycle from zero through G_L minus one, together with the extra reset from G_(L-1) minus one to zero. That extra source is the unique vertex with two outgoing edges, and zero is the unique vertex with two incoming edges. Every edge occurs on natural digit rows. One extra input digit determines the successor window uniquely, while the original window cannot determine it even on natural rows. After h steps, h extra input digits suffice.

## References

- Truth anchor: `D5/S1/Digit/Infinite/WindowSuccessorGraph.window_successor_graph`
- Dependency: [D5/S1/Digit/Infinite/InfiniteSuccessorFibres](InfiniteSuccessorFibres.md)
- Dependency: [D5/S1/Digit/Infinite/MultiplierObstruction](MultiplierObstruction.md)
