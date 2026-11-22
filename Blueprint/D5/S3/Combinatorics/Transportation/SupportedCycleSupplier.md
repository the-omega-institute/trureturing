# SupportedCycleSupplier

## Abstract

Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge.

**Theorem 1.1 (A simple cycle of target disagreements).**

Lean statement: `D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle` (`✓ std3`). ∎

*Citation.* Guanyang Wang (2026). *KTV Proof Formalization*. URL: <https://github.com/guanyangwang/ktv-swap-lean/blob/15b5f47c9ac833bfdf99b8b29374af7a678ef4bc/KTV/Johnson/Connectivity.lean#L1394>.

*Commentary.*

Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge.

Equal row counts pair a positive disagreement with a negative disagreement in the same row; equal column counts then give a positive disagreement in the next row. Iteration on the finite set of positive disagreements repeats a state and yields an alternating closed walk. Opposite Boolean values exclude a one-step loop. A shortest such walk has no repeated row or column, since either repetition would cut out a shorter alternating closed walk. Its length is therefore at least two, with separately distinct rows and columns and the required closing edge.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle`
