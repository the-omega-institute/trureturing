# Every value branch and every symmetry edge is checked

## Abstract

Sound finite DAG replay of actual partial-event lower bounds.

Each row stores a partial assignment, an integer lower bound and either a complete event or a split with one earlier child for every possible value. Every split checks the recorded parent-to-child lower bound and exact assignment transport under its supplied symmetry. No canonicalization edge or external minimum is trusted.

**Theorem 1.1 (Factoring topology from terminal score calculations).**

Lean statement: `D5/S0/Certificates/FinitePartialBoundDAG.checked_structure_and_terminals`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FinitePartialBoundDAG.checked_structure_and_terminals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The structural checker validates every split and requires a terminal row to equal its complete event. Separate actual numerical inequalities for all terminal rows then yield full acceptance by the original checker. This allows the large finite topology to be replayed independently of expensive exact score evaluations, while retaining both obligations.

**Theorem 1.2 (Every accepted row bounds every compatible completion).**

Lean statement: `D5/S0/Certificates/FinitePartialBoundDAG.checked_rows_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FinitePartialBoundDAG.checked_rows_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction over earlier-child indices gives the recorded lower bound for every full event compatible with the row's actual partial assignment. A supplied event action must preserve the actual score, and its corresponding partial action must transport compatibility. Full branch coverage and these earned symmetry premises prevent a discarded completion from being silently omitted.

## References

- Truth anchor: `D5/S0/Certificates/FinitePartialBoundDAG.checked_rows_lower_bound`
- Truth anchor: `D5/S0/Certificates/FinitePartialBoundDAG.checked_structure_and_terminals`
- Dependency: [D5/S0/Certificates/FiniteSymmetryBoundReplay](FiniteSymmetryBoundReplay.md)
