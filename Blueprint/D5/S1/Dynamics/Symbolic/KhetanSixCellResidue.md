# Residue propagation at the six-cell Nivat boundary

## Abstract

Exact adjacent-column residue partitions force a horizontal or vertical period.

This module isolates the combinatorial core of the six-cell boundary discussed by Khetan. The hypotheses are the exact XOR partition of every adjacent pair of columns and their disjointness. The one-dimensional three-point tiling rigidity and the orbit-closure extraction remain separate obligations; this theorem therefore records a conditional residue-propagation result rather than a resolution of the full open problem.

**Theorem 1.1 (Residue change forces a period).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSixCellResidue.three_residue_column_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSixCellResidue.three_residue_column_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a column predicate T and integer residue labels r, assume that exactly one of the two adjacent column memberships holds precisely when y has residue r(x) modulo 3, and assume adjacent memberships are disjoint. If the labels are constant modulo 3, XOR cancellation gives T(x+2,y) ↔ T(x,y). If a label changes, the middle column is empty; periodicity propagates from that empty column in both integer directions, giving T(x,y+3) ↔ T(x,y) for every column.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSixCellResidue.three_residue_column_dichotomy`
