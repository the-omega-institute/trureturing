# Frontier Retirement and Boundary Flow

## Abstract

The explicit edge-flow ledger verifies starts, all interior transitions, and both terminal geometries without adding a cycle condition.

**Definition 1.1 (Residual semitone boundary flow).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Retirement.boundaryFlow`

*Formalization.* `D5/S3/Combinatorics/Zigzag/Retirement.boundaryFlow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flow is an integer function on ZMod n. An edge contributes +1 at its source and -1 at its target; a configuration combines the five-state frontier with the running +1 charge. The final boundaryFlow is supported at the two semitone residues, so zero charge is exactly the remaining balance condition.

**Theorem 1.2 (The four admissible starts split by sign).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Retirement.start_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/Retirement.start_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only allowed class-two forms split into positive II/IV and negative III/V starts. Their distinct labels, initial states, and charges agree with PathData's two start tables. This establishes the beginning of the inverse classification.

**Theorem 1.3 (One labelled step preserves the flow invariant).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Retirement.transition_flow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/Retirement.transition_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each indexed transition, adding its low and high edges transforms the current frontier flow into the next configuration and adds precisely its stored charge. All twelve labels in each sector are checked; the shared topology alone would not prove this identity.

**Theorem 1.4 (The even antipodal pair retires the frontier).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Retirement.even_terminal_flow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/Retirement.even_terminal_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n=6r the last two classes form an antipodal pair. The six boundary positions are proved distinct for r>=1, and the sector-specific terminal labels leave only the recorded semitone charge. The odd singleton has its own theorem and cannot be inferred from this pair.

**Theorem 1.5 (The odd singleton retires the frontier).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Retirement.odd_terminal_flow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/Retirement.odd_terminal_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n=6r+3 one central class remains. Its single label and charge are checked in both sectors against the final boundary flow; using the even antipodal table here would change the counted object.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/Retirement.boundaryFlow`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Retirement.even_terminal_flow`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Retirement.odd_terminal_flow`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Retirement.start_classification`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Retirement.transition_flow`
- Dependency: [D5/S3/Combinatorics/Zigzag/PathData](PathData.md)
