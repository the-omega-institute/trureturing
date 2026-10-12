# Noncommutative edge return cycles

The existing face pairing induces concrete edge cycles.  The statements below use the
repository's `edgeRel` relation and its equivalence closure, so each step is an actual paired
face slot.

**Theorem 1.1 (Low-edge return cycle).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.low_edge_cycle`.

For every group `G`, opposite-group action on `Ω`, and `x : Ω`, the low edge labels follow

\[
0\longrightarrow3\longrightarrow5\longrightarrow0,
\]

while the right-action coordinates are successively multiplied by `v⁻¹`, `u`, and `u`.
Thus the three actual slots expose the return word `v⁻¹ * u²`.

**Theorem 1.2 (High-edge return cycle).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.high_edge_cycle`.

For every `x`, the high edge labels follow

\[
1\longrightarrow2\longrightarrow4\longrightarrow1,
\]

while the right-action coordinates are successively multiplied by `v`, `v`, and `u`.
Thus the three actual slots expose the return word `v² * u`.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.facePair`
- Truth anchor: `D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.slotMap`
- Dependency: `D5/S3/Geometry/Hyperideal/ActualCornerTransport`
