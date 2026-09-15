# Guarded Box Path Attainment

## Abstract

Guarded Box Path Attainment.

**Theorem 1.1 (Shortest successful unit words).**

Lean statement: `D5/S0/Rewriting/GuardedBoxPathAttainment.exists_shortest_word`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/GuardedBoxPathAttainment.exists_shortest_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set of natural coordinates with arbitrary natural capacities, any two configurations inside the box can be joined by a successful word of unit increases and decreases. Its length equals the sum of the absolute coordinate differences, and no successful word with the same endpoints is shorter. Moving a coordinate toward its endpoint keeps it between its current value and its target, so every guard succeeds. Each move reduces the remaining distance by one. At distance zero the empty word suffices. Zero-capacity coordinates require no instructions.

## References

- Truth anchor: `D5/S0/Rewriting/GuardedBoxPathAttainment.exists_shortest_word`
- Dependency: [D5/S0/Rewriting/GuardedBoxPaths](GuardedBoxPaths.md)
