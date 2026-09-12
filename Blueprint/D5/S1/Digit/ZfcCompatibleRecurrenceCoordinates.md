# Two-coordinate reconstruction for Fibonacci recurrences

## Abstract

Every Fibonacci recurrence observation has two integer coordinates, with an explicit reconstruction formula.

**Theorem 1.1 (Two initial coordinates reconstruct every recurrence observation).**

$$\forall n \in \mathbb{N},\ w(n) = G(n) \times (w(1) - w(0)) + H(n) \times (2 \times w(0) - w(1)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZfcCompatibleRecurrenceCoordinates.recurrence_two_coordinate_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A sequence satisfying w at n plus two equals w at n plus one plus w at n is determined by its first two values. The reconstruction uses the two integer-valued recurrence coordinates G and H, so it works in every additive commutative group.

The proof performs a genuine two-step induction and exposes the recurrence decomposition needed by the contextual arithmetic model. It does not formalize ZFC models, formula satisfaction, or the full Enc/Dec semantics.

## References

- Truth anchor: `D5/S1/Digit/ZfcCompatibleRecurrenceCoordinates.recurrence_two_coordinate_reconstruction`
- Dependency: [D5/S1/Digit/Raw](Raw.md)
