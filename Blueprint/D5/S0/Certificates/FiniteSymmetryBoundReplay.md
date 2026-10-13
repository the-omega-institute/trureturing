# Finite symmetry bound replay

## Abstract

Kernel replay of partial bounds and rank-decreasing finite symmetry cuts.

**Theorem 1.1 (Partial lower bounds are sound).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.partial_lower_bound_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteSymmetryBoundReplay.partial_lower_bound_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact values on complete events and monotonicity under filling unknown coordinates imply the stored partial lower bound for every compatible event.

**Theorem 1.2 (Accepted trees prove a global bound).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.checked_global_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteSymmetryBoundReplay.checked_global_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on an actual natural rank rules out every bad event. A symmetry cut is accepted only with score preservation and strict descent.

**Theorem 1.3 (Concrete lexicographic descent).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.finite_lex_dominates_rank_lt`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteSymmetryBoundReplay.finite_lex_dominates_rank_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate permutations and outcome relabellings use a finite lexicographic order and a cardinality order isomorphism to Nat.

## References

- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.checked_global_lower_bound`
- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.finite_lex_dominates_rank_lt`
- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.partial_lower_bound_sound`
