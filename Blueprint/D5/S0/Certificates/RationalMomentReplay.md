# Exact rational compression replay

## Abstract

A finite elimination trace is replayed against current weights. Every successful step preserves the same moments and removes support; the final dimension-dependent bound is checked separately.

**Definition 1.1 (Structurally recursive replay).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.replaySteps`

*Formalization.* `D5/S0/Certificates/RationalMomentReplay.replaySteps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Terminates on every finite input list and returns failure at the first invalid step. It does not discover null directions.

**Theorem 1.2 (Trace-wide invariants).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.replaySteps_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.replaySteps_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successful replay preserves nonnegativity, total mass, and all nominated moments. The final support is contained in the initial support, and each step consumes at least one support point.

**Theorem 1.3 (Normalized vectors retain an atom).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.activeAtoms_card_pos_of_total_one`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.activeAtoms_card_pos_of_total_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite vector whose total is one cannot have empty nonzero support.

**Theorem 1.4 (Bound successful trace length).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.replaySteps_length_lt_initial_support`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.replaySteps_length_lt_initial_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting from N active atoms in a probability vector, a successful trace has at most N-1 steps. This bounds accepted steps, not rational arithmetic bit complexity.

**Definition 1.5 (Complete certificate consumer).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.checkCompression`

*Formalization.* `D5/S0/Certificates/RationalMomentReplay.checkCompression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Checks initial normalization and nonnegativity, replays the supplied trace, and requires final support at most the number of retained features plus one.

**Theorem 1.6 (Certified sparse probability output).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.checkCompression_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.checkCompression_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acceptance yields a normalized nonnegative output with the same feature moments, contained support, and the stated terminal support bound.

**Theorem 1.7 (Preserve arbitrary support admissibility).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.checkCompression_preserves_support_predicate`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.checkCompression_preserves_support_predicate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every predicate satisfied by all initial nonzero atoms remains true for all output nonzero atoms. The predicate need not be linear or decidable.

**Theorem 1.8 (Closed exact accepted example).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.mean_preserving_replay_example`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.mean_preserving_replay_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A three-atom uniform law compresses to its middle atom while preserving its mean. The source includes an ordinary decide proof of the closed checker result.

**Theorem 1.9 (Reject a forbidden support revival).**

Lean statement: `D5/S0/Certificates/RationalMomentReplay.rejects_zero_atom_reactivation`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentReplay.rejects_zero_atom_reactivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A direction preserving mean and total would move mass into an initially zero middle atom. The inactive-coordinate check rejects that payload.

## References

- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.activeAtoms_card_pos_of_total_one`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.checkCompression`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.checkCompression_preserves_support_predicate`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.checkCompression_sound`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.mean_preserving_replay_example`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.rejects_zero_atom_reactivation`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.replaySteps`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.replaySteps_length_lt_initial_support`
- Truth anchor: `D5/S0/Certificates/RationalMomentReplay.replaySteps_sound`
- Dependency: [D5/S0/Certificates/RationalMomentElimination](RationalMomentElimination.md)
