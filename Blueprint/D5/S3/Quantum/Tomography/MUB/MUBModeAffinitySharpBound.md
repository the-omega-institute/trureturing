# MUB Mode Affinity Sharp Bound

## Abstract

Rowwise collision thresholds constrain MUB mode affinity and double completions.

**Theorem 1.1 (Row collision bounds total affinity).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.one_le_modeAffinityTotal_of_row_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.one_le_modeAffinityTotal_of_row_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rowwise three-mode collision threshold gives a lower bound on total mode affinity.

**Theorem 1.2 (Row collision bounds mode mixing).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.modeMixingTotal_le_two_of_row_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.modeMixingTotal_le_two_of_row_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same rowwise threshold bounds total mode mixing by two.

**Theorem 1.3 (Affinity budget excludes two strict excesses).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_affinity_pair_above_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_affinity_pair_above_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two quantities each exceeding one cannot satisfy the two-dimensional budget.

**Theorem 1.4 (Affinity equality locus).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.affinity_pair_eq_one_of_lower_bounds_and_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.affinity_pair_eq_one_of_lower_bounds_and_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two lower bounds and the budget force both affinities to equal one.

**Theorem 1.5 (Completion pair affinity equality).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.completion_pair_forced_to_affinity_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.completion_pair_forced_to_affinity_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two rowwise collision bounds and the MUB budget force equality of both context affinities.

**Theorem 1.6 (Strict affinity excludes completion pair).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_completion_pair_of_affinity_strict_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_completion_pair_of_affinity_strict_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strict context-level lower bound above one excludes a pair satisfying the MUB budget.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.affinity_pair_eq_one_of_lower_bounds_and_budget`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.completion_pair_forced_to_affinity_one`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.modeMixingTotal_le_two_of_row_collision`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_affinity_pair_above_one`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.no_completion_pair_of_affinity_strict_lower_bound`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBModeAffinitySharpBound.one_le_modeAffinityTotal_of_row_collision`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget](MUBModeSymmetryBudget.md)
