# Actual periodic-skeleton density exhaustion

## Abstract

Actual periodic-skeleton density exhaustion.

**Definition 1.1 (Actual periodic coordinate phases).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.phases`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.phases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a two-sided binary point y and a positive natural period p, the finite set consists of exactly those residue classes j in Z/pZ for which y(j+kp)=y(j) for every signed integer k. The chosen representative is j.val in the complete interval from zero to p-1. This is the actual periodic coordinate condition; no finite sampling or word approximation substitutes for it.

**Definition 1.2 (Periodic-skeleton density).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is the real number of actual periodic residue classes divided by the positive period p. This is the source periodic-skeleton count on one complete period. It does not assert that p is an essential period, that the sequence supplied later is an essential period structure, or that the point is nonperiodic.

**Theorem 1.3 (A density cannot exceed one).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density_le_one`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering the p-element residue space gives at most p periodic classes, so every actual periodic-skeleton density is at most one. This generic finite-count bound is consumed in the balanced limit proof.

**Theorem 1.4 (Shared columns are actual periodic phases).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.common_phases_subset_periodic_phases`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.common_phases_subset_periodic_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the actual aligned compact-limit point and a balanced level n. The actual origin-aligned marked tiling identifies each residue j with its physical offset j. Outside the literal word-disagreement set both tile types read the same symbol at that offset; tiled_common_column_periodic therefore proves equality at j+k h(n) for all integers k. Thus the complement of the disagreement set is included in the actual periodic skeleton.

**Theorem 1.5 (An integral bound on actual skeleton holes).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_phases_card_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_phases_card_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common-phase inclusion and the existing SparseDisagreement.wordDisagreements_card bridge imply h(n) is at most the number of actual periodic phases plus disagreementCount(n). The existing list mismatch recurrence is reused rather than reproved. Extra periodic phases are allowed; this theorem claims only a lower bound.

**Theorem 1.6 (An explicit geometric density bound).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual h(n)-periodic skeleton of the aligned point has density at least 1-(1/3)^n. Its proof divides the integral phase bound by the positive height and casts the previously proved exact rational word-disagreement fraction to the reals.

**Theorem 1.7 (Actual periodic skeletons exhaust density one).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_tendsto_one`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_tendsto_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual skeleton densities along the balanced heights converge to one: 1-(1/3)^n is a lower bound, one is an upper bound and the geometric error converges to zero. This is a faithful intermediate periodic-skeleton result. It supplies no essential-period extraction theorem, and hence does not by itself complete the primary source period-structure definition of regular Toeplitzness.

**Theorem 1.8 (One generator has all proved properties).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.exists_balanced_toeplitz_generator_with_density`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.exists_balanced_toeplitz_generator_with_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one binary point in the actual balanced subshift with periodic coordinates for all signed multiples, no positive global shift period, orbit closure exactly equal to that compact minimal subshift, and actual balanced-height periodic-skeleton densities converging to one. Every clause refers to the same actual aligned point. Essential-period structure, strict ergodicity and lift splitting are separate obligations. Public theorem escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the mathematical build and scoped axiom report do not constitute declared_validated registration evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_lower_bound`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_density_tendsto_one`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.aligned_periodic_phases_card_lower_bound`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.common_phases_subset_periodic_phases`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.density_le_one`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.exists_balanced_toeplitz_generator_with_density`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.phases`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal](BalancedMinimal.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement](SparseDisagreement.md)
