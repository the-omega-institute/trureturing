# Actual regular balanced Toeplitz generator

## Abstract

Actual regular balanced Toeplitz generator.

**Theorem 1.1 (Balanced heights form a divisibility scale).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.height_dvd_succ`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.height_dvd_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each balanced height divides its successor, by the literal multiplier 3 times the next factorial. This supplies the original skeleton scale for essential-period extraction; the heights themselves are not asserted essential.

**Theorem 1.2 (Shifted actual skeletons are nonempty).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_nonempty`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every height h(n+1), the same actual aligned point has a nonempty periodic-coordinate skeleton. Its actual density is bounded below by 1-(1/3)^(n+1), which is strictly positive. This explicitly avoids the empty initial h(0)-skeleton of the nonconstant point.

**Theorem 1.3 (Actual shifted heights cover every signed coordinate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_cover`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate period p supplied by the actual compact-limit Toeplitz construction divides (p+1) factorial and hence the later balanced height h(p+1). Therefore the concrete shifted height scale covers every signed coordinate, without assuming the scale coverage needed by the generic extraction theorem.

**Theorem 1.4 (A genuine essential period structure has density one).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_has_regular_period_structure`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_has_regular_period_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same actual aligned compact-limit point there exists a source period structure with strictly increasing positive essential periods, divisibility into each successor and coverage of every signed coordinate, whose actual normalized skeleton densities converge to one. Every extracted essential skeleton preserves its actual letters and holes. Compatible density rescaling transfers the balanced-height limit to the cofinal strict subsequence. Nonemptiness, coverage and aperiodicity needed by extraction are all discharged for this concrete point.

**Theorem 1.5 (One actual regular Toeplitz point generates the subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.exists_balanced_regular_toeplitz_generator`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.exists_balanced_regular_toeplitz_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One binary point in the actual balanced subshift has periodic coordinates for all signed multiples, has no positive global shift period, has orbit closure exactly the compact minimal balanced subshift, and admits an actual source essential period structure along which actual normalized skeleton densities converge to one. All clauses concern the same point. This supplies regular Toeplitzness in the source period-structure sense; strict ergodicity and lift splitting remain separate statements. Public escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726, so the mathematical proof and scoped report do not constitute declared_validated registration evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_has_regular_period_structure`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_cover`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.aligned_shifted_sites_nonempty`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.exists_balanced_regular_toeplitz_generator`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.height_dvd_succ`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure](EssentialPeriodStructure.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling](PeriodicSkeletonRescaling.md)
