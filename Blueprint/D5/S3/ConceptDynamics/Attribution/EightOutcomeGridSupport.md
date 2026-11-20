# Three regular orbits are necessary and sufficient

## Abstract

The exact seed support for the denominator 210 grid on eight labels.

**Theorem 1.1 (Exact seed budget for eight labels and denominator 210).**

$$\forall B, \operatorname{SeedBudget}\left(8, 210, B\right) \iff 120960 \le B$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/EightOutcomeGridSupport.grid_support_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SeedBudget(k,m,B) means there is a finite seed set of cardinality at most B with an action of all permutations of the k labels. The invariant real seed weights are positive and sum to one. A single deterministic equivariant readout reproduces each coordinate divided by m for every natural profile of total m.

The primes at most eight divide 210, so the prime-cycle profile test forces regular seed orbits. A tied-coordinate profile can prescribe every integer from zero to thirty in denominator units. In each regular orbit eight stabilizer blocks supply a digit between zero and eight for a tied label. At least two orbits are required by the number of distinct digit vectors. For two orbits their scaled weights sum to fifteen quarters by normalization. The code bound for integer masses on two-digit diagonals leaves only twenty-seven codes, fewer than the thirty-one required levels.

The complete-grid theorem gives three orbits at denominator 1680. Multiplying each input coordinate by eight embeds the coarser profiles in that grid. This embedding commutes with label permutations and preserves every coordinate divided by its denominator.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/EightOutcomeGridSupport.grid_support_budget_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/PermutationGridSupport](PermutationGridSupport.md)
