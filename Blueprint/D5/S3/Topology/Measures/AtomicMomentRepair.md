# Exact moment repair with admissible atoms

## Abstract

Replace the zero cutoff while preserving five signed moments.

**Theorem 1.1 (Exact moment matching at arbitrarily small correction cost).**

Lean statement: `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the five-coordinate moment function be continuous from the right at zero. Fix five positive cutoff nodes in (0,1] whose moment columns form a basis. For any real weight on the zero cutoff and any strictly positive correction budget, a positive cutoff with the original weight and corrections on the five basis nodes have the same weighted moment as the zero cutoff. The sum of the absolute correction weights is strictly below the budget.

The reusable OmegaMath proof applies to a singleton family. Right continuity puts the zero-cutoff moment in the closure of the positive-cutoff moments. The proof takes the residual of a nearby admissible replacement in fixed basis coordinates and chooses the replacement where the sum of their absolute values is small.

For the total-variation application, assume a feasible finite atomic measure attains the closed-interval lower bound. Collect equal nodes and apply the theorem to the zero-cutoff atom if it occurs. Keep the remaining positive-cutoff atoms and weights. The repaired measure is feasible in the positive domain. Domain inclusion gives the closed minimum as a lower bound on its total variation. The triangle inequality bounds it above by the closed minimum plus the sum of the absolute correction weights. The correction budget is arbitrary, so the two infima agree.

## References

- Truth anchor: `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair`
