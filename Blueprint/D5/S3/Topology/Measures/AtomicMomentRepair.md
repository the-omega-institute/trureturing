# Exact moment repair with admissible atoms

## Abstract

Approximate signed atoms by admissible ones while matching moments exactly.

**Theorem 1.1 (Exact moment matching at arbitrarily small correction cost).**

Lean statement: `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite family of old moment vectors and their real signed weights. Each vector lies in the closure of the image of the admissible atoms. Fix a finite basis of moment vectors realized by admissible atoms. For every positive budget, choose one admissible atom per old vector, keeping its weight. A signed correction on the fixed basis restores the original weighted moment exactly. The sum of the absolute correction weights is strictly below the budget.

The residual is the original moment minus the weighted moment of the replacement family. Express it in the fixed basis. The sum of the absolute coordinates depends continuously on the replacement vectors and vanishes at the old vectors. The open set of families with small cost contains an admissible replacement family. Summing the correction in the fixed basis restores the target.

For the cutoff application, assume the moment function is continuous from the right at zero and five positive-cutoff moment columns form a basis. Take a feasible finite atomic measure on the closed cutoff interval whose total variation attains the closed-interval lower bound. Apply the theorem to the single zero-cutoff atom after collecting weights at equal nodes. Keep all its positive-cutoff atoms and weights, move the zero atom with its original weight, then add the correction on the five basis nodes. The repaired measure is feasible on the positive domain. Its total variation is at least the closed lower bound by domain inclusion. The triangle inequality bounds it above by the closed optimum plus the sum of the absolute correction weights. Since that sum is arbitrarily small, the two infima agree. The Arb certificate supplies the spectral input, positive-column determinant and closed-interval primal and dual checks.

## References

- Truth anchor: `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair`
