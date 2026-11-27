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

For positive cutoffs, the old vectors come from the closed cutoff interval, including the continuous limit at zero. A basis consists of five positive-cutoff moment columns. Moving the zero atom and correcting the five moments gives allowable measures with total variation approaching the closed-interval minimum. The spectral input, basis determinant, and dual contact check are separate certificate inputs.

## References

- Truth anchor: `D5/S3/Topology/Measures/AtomicMomentRepair.exists_exact_moment_repair`
