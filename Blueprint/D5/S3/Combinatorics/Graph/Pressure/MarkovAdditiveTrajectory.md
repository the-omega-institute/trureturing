# Actual Markov trajectory prefixes and fixed-initial Doob scores

## Abstract

Actual Markov trajectory prefixes and fixed-initial Doob scores

**Theorem 1.1 (The actual trajectory prefix measure).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty state type with measurable singletons, the real stochastic matrix K determines a row PMF and an actual Markov kernel. Starting the homogeneous Kernel.trajMeasure at the fixed positive normalized stationary row pi of the reference matrix P, its first n+1 states have exactly the pushforward of initialPathPMF K n under (i,w) mapped to Fin.cons i w. The equality holds for every n including zero, every stochastic K, and every finite path, with zero transition masses retained. The proof applies the existing trajectory singleton product theorem and matches its n transition factors to the recursive path weight; finite measures are equal on all singleton masses.

**Theorem 1.2 (The global family has the corrected complete-path score).**

Lean statement: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty irreducible row-stochastic P and arbitrary directed reward g, the globally defined Doob kernel agrees near zero with the constructed implicit local family by normalized Perron uniqueness. On every path of positive base mass, the derivative at zero of the logarithm of its actual initialPathPMF mass is the sum of the corrected transition increments. The initial row pi is fixed throughout the family. This identifies the actual probability mass with the previously derived local score, without a moving-stationary-initial term or a quantum Fisher assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.globalDoob_path_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory.trajectory_prefix_eq`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal](MarkovAdditiveGlobal.md)
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths](MarkovAdditivePaths.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](../../../Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.md)
