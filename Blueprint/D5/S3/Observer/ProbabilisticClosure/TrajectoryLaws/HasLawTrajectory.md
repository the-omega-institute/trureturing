# Own-history conditional distributions determine the trajectory law

## Abstract

Own-history conditional distributions determine the trajectory law.

**Theorem 1.1 (Own-history conditional distributions determine the trajectory law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory.has_law_traj_measure`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory.has_law_traj_measure` (`✓ std3`). ∎

*Citation.* Rémy Degenne and Paulo Rauber (2026). *Own-history conditional distributions determine the trajectory law*. URL: <https://github.com/LeanMachineLearning/LML/tree/357e9dd450b76d6ff85955280bb4721a2c520442>.

*Commentary.*

For any measurable sample space with a finite measure, measurable coordinates with the specified initial probability law and own-history conditional distributions have the corresponding Ionescu--Tulcea trajectory law.

The initial law is a probability measure; the actual sample measure need only be finite. Coordinates may have dependent measurable types. Each successor conditional law is given the coordinates through the current time. The finite-history induction and projective-limit uniqueness identify the complete trajectory distribution.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory.has_law_traj_measure`
