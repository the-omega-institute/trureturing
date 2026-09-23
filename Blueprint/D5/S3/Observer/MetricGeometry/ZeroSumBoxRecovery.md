# Sharp Zero-Sum Box Recovery

## Abstract

The zero-sum plane has sharp joint box-noise recovery constant four thirds although every coordinate has scalar cost one.

**Definition 1.1 (Observation space).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.Data`

*Formalization.* `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.Data` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Data consists of all functions from Fin 3 to the real numbers. Its function-space norm is the maximum of the three absolute coordinate values.

**Definition 1.2 (Legal states).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.State`

*Formalization.* `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state is a data vector whose three coordinates sum to zero. Observation is the inclusion of this plane into Data; state error is measured by the ambient supremum norm of the difference.

**Definition 1.3 (Signed scalar representation costs).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.coefficientCosts`

*Formalization.* `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.coefficientCosts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a coordinate i, the attainable costs are the sums of absolute values of three real coefficients a, subject to the identity that the sum of a(j) times x(j) equals x(i) for every legal state x. Coefficients can have either sign; each observation has weight one. The full task family consists of exactly the three coordinates.

**Definition 1.4 (Worst-case risk of an arbitrary estimator).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.recoveryRisk`

*Formalization.* `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.recoveryRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real noise radius epsilon and any function R from Data to State, take the supremum over every pair consisting of a legal state x and a noise vector e with norm at most epsilon. The cost of this pair is the supremum norm of R(x+e)-x, embedded in the extended nonnegative reals. The same pair supplies both the observed datum and the state used in the loss. An unbounded estimator retains infinite risk. No linearity, continuity, measurability or exactness assumption is imposed on R.

**Definition 1.5 (A legal reconstruction).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.meanProjection`

*Formalization.* `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.meanProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reconstruction P subtracts one third of the sum of the input coordinates from each coordinate. Its output has sum zero for every datum, including data outside the observation image.

**Theorem 1.6 (Scalar cost one and attained joint risk four thirds).**

Lean statement: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.zero_sum_box_recovery_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.zero_sum_box_recovery_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon greater than or equal to zero, each coordinate's attainable coefficient-cost set has least element one. The supremum, over the three coordinates, of these infimal costs is therefore one. P fixes every legal state and, on every data vector e, its norm is at most four thirds of the norm of e. The infimum of recoveryRisk over all functions from Data to State is exactly the extended nonnegative value of four thirds times epsilon, and P attains that value. In particular the assertion includes zero noise.

The upper scalar cost uses a coefficient of one at the target coordinate and zero elsewhere. A legal vector with target coordinate one, another coordinate minus one and third coordinate zero forces every signed representation to cost at least one. For the joint lower bound, fix the common datum with all coordinates equal to minus epsilon divided by three. For each coordinate i, form a legal candidate with coordinate i equal to minus four epsilon divided by three and the other two coordinates equal to two epsilon divided by three. Subtracting that candidate from the common datum gives noise of norm exactly epsilon and reproduces the same datum. The legal output R at this datum has some nonnegative coordinate, forcing error at least four epsilon divided by three for the corresponding candidate. This construction also works at epsilon zero.

Each row of P has coefficients two thirds, minus one third and minus one third. Bounding each noise coordinate by its supremum norm proves the uniform projection bound. Since P fixes legal states, the reconstruction error at x+e equals P(e); this gives the matching risk upper bound. Three separate coordinate estimates can have error at most epsilon while their sum fails to vanish. The extra factor measures the requirement to return one common legal state for noisy data outside the true observation image. It does not change the scalar task constant on that image. The statement concerns this three-coordinate deterministic recovery model and does not assert a simplex transport or a theorem in arbitrary dimension.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.Data`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.State`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.coefficientCosts`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.meanProjection`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.recoveryRisk`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery.zero_sum_box_recovery_sharp`
- Dependency: [D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound](../MeasureSeparation/RobustMinimaxKernelBound.md)
