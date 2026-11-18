# Local order for the BKM metric adjoint

## Abstract

For every faithful nonflat finite complex density, a rotated projective measurement has an attainable Gibbs curve that obstructs positive recovery under local operator order.

**Definition 1.1 (Unitary basis change).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.basisChange`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.basisChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate a matrix by a unitary. Its inverse reads the matrix in that basis.

**Definition 1.2 (Logarithmic mean).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.logMean`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.logMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean is the difference quotient (x−y)/(log x−log y) for distinct arguments, with value x when the arguments coincide.

**Definition 1.3 (Coordinate projection).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.projector`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.projector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank-one projection has one at its selected diagonal entry and zero elsewhere.

**Definition 1.4 (Encoded measurement Kraus operator).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementKraus`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementKraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator is the coordinate projection multiplied on the right by V*. It takes the selected input-basis amplitude to the standard output coordinate.

**Definition 1.5 (Real quadratic form).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.quadratic`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate Re(z*Xz) for the given complex vector and matrix.

**Definition 1.6 (Two-coordinate Hadamard rotation).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.rotation`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.rotation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unitary acts as the normalized real Hadamard block on the selected distinct coordinates and is the identity on their complement.

**Definition 1.7 (Logarithmic-mean integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.omega`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a reference a and a matrix X, integrate a^u X a^(1−u) over the unit interval using the actual real spectral powers.

**Definition 1.8 (Adjoint of the encoded measurement).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementAdjoint`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementAdjoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear map takes the diagonal part of an output matrix and conjugates it by the unitary whose columns define the measurement basis.

**Definition 1.9 (Gibbs exponential).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.gibbs`

*Formalization.* `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.gibbs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For input reference a, output reference τ and measurement basis V, take the matrix exponential of log a plus the measurement adjoint of log Y minus log τ.

**Theorem 1.10 (Attainable local order obstruction).**

Lean statement: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurement_order_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurement_order_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an unequal eigenpair α>β>0 of a and apply a two-coordinate Hadamard rotation in its actual spectral basis. The resulting projective measurement with standard diagonal encoding is completely positive and trace preserving. Conjugation of the output by V gives the Lüders measurement. Its faithful output reference is τ. On all complex matrices the BKM metric adjoint E is the logarithmic-mean integral composed with the measurement adjoint and the resolvent logarithmic derivative. The spectral coefficients cancel in the metric pairing, including the equal-eigenvalue branch. The map E preserves trace and adjoints and sends τ to a. For the first selected output projection P, the quadratic form of E(P) on the specified vector is strictly negative. The line τ+t(P−τ) comes from faithful trace-one inputs near a on both sides of zero. The full matrix exponential derivative gives the Gibbs derivative E(P)−a. Local positive-semidefinite domination by a positive complex linear map R with R(τ)=a would give a scalar local minimum in the same vector, forcing the negative quadratic value on R(P). The conclusion concerns this additional two-sided order requirement. Trace preservation of R is unnecessary.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.basisChange`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.gibbs`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.logMean`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementAdjoint`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurementKraus`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.measurement_order_obstruction`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.omega`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.projector`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.quadratic`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction.rotation`
- Dependency: [D5/S3/Divergence/LogDerivTrace](../../Divergence/LogDerivTrace.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../Divergence/UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Matrix/ExponentialFirstResponse](../Matrix/ExponentialFirstResponse.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
