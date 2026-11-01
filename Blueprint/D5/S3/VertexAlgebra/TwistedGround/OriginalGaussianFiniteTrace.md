# Original Gaussian Finite Trace Differentiation

## Abstract

Original Gaussian Finite Trace Differentiation

Entrywise matrix differentiation keeps the full noncommutative power differential until cyclicity is applied to the trace. The original weighted finite moments have a dimension-independent bound from an absolutely summable weighted-source majorant. The finite trace-log derivative is obtained by a derivative M-test on each interior radial interval.

These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.

**Definition 1.1 (traceFiniteWeight).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceFiniteWeight`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceFiniteWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original source coordinate multiplied by its positive physical frequency on the finite section.

**Definition 1.2 (finiteTraceMoment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite matrix-power moment with two original weighted source factors and no complex conjugation.

**Definition 1.3 (traceWeightBound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A polynomial-geometric coordinate bound at the enclosing radial radius.

**Definition 1.4 (traceWeightMass).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightMass`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the nonnegative coordinate majorant.

**Theorem 1.5 (traceWeightBound_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted coordinate majorant is summable for every nonnegative radius below one.

**Theorem 1.6 (traceWeightValue_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightValue_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightValue_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original signed weighted coordinate is bounded by the enclosing-radius majorant.

**Theorem 1.7 (finiteTraceMoment_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite power moment is bounded by the square of the majorant mass times the radial power, independently of the section dimension.

**Theorem 1.8 (finiteLog_hasDerivAt_traceMoments).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteLog_hasDerivAt_traceMoments`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteLog_hasDerivAt_traceMoments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite section and real r strictly between zero and one, the actual finite logarithm at sqrt r has derivative minus one over r times the sum of its odd weighted moments.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteLog_hasDerivAt_traceMoments`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceFiniteWeight`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightMass`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightValue_bound`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant](OriginalGaussianDeterminant.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent](OriginalGaussianWeightedResolvent.md)
