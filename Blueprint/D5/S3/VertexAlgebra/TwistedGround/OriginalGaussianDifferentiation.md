# Original Gaussian Operator and Resolvent Differentiation

## Abstract

Original Gaussian Operator and Resolvent Differentiation

The carrier, literal signed operator, original source and signed Neumann column are imported from their existing owners. The derivative owner keeps the same complex square-summable carrier and uses norm-absolutely convergent rank-one and coordinate-weighted series on the open unit disk.

The operator derivative is obtained by differentiating the actual rank-one series under a polynomial-geometric majorant. A general coordinate-weighted source family is differentiated in the norm of the original carrier, and the Neumann inverse is differentiated through its norm-controlled one-minus operator unit. The original column derivative is the derivative of the actual inverse column, with no determinant or trace interchange.

On the real radial interval, the frequency-weighted source supplies the literal rank-one identity for the radial operator derivative. The negative-sign resolvent moment is then computed from the differentiated normalized column and the existing positive weighted column pair. The result is a coefficient-model identity for the actual inverse of one minus the operator.

These results establish no determinant derivative exchange, determinant-period identity, endpoint asymptotic, physical Gaussian realization, vertex-operator-algebra construction, fusion or anomaly statement, string theory, or AdS/CFT realization.

**Definition 1.1 (operatorDerivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.operatorDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.operatorDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The norm-summable termwise derivative of the literal signed rank-one operator series on the complex unit disk.

**Theorem 1.2 (hasDerivAt_operator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_operator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z with norm less than one, the original operator has the displayed operator-norm derivative operatorDerivative z.

**Theorem 1.3 (hasDerivAt_sourceFamily).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_sourceFamily`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_sourceFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural coordinate weight j gives a norm-differentiable source family; its derivative raises the coordinate weight by one and lowers the complex power by one.

**Theorem 1.4 (hasDerivAt_resolvent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Neumann inverse of one minus the literal operator has derivative resolvent z multiplied on both sides of operatorDerivative z.

**Theorem 1.5 (hasDerivAt_columnSeries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_columnSeries`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_columnSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original inverse column, formed from the actual source family and signed resolvent, has the derivative obtained by the product rule for the resolvent and source.

**Theorem 1.6 (radial_operator_derivative_rankOne).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_operator_derivative_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_operator_derivative_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After multiplying by r, the radial operator derivative is one half of the rank-one map built from the actual weighted source and its unconjugated bilinear functional.

**Theorem 1.7 (bilinear_negative_resolvent_weighted_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r strictly between zero and one, the weighted source paired with the actual one-minus resolvent column is absolutely summable and equals 3r/(4(1-r)) minus 2r times the derivative of F divided by F, embedded into the complex numbers.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_columnSeries`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_operator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_resolvent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_sourceFamily`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.operatorDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_operator_derivative_rankOne`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent](OriginalGaussianResolvent.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent](OriginalGaussianWeightedResolvent.md)
