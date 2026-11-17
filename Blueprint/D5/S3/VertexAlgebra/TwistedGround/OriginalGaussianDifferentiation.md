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

**Theorem 1.7 (derivative_shifted_geometric).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.derivative_shifted_geometric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.derivative_shifted_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural polynomial coordinate weight is summable against a positive geometric ratio strictly below one. This bound controls the differentiated source and central-binomial series.

**Definition 1.8 (sourceCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The single-coordinate coefficient of the original source family, including its inverse frequency square root.

**Definition 1.9 (sourceFamilyTerm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamilyTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamilyTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural coordinate weight and complex power multiply the original single-coordinate coefficient.

**Theorem 1.10 (sourceFamily_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural coordinate weight and every complex parameter of norm less than one, the original source-family terms are norm-absolutely summable.

**Theorem 1.11 (sourceFamily_apply).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate of the original source family equals the displayed half-binomial coefficient, coordinate weight and complex power divided by the frequency square root.

**Theorem 1.12 (sourceFamily_zero_eq_source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_zero_eq_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_zero_eq_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the square root of any real parameter in the half-open unit interval, the zeroth source family is the original source vector.

**Definition 1.13 (radialColumnDerivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumnDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumnDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real radial derivative of the original source column is the complex derivative scaled by the derivative of the square root.

**Definition 1.14 (radialNormalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialNormalization`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialNormalization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar normalization is the reciprocal of the real period times the square root of one minus the radial parameter.

**Theorem 1.15 (radial_column_derivative_scaled).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_column_derivative_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_column_derivative_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open real unit interval, the radial column derivative multiplied by the radial parameter is one half of the normalization times the original resolvent applied to the weighted source.

**Theorem 1.16 (bilinear_negative_resolvent_weighted_scalar).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r strictly between zero and one, the weighted source paired with the actual one-minus resolvent column is absolutely summable and equals 3r/(4(1-r)) minus 2r times the derivative of F divided by F, embedded into the complex numbers.

**Definition 1.17 (radialSourceFamily).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialSourceFamily`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialSourceFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original source family evaluated at the complex embedding of the real square root, with the natural frequency weight unchanged.

**Definition 1.18 (radialColumn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumn`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual source resolvent column evaluated at the complex embedding of the real square root.

**Theorem 1.19 (hasDerivAt_radial_sourceFamily).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j and every real 0<r<1, the jth radial source family has derivative the next weighted source divided by 2r.

**Theorem 1.20 (hasDerivAt_radial_column).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_column`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1, the actual radial column has derivative radialColumnDerivative r.

**Definition 1.21 (sourceBilinearFunctional).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original ordinary complex bilinear pairing is innerSL with star on the first vector.

**Theorem 1.22 (sourceBilinearFunctional_apply).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all square-summable complex vectors w and x, the original bilinear functional equals the sum of their coordinate products.

**Theorem 1.23 (sourceBilinearFunctional_smul_left).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original bilinear functional is complex linear in its first argument.

**Theorem 1.24 (sourceFamily_one_eq_weightedSource).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<=r<1, the first source family at sqrt(r) is the literal frequency-weighted original source.

**Theorem 1.25 (radial_pair_normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_pair_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_pair_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 0<r<1, one plus the ordinary bilinear pairing of the first radial source family with the radial column is the complex embedding of radialNormalization r.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.derivative_shifted_geometric`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_columnSeries`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_operator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_column`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_resolvent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_sourceFamily`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.operatorDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumnDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialNormalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialSourceFamily`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_column_derivative_scaled`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_operator_derivative_rankOne`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_pair_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamilyTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_zero_eq_source`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent](OriginalGaussianResolvent.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianWeightedResolvent](OriginalGaussianWeightedResolvent.md)
