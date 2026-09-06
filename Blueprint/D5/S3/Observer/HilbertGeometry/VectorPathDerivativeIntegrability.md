# Vector Path Derivative Integrability

## Abstract

Bochner integrability of the totalized derivative of a vector path.

**Theorem 1.1 (Bounded variation gives an integrable derivative).**

$$\forall F: Type, [\operatorname{NormedAddCommGroup}\left(F\right)], [\operatorname{NormedSpace}\left(Real, F\right)], [\operatorname{CompleteSpace}\left(F\right)],\\{}\forall f: Real \to F, \forall a, b: Real, \operatorname{BoundedVariationOn}\left(f, \operatorname{uIcc}\left(a, b\right)\right) \implies \operatorname{IntervalIntegrable}\left(\operatorname{deriv}\left(f\right), volume, a, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability.bounded_variation_interval_integrable_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete real normed vector space F, every path f and all real endpoints a,b, bounded variation on the unordered closed interval implies Bochner interval integrability of deriv f with respect to Lebesgue measure. The proof bounds derivative norms by the derivative of the scalar accumulated variation and applies the monotone integrability theorem.

**Theorem 1.2 (Absolute continuity supplies derivative integrability).**

$$\forall F: Type, [\operatorname{NormedAddCommGroup}\left(F\right)], [\operatorname{NormedSpace}\left(Real, F\right)], [\operatorname{CompleteSpace}\left(F\right)],\\{}\forall f: Real \to F, \forall a, b: Real, \operatorname{AbsolutelyContinuousOnInterval}\left(f, a, b\right) \implies \operatorname{IntervalIntegrable}\left(\operatorname{deriv}\left(f\right), volume, a, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability.absolutely_continuous_interval_integrable_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same conclusion follows directly from AbsolutelyContinuousOnInterval through its bounded-variation theorem. This prerequisite has no dimension, separability, smoothness, or assumed reconstruction condition. The derivative is totalized to zero at nondifferentiable points. Almost-everywhere differentiability in Hilbert space, integral reconstruction, and the minimum and unique affine minimizer of path energy remain separate obligations; neither theorem here asserts them.

## References

- Truth anchor: `D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability.absolutely_continuous_interval_integrable_deriv`
- Truth anchor: `D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability.bounded_variation_interval_integrable_deriv`
