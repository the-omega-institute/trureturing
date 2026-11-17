# Rigidity at zero exponential type

## Abstract

Phragmen-Lindelof damping and reflection connect growth to whole-plane constancy.

**Theorem 1.1 (A real-axis bound forces constancy).**

Lean statement: `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an entire complex function f bounded on the entire real axis by a real B, an arbitrarily small positive exponential growth bound on the whole plane implies f(z)=f(0) at every complex z. No positivity assumption on B or on the growth constants is added. Exponential damping, Mathlib Phragmen-Lindelof on a half-plane, removal of the damping, and the bounded entire function theorem prove the claim. This root is consumed by the reflection and zero-limit root in this module.

**Theorem 1.2 (Reflection and a vanishing ray limit).**

Lean statement: `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an entire zero exponential type f with f(1-z)=f(z), convergence to zero on the full positive real ray implies f is identically zero. Reflection bounds the negative tail and continuity bounds the middle compact interval, supplying the preceding real-axis theorem. SparseQuartetProduct.reflected_difference_zero consumes this result.

The bounds quantify over every positive real epsilon and every complex point; a limit along a discrete sequence is not the stated hypothesis. These analytic implications do not assert actual-zeta or RH rigidity and do not classify minimal type. All declarations are general analytic arguments rather than any of the four computational utility classes, so utility is none. Mathlib supplies the half-plane and Liouville tools; this module supplies their damping and reflection composition without a literature-novelty claim.

## References

- Truth anchor: `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real`
- Truth anchor: `D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero`
- Dependency: [D5/S3/Analytic/Entire/ExponentialPolynomial](ExponentialPolynomial.md)
