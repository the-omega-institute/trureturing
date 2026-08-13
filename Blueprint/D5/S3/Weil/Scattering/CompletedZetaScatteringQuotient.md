# Completed-Zeta Scattering Quotient

## Abstract

A real spectral parameter gives a unit-modulus quotient of the classical completed-zeta reading.

**Theorem 1.1 (Real spectral scattering quotient has unit norm).**

$$\forall t \in {\mathbb{R}},\; \operatorname{completedZetaReading}\left(\frac{1}{2} + t \cdot i\right) \ne 0 \Rightarrow \left\lVert \frac{\operatorname{completedZetaReading}\left(\frac{1}{2} - t \cdot i\right)}{\operatorname{completedZetaReading}\left(\frac{1}{2} + t \cdot i\right)} \right\rVert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/CompletedZetaScatteringQuotient.real_spectral_scattering_quotient_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the leading unitary clause of the source scattering form. For a real spectral parameter, the reflected completed-zeta values coincide by the functional equation, so their quotient has norm one when the denominator is nonzero.

The declaration is an honest partial closure. It does not define a scattering matrix, phase branch, zero-counting function, phase jumps, Wigner delay, numerical certificate, or physical interpretation; all of those source clauses remain unresolved.

## References

- Truth anchor: `D5/S3/Weil/Scattering/CompletedZetaScatteringQuotient.real_spectral_scattering_quotient_norm`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
