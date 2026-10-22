# Retained Creation Energy

## Abstract

Full retained energy Gaussian

The original lattice datum D has no positivity or occupation hypothesis. The charges a and b and every oscillator energy are unrestricted. F_e is the original correctedSource(a+b,creationCoeff(a,e)). Its retained polynomial contains every normal variable X(some i) and the shift X(none). The previously proved scalar G_e is an algebra evaluation, not a vacuum matrix element. Its scalar proof is reused without replacing the full retained polynomial.

**Theorem 1.1 (Full Retained Energy Convolution).**

$$\operatorname{FullRetainedEnergyRecurrence}\left(D, a, b, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian.actual_full_retained_energy_recurrence` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The exact original contraction and insertion equations yield (e+1) F_(e+1) as a finite convolution against the normal multiplier sum_l a_l X(some(l,k)) and C((k+1) h_(k+1)) X(none)^(k+1). The coefficient h is the original chargedEnergyLogCoefficient. The coordinate pairing is contracted before the finite triangular energy region is regrouped by total pair energy. The existing ordered-pair reflection supplies the half exactly once. No retained variable is evaluated away. Every summation is over its genuine finite energy support. This source-side polynomial identity does not establish a product-side recurrence or either all-j branch identity.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian.actual_full_retained_energy_recurrence`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCreationEnergyContraction](LatticeHalfFockCreationEnergyContraction.md)
