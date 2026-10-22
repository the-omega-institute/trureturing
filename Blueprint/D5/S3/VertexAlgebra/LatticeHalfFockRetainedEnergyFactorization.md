# Retained Gaussian Factorization

## Abstract

Full retained creation-energy factorization

D is the unrestricted original lattice datum, and a,b range over its full integral charge group. The output charge is a+b; arbitrary output charge c is obtained by b=c-a. No positivity, rank restriction, occupation cutoff, or nonzero target coefficient is assumed. G is the actual energy scalar already identified with chargedEnergyGaussian. All retained oscillator variables and the distinguished shift variable remain independent.

**Theorem 1.1 (Full Polynomial Gaussian).**

$$\operatorname{RetainedEnergyGaussianFactorization}\left(D, a, b, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization.actual_retained_energy_gaussian_factorization` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The e-th original corrected creation coefficient equals the e-th coefficient of the normal creation exponential, renamed into X(some i), times the scalar-energy series with its e-th coefficient multiplied by X(none)^e. The scalar recurrence is reused, not re-proved or promoted from a vacuum projection. The derivative of the product has the full retained polynomial convolution derived from actual contraction and insertion. Strong induction and the genuine original coefficient F_0=1 identify the complete coefficients. The scalar-only statement cannot replace this full polynomial equality.

**Theorem 1.2 (Exact Finite Normal-Energy Expansion).**

$$\operatorname{RetainedEnergyFiniteGaussian}\left(D, a, b, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization.actual_retained_energy_finite_gaussian` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every e, the retained polynomial is the finite sum over 0<=n<=e of rename(some,creationCoeff(a,n)) times C(coeff(e-n,chargedEnergyGaussian(a,b))) times X(none)^(e-n). This keeps every normal frequency, repeated variable and shift. The original singleton and ordered-pair contributions enter G exactly once. Applying the existing native correction evaluation gives equality of the original fields and hence of every integer mode on an arbitrary actual target tensor, by finite linearity. This does not yet prove the regular charged-product scalar ratio, the two-sheet substitution, the complete Lambda/J jet comparison, or either original charged all-j endpoint.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization.actual_retained_energy_finite_gaussian`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization.actual_retained_energy_gaussian_factorization`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian](LatticeHalfFockRetainedEnergyGaussian.md)
