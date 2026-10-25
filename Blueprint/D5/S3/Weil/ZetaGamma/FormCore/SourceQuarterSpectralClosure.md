# The original quarter-digamma graph closes from finite energies

## Abstract

Finite resolvents and the complete Hankel square series pay both graph directions.

**Theorem 1.1 (The original even and zero extensions have equivalent graphs).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_even_zero_domain_and_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_even_zero_domain_and_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary complex half-line L1 and L2 input, the actual bare-quarter weight W(xi)=Re(psi(1/4+i*xi))-Re(psi(1/4)) has equivalent weighted Fourier graph domains for the zero extension and its even extension. The domain equivalence is derived before the infinite energy identity. Finite energy identities E_N=2*U_N-S_N, nonnegative monotone convergence and the complete Hankel Laplace-square series supply the two uniform bounds. On the proved zero-extension graph, E=2*U-Re(Hankel(1/4,u)). No infinite identity or extra trace premise is assumed.

**Theorem 1.2 (The actual infinite reflected cross has a domain and value).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_reflected_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_reflected_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same L1 and L2 input on its original zero-extension quarter graph gives an integrable literal W-weighted Fourier cross, whose real integral is minus Re(Hankel(1/4,u))/2. Weighted AM-GM pays its complex domain. Polarization and the already derived graph identity pay its value. Equality with the literal even function u(abs(t)) is through an almost-everywhere identity at the origin; no value-u(0) restriction is introduced.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_even_zero_domain_and_identity`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_reflected_cross`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1](ActualGammaResidualL1.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](LineFourier.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/PositiveHankelL2](PositiveHankelL2.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal](SourceGammaOffDiagonal.md)
