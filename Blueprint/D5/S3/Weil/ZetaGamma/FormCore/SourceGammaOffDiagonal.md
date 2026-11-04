# The actual reflected Fourier kernels

## Abstract

The original L1 half-line input pays the reflected cross before inversion.

**Theorem 1.1 (The reflected cross uses the sum of the source coordinates).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_l1_reflected_unitary_cross_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_l1_reflected_unitary_cross_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex half-line L1 source u and complex full-line L1 multiplier p, the actual reflected unitary Fourier cross is integrable. Its integral equals the actual double half-line kernel integral. The operator kernel carries 1/(2*pi); its argument is s+t. These absolute-domain proofs precede Fubini.

**Theorem 1.2 (The actual resolvent kernel).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_inverse_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_inverse_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every real z, the actual L1 inverse multiplier kernel of 1/(xi^2+a^2) equals exp(-a*abs(z))/(2*a), with the original multiplier integrability retained.

**Theorem 1.3 (The original source Laplace square).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_reflected_cross_laplace_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_reflected_cross_laplace_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every complex half-line L1 input u, the actual reflected resolvent cross equals normSq(Laplace(a,u))/(2*a). Both the actual Laplace and spectral-product domains are proved in the same statement.

**Theorem 1.4 (The double pole retains its sign).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_inverse_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_inverse_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, the actual multiplier xi^2/[a*(xi^2+a^2)^2] has inverse kernel exp(-a*abs(z))*(1-a*abs(z))/(4*a^2). The proof computes the genuine exponential self-convolution. This signed kernel is retained, including its change of sign.

**Theorem 1.5 (The actual resonant reflected double integral).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and the original arbitrary complex L1 source, the resonant reflected spectral cross and its actual double half-line kernel integral agree. The sum s+t and signed kernel remain literal.

**Theorem 1.6 (The resonant first moment is explicit).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_laplace_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_laplace_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, the real resonant cross is normSq(Laplace(a,u))/(4*a^2) minus Re(conj(Laplace(a,u))*FirstMoment(a,u))/(2*a). The genuine first moment is integrable. The mixed term is retained in the later actual Gamma calculation; the kernel suppliers alone imply no energy positivity.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_l1_reflected_unitary_cross_kernel`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_inverse_kernel`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resolvent_reflected_cross_laplace_square`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_inverse_kernel`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_kernel`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal.actual_resonant_reflected_cross_laplace_moment`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile](ActualSuzukiLacunaryProfile.md)
