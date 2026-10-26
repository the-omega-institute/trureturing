# Source-weighted golden spectrum

## Abstract

Source-weighted golden spectrum

The native atom M is [0,1;1,1]. phi and psi are the expanding and contracting golden roots. spectralPlus=(M-psi I)/(phi-psi) and spectralMinus=(phi I-M)/(phi-psi). alpha(S) and eta(S) are their trace pairings with S. These definitions use the basis order of the actual acquisition matrix.

The source may have eta=0 or eta<0. Positivity is required only for alpha on legal sources. Every pure-M clock, including zero, uses the same literal trajectory and the same source.

**Theorem 1.1 (Source-weighted trace expansion).**

Lean statement: `D5/S3/Observer/Linear/GainRaySpectral.pureM_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRaySpectral.pureM_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 2 by 2 auxiliary matrix S and every natural i, trace(acquisition(replicate i false) S) equals alpha(S) phi^i + eta(S) psi^i. This is the weighted trace, rather than the trace of M^i alone.

**Theorem 1.2 (Legal source weights).**

Lean statement: `D5/S3/Observer/Linear/GainRaySpectral.legal_spectral_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRaySpectral.legal_spectral_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every P satisfying LegalSource P, alpha(P)>0 and alpha(P)+eta(P)=1. There is no sign or nonzero premise on eta(P).

**Theorem 1.3 (Independent auxiliary source coordinates).**

Lean statement: `D5/S3/Observer/Linear/GainRaySpectral.spectral_basis_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRaySpectral.spectral_basis_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

alpha(spectralPlus)=1, eta(spectralPlus)=0, alpha(spectralMinus)=0 and eta(spectralMinus)=1. The two projectors are auxiliary matrices in universal linear identities; they need not be legal positive sources.

**Theorem 1.4 (Literal clock expansion).**

Lean statement: `D5/S3/Observer/Linear/GainRaySpectral.pureM_readAt`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRaySpectral.pureM_readAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, original W:World d and natural n,i with i<=n, readAt W (replicate n false) i equals gain(d,W.coeff)(i) times [alpha(W.source) phi^i+eta(W.source) psi^i], plus W.drift. The coefficient vector, drift and clock are the original ones.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRaySpectral.legal_spectral_weights`
- Truth anchor: `D5/S3/Observer/Linear/GainRaySpectral.pureM_readAt`
- Truth anchor: `D5/S3/Observer/Linear/GainRaySpectral.pureM_spectral`
- Truth anchor: `D5/S3/Observer/Linear/GainRaySpectral.spectral_basis_weights`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Observer/Linear/GainRaySources](GainRaySources.md)
