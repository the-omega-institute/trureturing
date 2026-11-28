# Equivariant Coefficients

## Abstract

Equivariant Coefficients

Archimedean Tate integral of slices of a rapid datum converges and is rapid. Mixed-model slice of a Schwartz-Bruhat datum as partial Fourier transform at places S. Finite slices of standard framed data along an isotropic subspace. Unit law of a tame character; idele of inverse uniformisers and its modulus. Fourier coefficient as functional of local datum, laws under shears and centre.

**Theorem 1.1 (exists_linear_centreCoeff).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients.exists_linear_centreCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients.exists_linear_centreCoeff` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

At each point x, Ψ ↦ (T-th Fourier coefficient of 𝒟Ψ) is a linear functional L on M. The shear of Ψ by z along the frame k at x stays in M and multiplies LΨ by ψ(tr(T_S z)), T_S = T divided by the idele invDifferentIdele, read at the ramified places S of 𝔠.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients.exists_linear_centreCoeff`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/StrongApproximation/EqualRankConstant](../../SiegelWeil/StrongApproximation/EqualRankConstant.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/ThetaIntegralLaws](../DualPair/ThetaIntegralLaws.md)
