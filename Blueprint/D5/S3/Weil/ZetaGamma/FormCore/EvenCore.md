# Actual Gamma form core: EvenCore

## Abstract

For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.

**Theorem 1.1 (actual ioc exists weil test core approximation).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ArchimedeanJumpDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy](DirectionalEnergy.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget](ExteriorBudget.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation](InteriorApproximation.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/Mollifier](Mollifier.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/SmoothCore](SmoothCore.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport](../PeriodicEnergyTransport.md)
