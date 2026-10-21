# Actual Gamma form core: FrequencyDomain

## Abstract

For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. The compact-core conclusions keep their original finite-energy hypotheses.

**Theorem 1.1 (actual gamma zero domain iff digamma weighted sum finite).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_gamma_zero_domain_iff_digamma_weighted_sum_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_gamma_zero_domain_iff_digamma_weighted_sum_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. The compact-core conclusions keep their original finite-energy hypotheses.

**Definition 1.2 (Literal finite Fourier sum).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actualFourierTruncation`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actualFourierTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For period d>0, base t, and a finite integer set S, the truncation is the sum of fourierCoeff(liftIoc(d,t,u),n)*exp(2*pi*i*n*x/d) over n in S. The coefficients use probability Haar measure. Equivalently each term is the physical coefficient sqrt(d)*fourierCoeff multiplied by the Lebesgue-normalized basis vector exp(2*pi*i*n*x/d)/sqrt(d).

**Theorem 1.3 (Fourier convergence in the actual Gamma form).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_fourier_truncation_form_core`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_fourier_truncation_form_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a>0 and let u be any complex L2 profile on (-a,a] with finite actual zero-extension Gamma energy. Every finite Fourier truncation and every residual belongs to that same zero-extension domain. As the finite integer set increases, the sum of the residual squared L2 mass and its actual zero-extension Gamma energy tends to zero. Parseval gives the physical mass tail, nonnegative digamma weights give the periodic energy tail, and E0<=EP+C(a)*mass gives the zero-extension energy limit. The residual domain hypotheses are proved before real integrals are used. No endpoint matching, parity or smoothness is imposed.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actualFourierTruncation`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_fourier_truncation_form_core`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_gamma_zero_domain_iff_digamma_weighted_sum_finite`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ArchimedeanJumpDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/DomainPassage](DomainPassage.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy](PeriodicSpectralEnergy.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport](../PeriodicEnergyTransport.md)
