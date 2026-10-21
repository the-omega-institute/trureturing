# Actual Gamma form core: LineFourier

## Abstract

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.1 (continuous raw fourier).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.2 (squared mass eq eLpNorm).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Definition 1.3 (angularFourier).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.4 (angular extended plancherel).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.5 (raw fourier sub).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Definition 1.6 (lineGapMass).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Definition 1.7 (actualDensity).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Definition 1.8 (actualIncrement).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Definition 1.9 (cyclicGap).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.10 (actual line spectralWeight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

**Theorem 1.11 (actual gamma whole line energy eq angular integral).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ArchimedeanJumpDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport](../PeriodicEnergyTransport.md)
