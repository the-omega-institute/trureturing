# Actual Gamma form core: LineFourier

## Abstract

For arbitrary complex F in L1(R) intersect L2(R), angularFourier(F,z) is the raw Fourier transform at z/(2*pi), with kernel exp(-i*z*x). Plancherel and the actual Gamma jump-energy identity use exactly 1/(2*pi). The energy identity is in ENNReal and permits infinite Gamma energy. The multiplier is Re digamma(1/4+i*z/2)-Re digamma(1/4), not a surrogate weight. For an Ioc L2 input, the literal PeriodicEnergyTransport.zeroExtension is L2 by zero_extension_memLp and L1 by finite interval measure and integrable_indicator_iff; this explains the application without adding a new zero-extension theorem here. No parity or reality restriction is imposed.

**Theorem 1.1 (continuous raw fourier).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integrable complex function on the real line, its raw Mathlib Fourier transform is continuous. Continuity follows from VectorFourier.fourierIntegral_continuous and supplies the measurability needed by the L1/L2 bridge and energy Tonelli proof.

**Theorem 1.2 (squared mass eq eLpNorm).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any AEStronglyMeasurable complex function, its extended squared mass is the square of its extended L2 seminorm. No MemLp or finite-mass hypothesis is added. The proof uses eLpNorm_nnreal_pow_eq_lintegral to relate the spatial and Fourier squared masses in the Plancherel bridge.

**Definition 1.3 (angularFourier).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The angular Fourier transform is the raw Fourier transform evaluated at z/(2*pi). The existing private integral calculation identifies the kernel exp(-i*z*x), fixing the sign and angular normalization for arbitrary complex inputs.

**Theorem 1.4 (angular extended plancherel).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex L1 and L2 input, extended spatial squared mass equals 1/(2*pi) times extended angular Fourier squared mass. The proof identifies the raw transform with the L2 transform almost everywhere and changes frequency variables by exactly 2*pi.

**Theorem 1.5 (raw fourier sub).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw transform of f-g is the pointwise difference of transforms when f and g are integrable complex functions. The integral_sub identity is used in the translation-gap calculation.

**Definition 1.6 (lineGapMass).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary squared translation-gap mass is the whole-line integral of norm(f(x)-f(x-s)) squared. In the energy proof each such integral is justified by the L2 hypothesis; finiteness of the subsequent Gamma-energy integral is not assumed.

**Definition 1.7 (actualDensity).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density is exp(-s/2)/(1-exp(-2*s)), selected from ArchimedeanJumpDecomposition.archimedeanJumpDensity. Its nonnegativity on positive rates, Levy kernel integrability and digamma evaluation supply the spectral weight identity.

**Definition 1.8 (actualIncrement).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual increment at real z is Re digamma(1/4+i*z/2)-Re digamma(1/4), with the displayed real-to-complex coercion and no clipping inside this real-valued definition.

**Definition 1.9 (cyclicGap).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The line phase-gap multiplier is 2*(1-cos((2*pi*xi)*s)). It retains both signs of xi and is used in the extended nonnegative frequency integral.

**Theorem 1.10 (actual line spectralWeight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real raw frequency xi, the nonnegative density-weighted phase-gap lintegral equals ofReal(actualIncrement(2*pi*xi)). Levy kernel integrability and nonnegativity convert the integral to a lintegral, and ArchimedeanJumpDecomposition.levy_integral_eq_digamma_increment evaluates it.

**Theorem 1.11 (actual gamma whole line energy eq angular integral).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex whole-line L1 and L2 input, the density-weighted translation-gap lintegral equals 1/(2*pi) times the actual-digamma-weighted angular Fourier squared-mass lintegral. Tonelli is applied before any finiteness restriction, so the ENNReal identity retains infinite Gamma energy.

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
