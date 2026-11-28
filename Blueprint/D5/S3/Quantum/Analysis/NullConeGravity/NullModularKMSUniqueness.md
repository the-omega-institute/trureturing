# Modular detailed balance and null-ray dynamics

## Abstract

Detailed balance determines the occupation multiplier. Its complementary symbol gives a bounded continuous strip correlator with an analytic interior, and the affine unitary transports null cuts by dilation.

The spectral calculation takes place on the Lebesgue frequency line. The positive thermal occupation is normalized using the reflected symbol from the null-diamond multiplier construction. The affine unitary gives the separate position-space action on the future half-line.

**Definition 1.1 (Normalized occupation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermal`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The inverse temperature β and frequency ν give the multiplier (1 + exp(−βν))⁻¹.

**Definition 1.2 (Covariance detailed balance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.DetailedBalance`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.DetailedBalance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The real covariance a and its skew part j satisfy a − j = exp(−βν)(a + j).

**Theorem 1.3 (Detailed-balance uniqueness).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_detailed_balance_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_detailed_balance_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For positive inverse temperature and nonzero frequency, the real detailed-balance equation has one solution for each skew symbol. The ratio of one plus the exponential to one minus the exponential equals the hyperbolic cotangent at half the scaled frequency.

**Theorem 1.4 (Normalized symbol uniqueness).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Solving the occupation balance equation yields the logistic multiplier and every such multiplier solves the equation.

**Theorem 1.5 (Occupation and reflection identities).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The logistic multiplier is strictly between zero and one at every real frequency. Reflection exchanges the occupation and its complement, and twice the occupation minus one equals the hyperbolic tangent of half the scaled frequency. Adding or subtracting that tangent from one yields twice the positive or reflected occupation respectively.

**Theorem 1.6 (Normalization of the null-cone multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_beta_two_pi_equals_nullA`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_beta_two_pi_equals_nullA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The multiplier convention uses the reflected frequency and half the existing null-cone symbol. Scaling frequency by twice pi gives the inverse-temperature convention of modular time.

**Definition 1.7 (Complex frequency phase).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.phase`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.phase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The complex time z and real frequency ν give exp(−izν).

**Definition 1.8 (Complex strip kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.stripKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.stripKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Multiply the complex frequency phase by (1 + exp(βν))⁻¹.

**Definition 1.9 (Complex strip correlation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kmsStrip`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kmsStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Integrate the product of the complex spectral density and the strip kernel over the real frequency line.

**Theorem 1.10 (Closed-strip integrability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The spectral multiplier with denominator one plus exp(βν) and phase exp(−izν) has absolute value at most one for imaginary part between zero and β. Thus every complex integrable spectral density gives an integrable kernel throughout the closed strip.

**Theorem 1.11 (Uniform closed-strip bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The absolute value of the correlation is at most the integral of the absolute value of the density on the whole closed strip.

**Theorem 1.12 (Continuity on the closed strip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Dominated convergence with the integrable norm of the density gives continuity, including at the two boundary lines.

**Theorem 1.13 (Holomorphy in the open strip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At each interior point there is a neighborhood separated from both boundaries by a positive distance. The derivative multiplier is bounded by |ν| exp(−δ|ν|) on that neighborhood, which gives an integrable dominating function and permits differentiation under the integral.

**Theorem 1.14 (Lower boundary).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_lower_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_lower_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At real modular time the strip kernel is the complementary thermal occupation times the real-time phase.

**Theorem 1.15 (Upper boundary).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_upper_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_upper_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At imaginary displacement β the phase acquires the factor exp(βν). This transforms the complementary occupation into the thermal occupation, with the real-time phase preserved.

**Definition 1.16 (Thermal multiplication operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermalOp`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermalOp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

On the Lebesgue Hilbert space of square-integrable complex functions, multiply by the normalized occupation.

**Definition 1.17 (Real-time spectral multiplication).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.spectralFlow`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.spectralFlow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

On the same frequency Hilbert space multiply by the complex exponential phase at real time.

**Theorem 1.18 (Hilbert-space boundary identities).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_boundary_identities`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_boundary_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The product of the conjugate of the first square-integrable vector and the second square-integrable vector is integrable by Hölder's inequality. The two boundary formulas become the corresponding inner products with the bounded spectral multipliers acting on the second vector.

**Theorem 1.19 (Uniqueness of inverse temperature).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_strip_determines_temperature`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_strip_determines_temperature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a nonnegative integrable spectral density supported on positive frequencies and having strictly positive total mass, the upper boundary at zero real time is strictly increasing with inverse temperature. Equality of two upper boundary values forces equality of the inverse temperatures.

**Definition 1.20 (Geometric coordinate dilation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.boostRay`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.boostRay` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The modular coordinate pullback sends x to exp(2πs)x.

**Theorem 1.21 (Future half-line invariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_preserves_halfline`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_preserves_halfline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The existing affine unitary acts almost everywhere by a positive coordinate dilation and a strictly positive scalar normalization. A vector supported on the positive half-line remains supported there.

**Theorem 1.22 (Geometric boost and transported cuts).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_ray_map`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_ray_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The dilation fixes the horizon at zero, composes by addition of modular times, and pulls the cut at a back to the cut at exp(−2πs)a. It preserves the positive half-line.

**Theorem 1.23 (Transport of cut-supported vectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

A square-integrable vector vanishes almost everywhere below a exactly when its modular evolution vanishes almost everywhere below exp(−2πs)a. The inverse dilation proves the reverse implication.

**Theorem 1.24 (Half-sided geometric inclusion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For nonnegative modular time and positive a, the original ray starting at a is contained in its pullback by the dilation. Conjugation of a translation by the inverse modular time action rescales its displacement by exp(2πs).

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.DetailedBalance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.boostRay`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_cut_inclusion`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_preserves_halfline`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.hsmi_modular_boost_ray_map`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kmsStrip`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_beta_two_pi_equals_nullA`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_detailed_balance_unique`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_properties`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_normalized_symbol_unique`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.kms_strip_determines_temperature`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_boundary_identities`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_lower_boundary`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_bounded`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_continuous`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_holomorphic`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_strip_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.modular_kms_upper_boundary`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.phase`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.spectralFlow`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.stripKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.thermalOp`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor](HyperfiniteTypeII1Factor.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
