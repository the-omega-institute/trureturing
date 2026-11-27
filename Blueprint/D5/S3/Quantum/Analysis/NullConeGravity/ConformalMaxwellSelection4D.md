# Conformal Maxwell selection and de Sitter Proca modes

## Abstract

Four-dimensional Maxwell transport and the exact transverse and longitudinal Proca weights.

Appendix B.1 of Satishchandran and Sorce gives the Minkowski characteristic Maxwell flux and its radiative reference on the constrained space. The four-dimensional comparison uses fixed characteristic coordinates and the transported Gaussian data.

**Definition 1.1 (Maxwell conformal weight).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Raise the conformal scale to the integer exponent D − 4.

**Theorem 1.2 (Volume and inverse metric factors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_density_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_density_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a positive scale the volume factor is Ωᴰ and each inverse metric factor is Ω⁻². Their product is the Maxwell conformal weight.

**Theorem 1.3 (Selection by a single scale).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_at_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_at_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At any positive Ω different from one the weight equals one exactly when D = 4.

**Theorem 1.4 (Selection by all positive scales).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The weight equals one at every positive scale exactly when D = 4. The forward implication can use Ω = 2.

**Definition 1.5 (Raised field contraction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellFieldContraction`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellFieldContraction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Sum qᵢqⱼFᵢⱼ² over both indices, where q contains the inverse diagonal metric entries.

**Definition 1.6 (Diagonal-chart Maxwell stress tensor).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellStress`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellStress` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Contract one field index using q. Subtract the covariant metric component times one quarter of the full field contraction.

**Theorem 1.7 (Stress trace identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For nonzero inverse metric entries the trace is (4 − D)/4 times the field contraction.

**Theorem 1.8 (Stress trace selection).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For nonzero inverse metric entries and nonzero field contraction the trace vanishes exactly in dimension four.

**Definition 1.9 (Density-coordinate divergence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellChartDivergence`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellChartDivergence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Differentiate the weighted reference-raised field in each chart coordinate, sum over the first index, and divide by the volume scale Ωᴰ.

**Theorem 1.10 (Four-dimensional divergence identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_divergence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension four the derivative acts on the reference-raised field alone, with the factor Ω⁻⁴ outside the sum.

**Theorem 1.11 (Source-free field equation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_vacuum_equals_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_vacuum_equals_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At a point of positive conformal scale, the vanishing of every divergence component is equivalent to the reference source-free equation.

**Theorem 1.12 (Conformal scaling of the screen density).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_screen_density_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_screen_density_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a positive scale, multiply the cross-section volume weight Ω^(D − 2) by the inverse screen metric weight Ω⁻² to obtain the Maxwell conformal weight.

**Definition 1.13 (Characteristic Maxwell flux).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellCharacteristicFlux`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellCharacteristicFlux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate the antisymmetrized generator derivative paired by the reference densitized inverse screen metric. Scale the cross-section volume by Ω^(D − 2) and the inverse screen metric by Ω⁻². Use a plus sign in front of the oriented integral.

**Theorem 1.14 (Characteristic symplectic invariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_symplectic_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_symplectic_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a positive conformal scale in dimension four, the flux agrees with the flux at unit scale.

**Definition 1.15 (Regulated radiative pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellRadiativeKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellRadiativeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use Eq. (125) with the common constrained profiles and angular screen. Pair the profiles at two generator times and the same angle, use the inverse-square kernel (u₁ − u₂ − iε)⁻², and multiply the integral by −1/π. Include one four-dimensional weight at each generator time.

**Theorem 1.16 (Pointwise regulator invariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_radiative_kernel_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_radiative_kernel_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At every regulator the transported and reference radiative pairings agree.

**Theorem 1.17 (Equality of the transported Gaussian states).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_states_equal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_states_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On a common Weyl system, normalized states whose Gaussian coefficients use the two respective right limits of the regulated pairing agree. Uniqueness of the boundary limit identifies the covariances on every Weyl generator.

**Theorem 1.18 (Zero Hilbert–Schmidt defect).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_covariance_defect_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_covariance_defect_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If the matrix elements of two bounded operators realize the respective right limits of the transported and reference kernels, uniqueness of the limit identifies the operators. Their square-root difference is Hilbert–Schmidt with squared norm zero.

**Definition 1.19 (Proca rescaling exponent).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaBeta`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaBeta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Half the kinetic exponent, β = (D − 4)/2.

**Definition 1.20 (Transverse curvature coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaCurvaturePotential`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaCurvaturePotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The coefficient is β(β + 1).

**Theorem 1.21 (Factorization of the curvature coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiplying out gives (D − 4)(D − 2)/4.

**Theorem 1.22 (Curvature cancellation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 3 the curvature coefficient vanishes exactly in dimension four.

**Theorem 1.23 (Transverse Proca equation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_transverse_rescaled_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_transverse_rescaled_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For H > 0 and t < 0, use Ω = −1/(Ht) and v = ΩᵝA. The operator (Ω^(D − 4)A′)′ + Ω^(D − 4)(k² + Ω²m²)A equals Ωᵝ[v″ + (k² + Ω²m² − β(β + 1)/t²)v]. The identity uses differentiability of A at negative times and of its derivative at t.

**Definition 1.24 (Longitudinal quadratic density).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaLongitudinalDensity`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaLongitudinalDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For temporal component a and longitudinal derivative u, add Ω^(D − 4)(u − ka)²/2 and Ω^(D − 2)m²a²/2.

**Theorem 1.25 (Exact temporal-component elimination).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_longitudinal_kinetic_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_longitudinal_kinetic_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive Ω, k and m, put c = k² + Ω²m². The unique minimizer is a₀ = ku/c. The minimum is Ω^(D − 4)Ω²m²u²/(2c), and the excess at any a is Ω^(D − 4)c(a − a₀)²/2.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_states_equal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_conformal_symplectic_invariant`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_covariance_defect_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_divergence`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_radiative_kernel_invariant`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell4D_vacuum_equals_reference`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellCharacteristicFlux`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellChartDivergence`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_at_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellConformalWeight_eq_one_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellFieldContraction`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellRadiativeKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwellStress`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_density_scaling`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_screen_density_scaling`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.maxwell_stress_trace_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaBeta`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaCurvaturePotential`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.procaLongitudinalDensity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_curvature_potential_zero_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_longitudinal_kinetic_weight`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D.proca_transverse_rescaled_ode`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState](CCRWeylState.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
