# De Sitter null-diamond kernels

## Abstract

The de Sitter cone admits an exact area-weighted flux and a conformal kernel specialization.

The area-weighted field gives the characteristic flux in the conformal chart. The normalized Bunch–Davies differential equation identifies the first local mass term. The massless invariant differential equation gives a separate obstruction at the antipode.

**Definition 1.1 (Conformal radial map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsMobius`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsMobius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use f(u) = u/(T − u) along a null generator.

**Definition 1.2 (Conformal factor).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsOmega`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsOmega` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use Ω(u) = 1/(H(T − u)) on the expanding chart.

**Definition 1.3 (Affine parameter).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsAffine`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsAffine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Divide the radial map f by H²T to fix the affine normalization.

**Theorem 1.4 (Derivative of the radial map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For u < T, the derivative is T/(T − u)².

**Theorem 1.5 (Affine Jacobian).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With H and T positive, the affine derivative is Ω(u)².

**Theorem 1.6 (Characteristic Wronskian).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_flux_wronskian_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_flux_wronskian_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With the area radius ρ = uΩ, multiply each scalar profile by ρ raised to κ. In the skew pairing, the derivative of this factor cancels. The affine derivative cancels its Jacobian and the weight becomes ρ raised to 2κ.

**Theorem 1.7 (Logarithm under the radial map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Off the diagonal, the transformed real logarithm of the absolute difference is the original logarithm plus log T and the two separate logarithmic corrections.

**Theorem 1.8 (Off-diagonal mixed derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_mixed_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_mixed_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The correction depending on the second coordinate becomes constant when differentiated in that coordinate. The subsequent derivative in the first coordinate removes it.

**Theorem 1.9 (Affine boundary logarithm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The complex logarithms of the two real differences have the same boundary phase. Their difference almost everywhere is a real sum of separate radial terms.

**Theorem 1.10 (Weak mixed derivative of the affine correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_mixed_weak`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_mixed_weak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On each compact radial interval below T, the boundary logarithm difference pairs to zero against the product of the derivatives of two continuously differentiable test functions that vanish at both endpoints.

**Definition 1.11 (Chord variable).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsChord`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsChord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the two radial map values by y/4, where y denotes the angular separation variable.

**Theorem 1.12 (Area-weighted mixed derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mixed_product_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mixed_product_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The area weights cancel the chord power, leaving the constant H raised to −2κ times (4/y) raised to κ. Differentiating the remaining composition gives the radial logarithmic derivatives of f times the sum of s²Uʺ and sUʹ.

**Definition 1.13 (Bunch–Davies differential operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Apply the hypergeometric differential expression to the normalized kernel Y.

**Theorem 1.14 (Conformal constant solution).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE_conformal_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE_conformal_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At zero relative mass, the normalized Bunch–Davies operator annihilates the constant one.

**Theorem 1.15 (Conformal locus).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_parameter_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_parameter_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive H and D at least four, the mass after subtracting the conformal value and dividing by H² vanishes exactly when m² + (ξ − ξc)R vanishes.

**Definition 1.16 (Formal series operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdFormalODE`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdFormalODE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Replace the derivatives in the Bunch–Davies equation by formal differentiation on real power series.

**Theorem 1.17 (Frobenius recurrence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_frobenius_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_frobenius_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Compute each coefficient of the formal differential expression. It vanishes in every degree exactly when (j + 1)(j + 1 − κ) times the next coefficient equals (j(j + 1) + e) times the current coefficient.

**Theorem 1.18 (First mass coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_first_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_first_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With constant coefficient one and κ different from one, the linear coefficient is e/(1 − κ).

**Theorem 1.19 (Dimension-four analytic obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At κ = 1, the degree-zero recurrence of any normalized formal power series forces e = 0.

**Theorem 1.20 (Dimension-four logarithmic coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonant_log_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonant_log_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a twice differentiable solution of the dimension-four equation tending to one at the tip, the quotient (Y(s) − 1)/(s log s) tends to e. The equation controls the derivative of the weighted derivative (1 − s)²Yʹ(s).

**Definition 1.21 (Leading angular coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsLeadingCoefficient`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsLeadingCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The coefficient in positive harmonic degree is the product of the two radial derivatives and −e/(4π), divided by (ℓ + κ − 1)(ℓ + κ).

**Theorem 1.22 (Power and logarithmic angular moments).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_angular_coefficient_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_angular_coefficient_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Evaluate the closed angular moment at exponent 1 − κ for κ > 1, and differentiate it at exponent zero for κ = 1. Both calculations give the same normalized coefficient in positive harmonic degree.

**Theorem 1.23 (Sign of the leading mode).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_coefficient_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_coefficient_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For κ at least one and positive harmonic degree, all radial and angular factors are positive. The coefficient vanishes at e = 0 and otherwise has sign opposite to eH². The result applies to κ = 1 in dimension four and κ = 3/2 in dimension five.

**Theorem 1.24 (Exact conformal kernel equality).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_hypergeometric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_hypergeometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive κ and 0 < s < 1, the ordinary hypergeometric series at conformal parameters reduces to the binomial series for the power s raised to −κ. Cancelling the common Gamma factor yields the conformal kernel with its full normalization.

**Theorem 1.25 (Massless invariant antipodal obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.allen_folacci_antipodal_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.allen_folacci_antipodal_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On −1 < P < 1, multiplication by (1 − P²) raised to D/2 makes the derivative a constant. If that constant is nonzero, the magnitude of the derivative tends to infinity at the antipode. A one-sided comparison with a reciprocal power excludes every finite limit of the original kernel there when D is at least four.

**Theorem 1.26 (Lower bound near the tip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_blowup`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_blowup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For κ > 1 and κu ≤ (κ − 1)T/2, the negative derivative of u raised to 1 − κ and divided by T − u is at least (κ − 1)/(2T) times u raised to −κ.

**Theorem 1.27 (Interior zero of the unscaled derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_bound_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_bound_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension five, the unscaled radial derivative vanishes at T/3. Its magnitude therefore fails the proposed positive lower bound on the entire half interval.

**Definition 1.28 (Radius in modular coordinates).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsModularRadius`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsModularRadius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use the logistic map of slope 2π and range (0, L).

**Definition 1.29 (Unscaled leading radial kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsUnscaledModularKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsUnscaledModularKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the signed unscaled derivative by the modular Jacobian.

**Theorem 1.30 (Translation toward the tip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_packet_diverges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_packet_diverges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A nonnegative, nonzero smooth compactly supported packet has an unbounded pairing with the signed leading radial term as it translates toward the tip. Its weighted Fourier square integral is invariant under the same translations.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.allen_folacci_antipodal_obstruction`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdFormalODE`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bdODE_conformal_constant`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_hypergeometric`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_conformal_parameter_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_first_coefficient`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_frobenius_recurrence`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.bd_resonant_log_coefficient`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsAffine`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsChord`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsLeadingCoefficient`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsMobius`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsModularRadius`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsOmega`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.dsUnscaledModularKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_boundary_log_mixed_weak`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_affine_hasDerivAt`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_flux_wronskian_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_angular_coefficient_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_leading_coefficient_sign`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mixed_product_rule`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_hasDerivAt`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_mobius_log_mixed_deriv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_blowup`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_bound_counterexample`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel.ds_unscaled_packet_diverges`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold](NullDiamondDimensionThreshold.md)
