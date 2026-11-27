# Dimension thresholds for null-diamond angular modes

## Abstract

The leading angular model for null diamonds is summable in spacetime dimensions four and five.

The angular model isolates the multiplicity and leading eigenvalue used in comparing characteristic covariances in the trace criterion of Satishchandran and Sorce.

**Definition 1.1 (Harmonic multiplicity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the difference of the homogeneous polynomial dimension in degree ℓ and its counterpart in degree ℓ minus two. The second term vanishes for degrees zero and one.

**Theorem 1.2 (Multiplicity in four dimensions).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension four the multiplicity is 2ℓ + 1.

**Theorem 1.3 (Multiplicity in five dimensions).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_five`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension five the multiplicity is (ℓ + 1)².

**Theorem 1.4 (Multiplicity in six dimensions).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension six the multiplicity is (ℓ + 1)(ℓ + 2)(2ℓ + 3)/6. The proof gives the factor of six before taking the natural-number quotient.

**Theorem 1.5 (Uniform multiplicity bounds).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In each dimension D ≥ 4 the multiplicity lies between positive multiples of ℓ^(D − 3) for every ℓ ≥ 1. Two applications of Pascal's identity express the difference as a sum of two binomial coefficients of lower degree.

**Definition 1.6 (Leading angular mode weight).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Divide the multiplicity by the square of (ℓ + κ − 1)(ℓ + κ), with κ = (D − 2)/2. The weight omits the common amplitude.

**Theorem 1.7 (Exact summability window).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_summable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With the degree-zero term set to zero, the weight is summable exactly in dimensions four and five among D ≥ 4. The denominator has growth ℓ⁴. Apply the angular comparison theorem to the shifted sequence of positive degrees.

**Theorem 1.8 (Logarithmic cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_six_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_six_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

In dimension six the sum through degree L lies between positive multiples of log L for all L ≥ 2. The two bounds follow by comparison with the harmonic sum.

**Theorem 1.9 (Power-law cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_ge_seven_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_ge_seven_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 7 the sum through degree L lies between positive multiples of L^(D − 6) for all L ≥ 1. Compare the lower sum with the integral of the increasing power and bound every summand above by its value at the cutoff.

**Theorem 1.10 (Angular power singularity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angular_power_sq_integrable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angular_power_sq_integrable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 5 the product of the weight t^((D − 4)/2) and the square of t^(-(D − 4)/2) is integrable on (0, 2] exactly in dimension five. On positive t the combined exponent is −(D − 4)/2, which must be greater than −1.

**Definition 1.11 (Squared angular density).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use the squared logarithm in dimension four and the weighted squared power in higher dimensions, in the variable t measured from angular coincidence.

**Theorem 1.12 (Angular integrability window).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity_integrable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity_integrable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared angular density is integrable on (0, 2] exactly in dimensions four and five among D ≥ 4. The four-dimensional case uses the logarithmic square integral.

**Definition 1.13 (Conformal curvature coupling).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalCoupling`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The conformal coupling is (D − 2)/(4(D − 1)).

**Definition 1.14 (De Sitter scalar curvature).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterRicciScalar`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterRicciScalar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For Hubble parameter H the scalar curvature is D(D − 1)H².

**Definition 1.15 (Squared mass relative to the conformal reference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Add the squared mass to the scalar curvature times the displacement of the curvature coupling from its conformal value.

**Theorem 1.16 (Equivalent conformal subtraction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_eq_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_eq_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 4 the relative squared mass is the bare squared mass plus the coupling times the scalar curvature, minus κ(κ + 1)H².

**Theorem 1.17 (Massless conformal cancellation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_conformal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_conformal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At zero mass and conformal coupling the relative squared mass vanishes.

**Theorem 1.18 (Massless minimal coupling).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_minimal_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_minimal_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 4 and H > 0 the massless minimally coupled relative squared mass is strictly negative. It equals −κ(κ + 1)H².

**Theorem 1.19 (De Sitter leading mode sum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitter_leadingModeWeight_summable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitter_leadingModeWeight_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The sum with the squared relative mass coefficient converges exactly when that coefficient vanishes or the dimension is four or five. This conclusion concerns the leading angular sum.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angularSquaredDensity_integrable_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.angular_power_sq_integrable_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalCoupling`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_conformal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_eq_sub`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterConformalMassSq_minimal_neg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitterRicciScalar`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.deSitter_leadingModeWeight_summable_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_bounds`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_five`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_four`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.harmonicMult_six`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_ge_seven_bounds`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_sum_six_bounds`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold.leadingModeWeight_summable_iff`
- Dependency: [D5/S3/Geometry/Lorentz/DimensionSelection4D](../../../Geometry/Lorentz/DimensionSelection4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
