# The actual smooth periodic density model

## Abstract

The actual smooth periodic density model

**Theorem 1.1 (The actual smooth periodic density model).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel.gibbs_kl_from_smoothFP`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel.gibbs_kl_from_smoothFP` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The torus is Fin d to AddCircle 1 and its lifted space is EuclideanSpace over the same finite coordinate type. The measure is the product of normalized circle Haar measures. The density law is Haar measure with the original positive density. These definitions include dimension zero.

The potential and density are C infinity. The smoothness order is the coerced inner top of WithTop of the extended natural numbers; bare outer top would incorrectly require analytic functions. Joint density regularity is relative to the closed slab, with smooth spatial slices, strict positivity, normalization, and the original interior Fokker–Planck equation. No transport law or flow regularity is an input.

The representative in the half-open fundamental cell defines the gradient, divergence and chemical velocity. Quotient fibre identities transfer derivatives of periodic lifts without differentiating this representative. Compactness supplies a strictly positive lower bound for the density. The Gibbs law is normalized, its relative entropy is finite, and the actual free energy equals temperature times that entropy minus temperature times the logarithm of the partition function.

The existing normalized torus Haar pullback and tilted-measure KL identities are applied to these actual laws. The numerical and physical interpretation of this smooth continuum model is separate from this mathematical identity.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel.gibbs_kl_from_smoothFP`
