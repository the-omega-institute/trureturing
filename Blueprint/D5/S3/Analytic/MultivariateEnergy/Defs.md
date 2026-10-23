# Spherical energy definitions

## Abstract

Multivariate spherical energies and their averaged pair kernels.

**Theorem 1.1 (Normalized surface measure).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit sphere is the subtype of real Euclidean space of dimension d consisting of vectors of norm one. Surface measure is the spherical measure from radial disintegration of volume, multiplied by the inverse of its total mass. For positive d it is a Borel probability measure.

**Definition 1.2 (The averaged pair characterization).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.claim`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The characterization quantifies over every dimension at least two and every arity at least three. A continuous symmetric kernel invariant under orthogonal transformations is minimized by normalized surface measure exactly when its averaged pair kernel is conditionally positive definite. The latter property tests the quadratic energy of differences of two finite positive measures with equal total mass, which is the Jordan formulation for finite signed measures of mass zero.

The matrix feature is A(x)=xx transpose minus I/d. Its pair and triple traces define a symmetric family by averaging over all unordered pairs and triples of inputs. Increasing enumeration selects the indices in each subset. The energy uses the product of the same measure in every input; the averaged pair kernel integrates all inputs except the last two against normalized surface measure.

## References

- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.claim`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure`
