# Fock Weyl irreducibility and squeezed-state disjointness

## Abstract

Coherent Weyl coefficients characterize the commutant on arbitrary mode index sets. Gaussian averaging detects finite-mode vacuum occupation and gives the exact criterion for a diagonal squeezed characteristic function to lie in the countable Fock folium.

**Definition 1.1 (Bounded Weyl displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.weylMap`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.weylMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

View the Weyl isometry as a bounded complex-linear operator.

**Theorem 1.2 (Scalar Fock Weyl commutant).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_commutant_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_commutant_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Weyl translation of the coherent kernel forces its vacuum column to be both holomorphic and antiholomorphic along each complex line. Density of coherent vectors then determines the commuting operator.

**Theorem 1.3 (Full Fock Weyl bicommutant).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_bicommutant_top`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_bicommutant_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Every bounded operator commutes with scalars, giving the full bounded operator algebra.

**Theorem 1.4 (Trivial Fock Weyl center).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_isFactor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_isFactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

An element of the center commutes with the Weyl displacements and hence acts by a scalar.

**Definition 1.5 (Squeezed characteristic function).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The diagonal covariance multiplies the squared real and imaginary quadratures by opposite exponential weights. For arbitrary parameters the characteristic function is used on finitely supported displacements.

**Theorem 1.6 (Weyl coefficient of the infinite squeeze).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_infiniteSqueeze`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_infiniteSqueeze` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The unit vector constructed from square-summable squeeze parameters realizes the characteristic function.

**Theorem 1.7 (Squeezed unit vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_of_summable_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_of_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The norm limit of finite product squeezes gives a single unit vector with the specified coefficients.

**Definition 1.8 (Finite-mode vacuum projection).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.vacuumProj`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.vacuumProj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The orthogonal coordinate projection keeps exactly the occupations that vanish on the selected modes.

**Theorem 1.9 (Gaussian Weyl average).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_gaussian_avg_eq_vacuumProj`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_gaussian_avg_eq_vacuumProj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate coherent matrix coefficients over finite complex coordinates with planar Lebesgue measure. The mixed Gaussian integrals erase the selected coherent coordinates. Boundedness and coherent totality identify the average with the projection.

**Theorem 1.10 (Anisotropic Gaussian average).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_gaussian_avg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_gaussian_avg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The two quadrature integrals in each mode give a reciprocal hyperbolic cosine. Finite product integration gives the product of those values.

**Definition 1.11 (Countable Fock folium).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.SqueezedInFockFolium`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.SqueezedInFockFolium` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A countable family of Fock vectors has unit total squared norm and reproduces the characteristic function on every finite set of modes.

**Theorem 1.12 (Exact square-summability criterion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Finite occupation sets capture more than half the total mass. Gaussian averages on modes disjoint from that set therefore bound the reciprocal hyperbolic-cosine products from below. The lower quadratic bound on the hyperbolic cosine gives summability.

**Theorem 1.13 (Excitability criterion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_excitable_iff_summable_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_excitable_iff_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Countable Fock excitability holds exactly when the squared squeezing parameters are summable.

**Theorem 1.14 (Non-excitability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_not_excitable_of_not_summable_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_not_excitable_of_not_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A nonsummable square family precludes a Fock folium representation.

**Theorem 1.15 (Strict disjointness of the pure squeezed state).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_gns_disjoint_of_not_summable_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_gns_disjoint_of_not_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Purity gives a scalar commutant for any cyclic realization of the state. Schur’s lemma would turn a nonzero bounded intertwiner into a unitary equivalence. The resulting Fock vector would reproduce the squeezed characteristic function on all finite-mode displacements, contradicting the summability obstruction.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.SqueezedInFockFolium`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_bicommutant_top`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_commutant_scalar`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_gaussian_avg_eq_vacuumProj`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.fockWeyl_isFactor`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_gaussian_avg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezedChar_infiniteSqueeze`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_excitable_iff_summable_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_gns_disjoint_of_not_summable_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_in_fock_folium_of_summable_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.squeezed_not_excitable_of_not_summable_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.vacuumProj`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness.weylMap`
- Dependency: [D5/S3/Quantum/Algebra/StateApproximation/IrreducibleBoundedLift](../../Algebra/StateApproximation/IrreducibleBoundedLift.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation](CCRFockOccupation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl](CCRFockWeyl.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite](CCRSqueezeInfinite.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState](CCRWeylState.md)
