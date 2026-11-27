# Ricci-flat plane-wave point-cone shear

## Abstract

Exact pre-caustic screen forms give a nonzero angular mismatch with inverse-square growth.

For positive tidal amplitude α, work with affine pairs 0 < u < v < π/α on the point cone. The oscillatory and hyperbolic Jacobi factors yield two distinct positive screen coefficients. This distinction gives a strictly positive axial mismatch on every separated pre-caustic radial rectangle.

**Definition 1.1 (Oscillatory Rosen factor).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Roger Penrose (1965). *A Remarkable Property of Plane Waves in General Relativity*. DOI: [10.1103/RevModPhys.37.215](https://doi.org/10.1103/RevModPhys.37.215). URL: <https://doi.org/10.1103/RevModPhys.37.215>.

*Commentary.*

The factor at u is sin(αu) divided by α.

**Definition 1.2 (Hyperbolic Rosen factor).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Roger Penrose (1965). *A Remarkable Property of Plane Waves in General Relativity*. DOI: [10.1103/RevModPhys.37.215](https://doi.org/10.1103/RevModPhys.37.215). URL: <https://doi.org/10.1103/RevModPhys.37.215>.

*Commentary.*

The factor at u is sinh(αu) divided by α.

**Theorem 1.3 (Vertex Jacobi propagator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_vertex_jacobian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_vertex_jacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Roger Penrose (1965). *A Remarkable Property of Plane Waves in General Relativity*. DOI: [10.1103/RevModPhys.37.215](https://doi.org/10.1103/RevModPhys.37.215). URL: <https://doi.org/10.1103/RevModPhys.37.215>.

*Commentary.*

The vertex Jacobian has the hyperbolic and oscillatory factors on its diagonal, in that order.

**Theorem 1.4 (Oscillatory Jacobi equation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For α > 0, the first derivative at u is cos(αu) and its derivative is −α² times the oscillatory factor.

**Theorem 1.5 (Hyperbolic Jacobi equation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For α > 0, the first derivative at u is cosh(αu) and its derivative is α² times the hyperbolic factor.

**Theorem 1.6 (Jacobi data at the tip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_tip_initial_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_tip_initial_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For α > 0 both factors start at zero with unit affine derivative.

**Theorem 1.7 (Cancellation of the Ricci trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_ricci_flat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_ricci_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At every positive affine parameter before the first caustic, the ratios of the second derivatives to their factors are −α² and α². Their sum is zero.

**Definition 1.8 (Oscillatory Synge coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the endpoint oscillatory factors by α(v−u) divided by sin(α(v−u)).

**Definition 1.9 (Hyperbolic Synge coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the endpoint hyperbolic factors by α(v−u) divided by sinh(α(v−u)).

**Theorem 1.10 (Inverse oscillatory screen integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For 0 < u < v < π/α and α > 0, divide v−u by the integral of the inverse square of the oscillatory factor. The antiderivative is −α cot(αu) at an affine argument u.

**Theorem 1.11 (Inverse hyperbolic screen integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For 0 < u < v and α > 0, divide v−u by the integral of the inverse square of the hyperbolic factor. The antiderivative is −α coth(αu) at an affine argument u.

**Theorem 1.12 (Strict ordering of the screen coefficients).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_lt_syngeQy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_lt_syngeQy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The oscillatory coefficient is strictly positive and strictly below the hyperbolic coefficient on every positive pre-caustic pair. The inverse-square oscillatory integrand strictly exceeds its hyperbolic counterpart on the affine segment.

**Definition 1.13 (Area-normalized angular factor).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Divide the square root of the product of the two screen coefficients by the directional screen form with angular components cos θ and sin θ.

**Definition 1.14 (Radial rectangle mismatch).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The four-corner difference adds the upper-upper and lower-lower values and subtracts the other two values of the angular factor.

**Theorem 1.15 (Angular factor on the oscillatory axis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_axis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a positive pre-caustic pair the value at θ = 0 equals the square root of the hyperbolic coefficient divided by the oscillatory one.

**Theorem 1.16 (Strictly positive axial mismatch).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_axis_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_axis_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Write the axial factor as the exponential of half the sum of log(sinh t / sin t) at αu and αv minus the same function at α(v−u). The slope of this logarithmic ratio is positive and strictly increasing on (0, π). Differentiation in u shows that the axial difference between the two fixed v values strictly increases from u₁ to u₂.

**Theorem 1.17 (Nonzero rectangles arbitrarily near the tip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.exists_rectMismatch_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.exists_rectMismatch_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive cutoff δ at or below the first caustic, the four affine parameters δ/5, 2δ/5, 3δ/5 and 4δ/5 give a nonzero axial mismatch.

**Definition 1.18 (Poisson parameter).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Divide the difference of the hyperbolic and oscillatory square roots by their sum.

**Theorem 1.19 (Strict Poisson parameter bounds).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter_mem_Ioo`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter_mem_Ioo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Strict ordering of the positive screen coefficients places the parameter strictly between zero and one.

**Theorem 1.20 (Poisson representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_eq_poisson`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_eq_poisson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The angular factor equals the disk Poisson kernel with the stated parameter at twice the screen angle.

**Theorem 1.21 (Unit angular average).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_average`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The integral of the angular factor over a full turn, divided by 2π, is one for each positive pre-caustic pair.

**Theorem 1.22 (Exact angular inner product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For two positive pre-caustic pairs with Poisson parameters s and t, the integral of the product of their angular factors over a full turn is 2π(1+st)/(1−st).

**Theorem 1.23 (Positive squared angular mismatch).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_integral_sq_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_integral_sq_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Continuity and the positive axial value give a strictly positive integral of the squared mismatch over a full turn.

**Theorem 1.24 (Zero shear for a scalar screen).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.screen_zero_shear`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.screen_zero_shear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

When two positive screen coefficients agree at all radial pairs, the normalized angular factor is one at every angle and its four-corner difference is zero.

**Theorem 1.25 (Exact polar annulus integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_squared`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For 0 < ε < ρ, the integral of the squared mismatch kernel with polar measure equals half the squared angular integral times the difference of the inverse squared radii, ε⁻²−ρ⁻².

**Theorem 1.26 (Divergence at angular coincidence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_diverges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_diverges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With a fixed positive outer radius, the annular square integral for every separated pre-caustic radial rectangle tends to positive infinity as the inner radius decreases to zero.

**Theorem 1.27 (Inverse-square growth on a sector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_kernel_not_L2_on_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_kernel_not_L2_on_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On two copies of a positive-radius screen ball, an almost-everywhere positive inverse-square lower bound for the modulus at small nonzero separations in a nonempty angular sector excludes square integrability for the product of the restricted volume measures.

**Definition 1.28 (Plane-wave shear kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWavePointConeShearKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWavePointConeShearKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For distinct screen endpoints, divide the angular mismatch at the displacement angle by π² times the squared displacement norm.

**Theorem 1.29 (Plane-wave obstruction on every screen ball).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWave_pointCone_shear_not_L2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWave_pointCone_shear_not_L2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A continuous angular mismatch with positive axial value gives a sector of inverse-square growth. Every separated pre-caustic rectangle therefore gives a shear kernel outside L² on every positive-radius screen ball.

**Theorem 1.30 (Kernel of a Hilbert–Schmidt operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hilbertSchmidt_has_integral_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hilbertSchmidt_has_integral_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On complex L² of an s-finite measure, a Hilbert–Schmidt operator is induced by a square-integrable product kernel. The square-summable images of an orthonormal basis give the kernel through an orthogonal series of separated factors.

**Definition 1.31 (Off-diagonal representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.RepresentsKernelOffDiagonal`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.RepresentsKernelOffDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On positively separated measurable rectangles, the kernel is integrable and its integral agrees with the operator pairing of the corresponding indicator functions.

**Theorem 1.32 (Hilbert–Schmidt obstruction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_obstruction_no_hilbertSchmidt_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_obstruction_no_hilbertSchmidt_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A Hilbert–Schmidt operator representing the wedge-singular kernel off the diagonal would supply a square-integrable representative with the same indicator pairings. These pairings determine the kernel almost everywhere off the diagonal, where the inverse-square lower bound forces divergence.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.RepresentsKernelOffDiagonal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.exists_rectMismatch_ne_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_average`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_axis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_eq_poisson`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardAnisotropy_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hadamardPoissonParameter_mem_Ioo`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.hilbertSchmidt_has_integral_kernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWavePointConeShearKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.planeWave_pointCone_shear_not_L2`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_diverges`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_annulus_squared`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_axis_pos`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rectMismatch_integral_sq_pos`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenP_jacobi`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosenQ_jacobi`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_ricci_flat`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_tip_initial_conditions`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.rosen_vertex_jacobian`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.screen_zero_shear`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_kernel_not_L2_on_ball`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.shear_obstruction_no_hilbertSchmidt_kernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_eq_integral`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQx_lt_syngeQy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D.syngeQy_eq_integral`
- Dependency: [D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D](../../../Geometry/Lorentz/PerturbedCausalOrderWeyl4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS](NullDiamondKernelHS.md)
