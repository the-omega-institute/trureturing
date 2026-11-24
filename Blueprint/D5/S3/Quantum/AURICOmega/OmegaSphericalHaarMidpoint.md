# Haar characters, spherical laws, and midpoint drift

## Abstract

Exact rational character identities, squared spherical triangle laws, and midpoint quaternion evolution.

**Theorem 1.1 (Even-character product expansion).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N},\; \operatorname{Coefficientwise}\left(\operatorname{polyMul}\left(\operatorname{character}\left(m\right), \operatorname{character}\left(n\right)\right), \operatorname{characterSum}\left(m, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.evenChar_product_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The character polynomials start with 1 and 4κ − 1, then follow the recurrence with multiplier 4κ − 2. The character sum runs from |m − n| through m + n, inclusive. Coefficientwise comparison assigns zero to omitted entries. Induction applies the character recurrence to a whole interval and cancels the overlapping terms.

**Theorem 1.2 (Haar expectation in every degree).**

$$\forall r \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{Haar}\left(\operatorname{character}\left(r\right)\right), \operatorname{delta}\left(r, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.haar_evenChar_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted factorial moment recurrence determines the expectation for every character. The value is one at degree zero and zero at every positive degree.

**Theorem 1.3 (Even-character Haar orthonormality).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{HaarInner}\left(\operatorname{character}\left(m\right), \operatorname{character}\left(n\right)\right), \operatorname{delta}\left(m, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.all_degree_peter_weyl_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the factorial moment functional to the product expansion. The degree-zero character occurs exactly when the two indices coincide.

**Theorem 1.4 (Squared spherical sine law).**

$$\forall a \in \mathbb{Z}^{4}, b \in \mathbb{Z}^{4}, c \in \mathbb{Z}^{4},\; \left(\left(a \ne 0 \land \left(b \ne 0 \land c \ne 0\right)\right) \land \left(\operatorname{spread}\left(a, b\right) \ne 0 \land \left(\operatorname{spread}\left(b, c\right) \ne 0 \land \operatorname{spread}\left(c, a\right) \ne 0\right)\right)\right) \Rightarrow \left(\operatorname{Equivalent}\left(\frac{\operatorname{vertexSpread}\left(a, b, c\right)}{\operatorname{spread}\left(b, c\right)}, \frac{\operatorname{vertexSpread}\left(b, c, a\right)}{\operatorname{spread}\left(c, a\right)}\right) \land \operatorname{Equivalent}\left(\frac{\operatorname{vertexSpread}\left(b, c, a\right)}{\operatorname{spread}\left(c, a\right)}, \frac{\operatorname{vertexSpread}\left(c, a, b\right)}{\operatorname{spread}\left(a, b\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.rational_spherical_sine_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge spread is one minus projective fidelity. The vertex spread is the normalized Gram determinant divided by the product of the incident spreads. Dividing each vertex spread by the opposite spread gives the same ratio by cyclic invariance of the determinant.

**Theorem 1.5 (Squared spherical Pythagorean law).**

$$\forall a \in \mathbb{Z}^{4}, b \in \mathbb{Z}^{4}, c \in \mathbb{Z}^{4},\; \left(\left(a \ne 0 \land \left(b \ne 0 \land c \ne 0\right)\right) \land \operatorname{dot}\left(a, a\right) \cdot \operatorname{dot}\left(b, c\right) = \operatorname{dot}\left(a, b\right) \cdot \operatorname{dot}\left(a, c\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(b, c\right), \operatorname{kappa}\left(a, b\right) \cdot \operatorname{kappa}\left(c, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.rational_spherical_pythagorean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Square the right-angle dot identity and clear the nonzero norms. With nonzero incident spreads the right-angle identity is also equivalent to vertex spread one.

**Theorem 1.6 (Exact norm drift at any rational sampling weight).**

$$\forall alpha \in \operatorname{IntRatio}\left(\right), A \in \mathbb{Q}^{4}, x \in \mathbb{Q}^{4},\; \left(\operatorname{Finite}\left(alpha\right) \land \left(\operatorname{scalarPart}\left(A\right) = 0 \land \operatorname{Equivalent}\left(\operatorname{normSq}\left(x\right), 1\right)\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{normSq}\left(\operatorname{alphaSample}\left(alpha, A, x\right)\right) - 1, \left(1 - 2 \cdot alpha\right) \cdot \operatorname{normSq}\left(\operatorname{alphaSample}\left(alpha, A, x\right) - x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.alpha_sampling_norm_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sample solves the implicit quaternion step by the conjugate and squared norm of the left factor. A pure generator acts by a skew-adjoint left multiplication, so the displacement is orthogonal to the weighted sample. Expanding that orthogonality gives the drift identity.

**Theorem 1.7 (The Cayley midpoint stays on the unit sphere).**

$$\forall A \in \mathbb{Q}^{4}, x \in \mathbb{Q}^{4},\; \left(\operatorname{scalarPart}\left(A\right) = 0 \land \operatorname{Equivalent}\left(\operatorname{normSq}\left(x\right), 1\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{normSq}\left(\operatorname{midpointStep}\left(A, x\right)\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.midpoint_unit_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The drift multiplier vanishes when the sampling weight is one half.

**Theorem 1.8 (The two midpoint legs have equal fidelity).**

$$\forall A \in \mathbb{Q}^{4}, x \in \mathbb{Q}^{4},\; \left(\operatorname{scalarPart}\left(A\right) = 0 \land \operatorname{Equivalent}\left(\operatorname{normSq}\left(x\right), 1\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(\operatorname{numerator}\left(x\right), \operatorname{numerator}\left(\operatorname{midpointStep}\left(A, x\right)\right)\right), \operatorname{kappa}\left(\operatorname{numerator}\left(\operatorname{midpointStep}\left(A, x\right)\right), \operatorname{triad}\left(\operatorname{numerator}\left(\operatorname{midpointStep}\left(A, x\right)\right), \operatorname{numerator}\left(x\right), \operatorname{numerator}\left(\operatorname{midpointStep}\left(A, x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.midpoint_half_step_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right multiplication of both nonzero numerator quaternions by the initial conjugate times the midpoint maps the first leg to the second up to a nonzero scaling. Projective fidelity is invariant under that common multiplication and scaling.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.all_degree_peter_weyl_orthonormal`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.alpha_sampling_norm_drift`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.evenChar_product_sum`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.haar_evenChar_expectation`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.midpoint_half_step_fidelity`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.midpoint_unit_norm`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.rational_spherical_pythagorean`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint.rational_spherical_sine_law`
