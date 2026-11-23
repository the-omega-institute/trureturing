# Weighted Phase Recurrence on a Finite Interval

## Abstract

A Fejer product gives finite interval recurrence for normalized weighted phase loss.

Let J be a finite index type, and let g, θ, and p be real-valued families on J. The entries of p are nonnegative and sum to one. Let N be a positive integer and let ε, δ, a, and R be real with ε > 1/N, δ > 0, and R > 0. For integer vectors k set ξ(k) = Σⱼ kⱼgⱼ and φ(k) = Σⱼ kⱼθⱼ. For every k with |kⱼ| ≤ N in every coordinate, assume cos φ(k) = 1 if ξ(k) = 0 and |ξ(k)| ≥ δ if ξ(k) ≠ 0.

**Definition 1.1 (Weighted phase loss).**

$$\forall t\in\mathbb{R},\quad\operatorname{phaseLoss}\left(g, \theta, p, t\right) = \sum_{j\in J}\,p_{j}(1 - \operatorname{cos}\left(g_{j}t - \theta_{j}\right))$$

*Formalization.* `D5/S3/Fourier/WeightedPhaseRecurrence.phaseLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition applies to arbitrary real weights. The recurrence theorem uses nonnegativity and normalization.

**Theorem 1.2 (A window uniform in its starting time).**

$$R\delta(\varepsilon - \frac{1}{N})>2(\varepsilon \cdot N^{|J|} - (\varepsilon - \frac{1}{N}))\quad\longrightarrow\quad\exists t\in[a,a + R],\quad\sum_{j\in J}\,p_{j}(1 - \operatorname{cos}\left(g_{j}t - \theta_{j}\right))<\varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedPhaseRecurrence.weighted_phase_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For offsets xⱼ = gⱼt − θⱼ, take the product P = ∏ⱼ F_N(xⱼ) of the Fejér polynomials. Each F_N is the normalized squared modulus of the geometric exponential sum of length N. Its triangular coefficients are 1 − |k|/N for |k| ≤ N, with the two endpoints zero. The one-coordinate identity (1 − cos x)F_N(x) = (1 − cos(Nx))/N follows from the geometric-sum identity.

Expand (ε − phaseLoss)P as (ε − 1/N)P plus the sum over j of (pⱼ/N) (F_N(xⱼ) − 1 + cos(Nxⱼ)) times the product of F_N over the other coordinates. Subtracting 1 removes the constant mode of the triangular coefficients in coordinate j. The cosine adds the two modes at ±N with coefficient 1/2 each. Multiplying the complex characters and taking real parts gives a cosine expansion on the integer box. All coefficients are nonnegative. The coefficient at the zero index is ε − 1/N, and evaluating with all offsets zero gives total coefficient mass εN^|J|.

The zero index contributes R(ε − 1/N) to the integral. Other exact resonances contribute nonnegatively by phase compatibility. For a nonzero frequency ξ, the affine cosine integral is a difference of two sines divided by ξ and has absolute value at most 2/|ξ| ≤ 2/δ. The length inequality gives a strictly positive integral. At a time where the integrand is positive, P is nonnegative and the loss is strictly below ε.

This uses the Fejér product of Bohr and Jessen and the finite averaging mechanism discussed by Sourmelidis (arXiv:2411.14221, §4). The finite exponential average also appears as norm_avg_le in the Riemann hypothesis repository's ExpSumCoeffEqZeroOfVanishing.lean at b8864ecd5798c6030a03d756fab95f0b89a12754, in the cycles-per-unit convention. Here the frequencies are angular and the interval start is arbitrary.

Maksimova (arXiv:2405.07051, Theorem 1) and Gonek–Montgomery (DOI 10.1016/j.indag.2016.02.002, Theorem C as quoted there) assume separation from zero for every nonzero vector in their respective boxes and allow arbitrary targets with coordinatewise tolerances. The weighted loss bound here permits exact resonances in its box when the target character on each is one. Sourmelidis also notes that Chen (DOI 10.1112/S0024610700008772) treats linear dependencies. For example, with g = (1,3), θ = (0,π), N = 2, and δ = 1, the only in-box relation is zero, and the relation (3,−1) outside the box has target cosine −1.

For the qualitative comparison, `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit` imposes the same character test on the whole relation lattice to obtain orbit closure on each upper ray. The cosine of the sum is the real part of the corresponding circle character and equals one exactly when that character is one. The product in the finite argument retains the frequencies in the stated box. With all θⱼ = π/2, cos(gⱼt − θⱼ) = sin(gⱼt) and the target character of k is i raised to Σⱼkⱼ. Its being one is the sum-divisibility condition in `D5/S3/Fourier/ShortPhaseRelations` restricted here to the box and applied to the normalized pointwise sine loss. For a fixed zeta cutoff the window theorem requires the stated compatibility and a verified separation δ.

## References

- Truth anchor: `D5/S3/Fourier/WeightedPhaseRecurrence.phaseLoss`
- Truth anchor: `D5/S3/Fourier/WeightedPhaseRecurrence.weighted_phase_recurrence`
- Truth anchor: `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit`
- Dependency: [D5/S3/Zeros/Repulsion/FejerNearCollisionBound](../Zeros/Repulsion/FejerNearCollisionBound.md)
- Narrative reference: [D5/S3/Fourier/ShortPhaseRelations](ShortPhaseRelations.md)
