# Weighted Phase Deficit and the Complete Relation Lattice

## Abstract

The complete integer relation lattice gives uniform lower and upper bounds for the weighted sine deficit at a common real time.

**Theorem 1.1 (Continuous orbit closure).**

$$\forall J \in FiniteType, g \in \mathbb{R}^{J},\; \operatorname{closure}\left(\left\{\left(\operatorname{exp}\left(i \cdot g_{j} \cdot t\right)\right)_{j \in J} \mid t \in \mathbb{R}\right\}\right) = \{p\in \mathbb{T}^{J} \mid \forall k \in \mathbb{Z}^{J},\; \sum_{j\in J} k_{j} \cdot g_{j} = 0 \Rightarrow \prod_{j\in J} \left(p_{j}\right)^{k_{j}} = 1\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit` (`✓ std3`). ∎

*Citation.* A. L. Onishchik (2020). *Kronecker theorem*. URL: <https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528>.

*Commentary.*

For each nonzero integer dot product with the frequency vector, the steps that turn it into an integral multiple of 2π form a countable set. One step in (0,1) avoids their union. Its discrete characters are exactly the zero-dot-product characters, so TorusOrbitClosure.result puts every point in their common kernel in the real orbit closure. The forward inclusion follows from character continuity.

**Theorem 1.2 (Centered angles and integer congruences).**

$$\forall J \in FiniteType, A \in Type, g \in \mathbb{R}^{J}, K \in \mathbb{Z}^{A\times J}, R \in \mathbb{R}^{A\times J}, x \in \mathbb{R}^{J},\; \left(R = \operatorname{cast}\left(K\right) \land \left(\forall k \in \mathbb{Z}^{J},\; k \in \operatorname{spanZ}\left(\operatorname{rows}\left(K\right)\right) \Leftrightarrow \sum_{j\in J} k_{j} \cdot g_{j} = 0\right)\right) \Rightarrow \left(\left(\operatorname{exp}\left(i \cdot \left(x_{j} + \frac{\pi}{2}\right)\right)\right)_{j \in J} \in \operatorname{closure}\left(\left\{\left(\operatorname{exp}\left(i \cdot g_{j} \cdot t\right)\right)_{j \in J} \mid t \in \mathbb{R}\right\}\right) \Leftrightarrow \left(\exists z \in \mathbb{Z}^{A},\; R \cdot x = 2 \cdot \pi \cdot z - \frac{\pi}{2} \cdot R \cdot \mathbf{1}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedPhaseRelationLattice.centered_lift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here R is the entrywise real cast of the integer row matrix K. Testing each row gives an integer winding number for the angle x + (π/2)1. Each integer relation uses only finitely many rows, even for an arbitrary row index type A. The same finite integral combination of their winding numbers gives the winding for that relation, so the row congruences imply every character equation. Every point of the closure has a lift of this form with x in (−π,π] coordinatewise. Rotate by −π/2 and take the argument on the unit circle.

**Theorem 1.3 (Uniform inverse Gram energy comparison).**

$$\forall J \in FiniteType, A \in FiniteType, g \in \mathbb{R}^{J}, w \in \mathbb{R}^{J}, K \in \mathbb{Z}^{A\times J}, R \in \mathbb{R}^{A\times J}, W \in \mathbb{R}, M \in \mathbb{R}^{J\times J}, G \in \mathbb{R}^{A\times A}, b \in \mathbb{Z}^{A} \to \mathbb{R}^{A}, E \in \mathbb{R}, D \in \mathbb{R},\; \left(\left(\forall j \in J,\; 0 < w_{j}\right) \land \left(0 < W \land \left(R = \operatorname{cast}\left(K\right) \land \left(\left(\forall k \in \mathbb{Z}^{J},\; k \in \operatorname{spanZ}\left(\operatorname{rows}\left(K\right)\right) \Leftrightarrow \sum_{j\in J} k_{j} \cdot g_{j} = 0\right) \land \operatorname{LinearlyIndependent}\left(\mathbb{R}, \operatorname{rows}\left(R\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(W = \sum_{j\in J} w_{j} \land \left(M = \operatorname{diag}\left(w\right) \land \left(G = R \cdot M^{-1} \cdot R^{T} \land \left(\left(\forall z \in \mathbb{Z}^{A},\; \operatorname{b}\left(z\right) = 2 \cdot \pi \cdot z - \frac{\pi}{2} \cdot R \cdot \mathbf{1}\right) \land \left(E = \operatorname{inf}_{z\in \mathbb{Z}^{A}} \operatorname{b}\left(z\right)^{T} \cdot G^{-1} \cdot \operatorname{b}\left(z\right) \land D = 1 - \operatorname{sup}_{t\in \mathbb{R}} \frac{\sum_{j\in J} w_{j} \cdot \operatorname{sin}\left(g_{j} \cdot t\right)}{W}\right)\right)\right)\right)\right) \Rightarrow \left(\frac{2 \cdot E}{\pi^{2} \cdot W} \le D \land \left(D \le \frac{E}{2 \cdot W} \land \left(\operatorname{IsEmpty}\left(A\right) \Rightarrow E = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedPhaseRelationLattice.weighted_phase_deficit_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite J gives finite character products and weighted sums. With finite A the Gram matrix admits the usual finite matrix inverse once positive definiteness is established. Positive individual weights make M and M⁻¹ positive definite. Real independence of the cast rows makes Rᵀ injective, so its pullback G = R M⁻¹ Rᵀ is positive definite and invertible. For each z, the vector x₀ = M⁻¹RᵀG⁻¹b(z) satisfies Rx₀ = b(z). Its squared M-norm is b(z)ᵀG⁻¹b(z). The M-cross term vanishes for each displacement in the kernel of R, so this is the attained minimum for that fiber.

Positive total weight W permits normalization and preserves the inequality directions when dividing by W. Full integral row generation ensures that the affine fibers enforce every character equation of the orbit closure. A proper sublattice can admit extra lifts and lower E.

Two hand-checked examples illustrate these hypotheses. When J is empty, the sum and W are zero. Totalized division gives score zero and D = 1, while E/(2W) is zero. For one frequency γ = 0 with weight 1, the full relation lattice is ℤ. The single row K = [4] generates 4ℤ, and z = 1 gives b(z) = 0. Since G = [16], each winding energy is a square divided by 16, so E = 0. The sine score is always zero, so D = 1 and the upper bound fails.

The continuous weighted sine deficit on the orbit closure has the same infimum as along the real-time orbit. In principal centered angles, the pointwise lower estimate for 1 − cos x has coefficient 2/π² on x². The upper estimate has coefficient 1/2 for every real x and applies to the affine minimizers. Taking the infimum over all integer windings gives the bounds. Empty A gives zero inverse Gram energy and hence zero deficit.

For the ζ-ordinate example, assume hRH proves Mathlib's RiemannHypothesis. Form zetaSpectrum hRH, then use the finite index type of members of Spectrum.cut (zetaSpectrum hRH) T, which keeps the positive ordinates γ with γ ≤ T. Multiply the chosen positive weight per occurrence by the analytic multiplicity of its zero. The comparison applies given a complete relation basis and positive total weight. Bounding the normalized energy for the actual ζ ordinates is a separate question.

## References

- Truth anchor: `D5/S3/Fourier/WeightedPhaseRelationLattice.centered_lift_iff`
- Truth anchor: `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit`
- Truth anchor: `D5/S3/Fourier/WeightedPhaseRelationLattice.weighted_phase_deficit_bounds`
- Dependency: [D5/S3/Fourier/TorusOrbitClosure](TorusOrbitClosure.md)
