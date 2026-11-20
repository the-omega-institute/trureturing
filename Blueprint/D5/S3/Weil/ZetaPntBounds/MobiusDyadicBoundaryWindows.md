# Disjoint zero windows at the zero abscissa

## Abstract

Critical signed dyadic Möbius energy bounds the sum of contributions from disjoint zero windows.

**Theorem 1.1 (A reciprocal mass bound on a zero-free line).**

$$\sum_{i\in t}\,a_{i}\leq\int_{\mathbb{R}}\,g(y)\,\mathrm{d}y$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.finite_gap_mass_le_integral_reciprocalDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f have no zeros on the vertical line of real part θ. Define the density g(y) = 1/((1+|y|)² |f(θ+iy)|²) and assume it is integrable. For a finite family of zeros ρᵢ of f, take gaps δᵢ = θ − Re ρᵢ in (0, 1] and pairwise disjoint open ordinate windows of radius δᵢ. Suppose f is complex differentiable with derivative norm at most Mᵢ > 0 on the closed rectangle between ρᵢ and its window on the line. Integrating the pointwise lower bound on each window gives a contribution aᵢ = 1/(8δᵢMᵢ²(1+|Im ρᵢ|)²). Disjointness lets the integrals add within the total mass of g.

**Theorem 1.2 (Finite families of disjoint windows).**

$$\sum_{i\in t}\,a_{i}\leq4+\frac{4\pi E}{(1-2^{\theta-1})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.finite_gap_mass_le_of_critical_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let θ < 1 be the unattained supremum of the real parts of nontrivial zeta zeros. For each zero ρ = β + iγ, write δ = θ − β. Use the open ordinate interval (γ − δ, γ + δ) and choose M > 0 that bounds the norm of the zeta derivative on the corresponding closed rectangle between real parts β and θ. Write S(x) for the sum of μ(n)/n over positive integers n ≤ x and D(x) = S(x) − S(2x). Assume D(x)² x^(1−2θ) is integrable over x > 1 and write E for its integral.

Along the segment from ρ to θ + iy the derivative bound gives |ζ(θ + iy)| ≤ 2δM for y in that interval. The weight satisfies 1 + |y| ≤ 2(1 + |γ|). Integrating the reciprocal density over the length 2δ gives a lower bound of 1/(8δM²(1 + |γ|)²), denoted by aᵢ. Pairwise disjoint intervals let these bounds add within the total mass controlled by the critical Möbius energy.

**Theorem 1.3 (Summability of the window contributions).**

$$\sum_{i}\,a_{i}\leq4+\frac{4\pi E}{(1-2^{\theta-1})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.gap_mass_summable_of_critical_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same zero-abscissa, derivative and weighted square-integrability hypotheses, assume the open windows are pairwise disjoint throughout the family. The finite-family theorem bounds every finite sum of nonnegative contributions. The full family is summable and its sum satisfies the displayed bound.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.finite_gap_mass_le_integral_reciprocalDensity`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.finite_gap_mass_le_of_critical_energy`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows.gap_mass_summable_of_critical_energy`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../../Arith/Robin/ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Weil/Mertens/MobiusDyadicEnergy](../Mertens/MobiusDyadicEnergy.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary](MobiusDyadicBoundary.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](MobiusPartialSumL2Divergence.md)
