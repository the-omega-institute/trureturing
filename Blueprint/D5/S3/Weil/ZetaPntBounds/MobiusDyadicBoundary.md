# Weighted Möbius energy and the boundary reciprocal of zeta

## Abstract

Weighted signed dyadic Möbius energy controls the reciprocal of zeta on a vertical line.

**Theorem 1.1 (Square-integrability of the weighted reciprocal).**

$$\int_{\mathbb{R}}\,\frac{1}{(1+\Vert y\Vert)^{2}\,\Vert \zeta\left(\theta+iy\right)\Vert^{2}}\,\mathrm{d}y\leq4+\frac{4\pi E}{(1-2^{\theta-1})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary.weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual signed difference D(x) = S(x) − S(2x), where S(x) is the finite sum of μ(n)/n over positive integers n ≤ x. Fix 0 ≤ θ < 2 with θ ≠ 1 and assume that ζ has no zeros on the line of real part θ. If the integral E of D(x)² x⁻⁽²θ⁻¹⁾ over x > 1 is finite, y ↦ 1/((1+|y|)|ζ(θ+iy)|) belongs to L² on the real line. Its squared norm satisfies the displayed bound.

The change of variables x = exp u gives a causal function in L². Damping it by exp(−hu) yields L¹ and L² and preserves the L² bound. Multiply the dyadic Mellin identity by the pole-removed zeta factor before using holomorphic uniqueness. Local division at each point of the zero-free line gives convergence of the angular Fourier transforms. Apply Plancherel and Fatou to bound the limiting symbol, and then use |1−2ˢ| ≥ |1−2ᶿ⁻¹| and |s| ≤ 1+|y| for s = θ−1+iy.

When the real parts of the nontrivial zeros have an unattained supremum Θ < 1, the theorem applies at θ = Θ. In this case finite critical Möbius energy forces finite weighted reciprocal mass on the zero-abscissa line.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary.weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy`
- Dependency: [D5/S3/Analytic/Laplace/CausalExponentialStripTransfer](../../Analytic/Laplace/CausalExponentialStripTransfer.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../../Arith/Robin/ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Weil/Mertens/MobiusDyadicEnergy](../Mertens/MobiusDyadicEnergy.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](../ZetaGamma/FormCore/LineFourier.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval](MobiusDyadicUnitWeightParseval.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](MobiusPartialSumL2Divergence.md)
