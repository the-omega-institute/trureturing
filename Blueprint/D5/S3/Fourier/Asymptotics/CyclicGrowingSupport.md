# Strict rear activation thresholds

## Abstract

Exact positive support and optimizer certification in the critical growing-window regime.

Let the positive integer periods q(n) have eventual parity e in {0,1}, write h(n)=2π/q(n), and assume n⁵h(n)² tends to a finite K. The front window is the image in the cyclic group of integers −n through n. The rear window of index l comprises offsets −l−e/2 through l+e/2 in unit steps from the antipodal angle. Fit the three scaled moment equations on these windows.

**Theorem 1.1 (Pointwise boundary signs certify the optimizer).**

$$\left(0 < \operatorname{SignedValue}\left(R\right) \land \operatorname{SignedValue}\left(R + 1\right) \le 0\right) \Rightarrow \operatorname{Support}\left(v\right) = \operatorname{TwoWindows}\left(n, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingSupport.eventual_window_support_of_point_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fixed rear index l, at sufficiently large n the front signs, matrix invertibility and dual coefficient inequalities hold. If the last included rear score is positive and the first omitted rear score is nonpositive at that n, the two-window fit is the unique optimizer, has the stated positive support and satisfies the squared-distance energy bound. The two conditions are imposed pointwise, so the omitted score may vanish.

**Theorem 1.2 (Eventual exact support away from rear activation thresholds).**

$$\operatorname{Threshold}\left(T, e, l\right) < \frac{3 \cdot K}{20} < \operatorname{Threshold}\left(T, e, l + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingSupport.eventual_strict_support_away_from_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define T₀(l)=l(2l−1)(2l+1)/4 and T₁(l)=l(l+1/2)(l+1). Assume 3K/20 differs from every Tₑ(l). Then K is positive and monotonicity and unboundedness of the threshold polynomial give a unique index l between consecutive thresholds.

The fitted values on the front and rear windows converge with the boundary scalings n² and n³. The endpoint and next-site signs at the front are strict. At the rear, the finite parity square sum identifies the strict inequalities of the limiting parabola with the two threshold inequalities. The signed cyclic values are a quadratic in the sampled cosine. Convexity and the four boundary signs determine its sign on the full grid.

For all sufficiently large n the disjoint grid windows realize exactly the coupled moment sums. The fitted weights, extended by zero outside them, are feasible, attain both cosine moment floors 1−2n(n+1)h²/5, and uniquely minimize energy. Every feasible competitor w has energy at least the fitted energy plus the squared distance from w to the fit. The optimizer has strictly positive support precisely on the two windows. Equality at a rear threshold is excluded.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingSupport.eventual_strict_support_away_from_thresholds`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingSupport.eventual_window_support_of_point_signs`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicEventualSupport](CyclicEventualSupport.md)
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits](CyclicGrowingEdgeLimits.md)
