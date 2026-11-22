# A sparse test for the integrated Mangoldt remainder

## Abstract

Testing the Riemann hypothesis at fourth powers

**Theorem 1.1 (The fourth-power sampling criterion).**

$$RiemannHypothesis \Leftrightarrow \left(\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; N \le n \Rightarrow U\left(n^{4}\right) < n^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_eventually_quartic_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The remainder U is CompleteMertensPeak.U with its inclusive natural-floor sum. Under RH the normalized remainder G is eventually smaller in absolute value than one, since its limiting envelope is at most the first Li mass, which is less than one. Substitution of 4 log n gives the strict bound at all sufficiently large fourth powers.

Conversely, put a = n⁴ and b = (n+1)⁴. Each Mangoldt ramp is a nonnegative multiple of the maximum of an affine function and zero, so the complete ramp sum lies below its endpoint chord. The nonlinear centering contributes at most (b−a)²/a. This follows by subtracting the tangent of z log z at a, then bounding the excess at b using log(b/a) ≤ b/a−1. For n ≥ 1 the gap is at most 15n³ and (n+1)² ≤ 4n². The sampled bounds therefore imply U(x) ≤ 229n² between adjacent samples.

Those intervals cover the entire tail. The normalized arithmetic kernel is eventually at most 230 after including the trivial-zero correction. Its affine-tail implication gives RH. The resulting equivalence leaves the arithmetic sample inequality to be proved.

**Theorem 1.2 (Finite fourth-power samples on arbitrarily late closed windows).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(RiemannHypothesis \Leftrightarrow \left(\forall k \in \mathbb{R},\; 0 < k \Rightarrow \left(\forall R \in \mathbb{R},\; \exists Y \in \mathbb{R},\; \operatorname{max}\left(R, 2\right) \le Y \land \left(\forall t \in \mathbb{R},\; t \in \operatorname{S}\left(Y, Y^{b}\right) \Rightarrow \operatorname{U}\left(t\right) \le t^{\frac{1}{2}+k}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_power_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Y ≥ 2 and Z ≥ Y, S(Y,Z) consists of Y, Z and every natural fourth power n⁴ with Y ≤ n⁴ ≤ Z. These finitely many samples allow arbitrary real endpoints. The window may depend on the exponent loss and the requested lower bound on its starting point.

For each x in the window, clip the fourth-power cell containing x to the window. Both ends of the clipped interval belong to S(Y,Z). Its chord error is at most 225√x and each sampled power bound is at most 16xᵖ for 1/2 ≤ p ≤ 1. This gives U(x) ≤ 241xᵖ throughout the window. Choose a smaller positive loss and move the window far enough to absorb 241. The whole-window power criterion then gives RH. The forward implication restricts that criterion to the sample points.

**Theorem 1.3 (Sampling on finite integer blocks).**

$$RiemannHypothesis \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall A \in \mathbb{N},\; \exists k \in \mathbb{N},\; \operatorname{max}\left(A, 2\right) \le k \land \left(\forall n \in \mathbb{N},\; \left(k^{3} \le n \land n \le k^{4}\right) \Rightarrow U\left(n^{4}\right) \le (n^{4})^{\frac{1}{2}+e}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_integer_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive exponent loss and each natural threshold A, the test asks for a natural k at least max(A,2). At this k it tests all fourth powers n⁴ with integer root between k³ and k⁴, including both boundary roots. Under RH the strict quartic tail estimate supplies the tests for every sufficiently large k.

Conversely, choose the real window with left end k¹² and power exponent 4/3. Its right end is k¹⁶. The boundary roots are k³ and k⁴, and monotonicity of the fourth power places every interior sample root between them. Such windows start arbitrarily far out, so they satisfy the closed-window criterion at every positive loss.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_eventually_quartic_samples`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_integer_blocks`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_power_windows`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak](ActualLinearPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows](MangoldtPointwiseWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
