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

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_eventually_quartic_samples`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak](ActualLinearPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
