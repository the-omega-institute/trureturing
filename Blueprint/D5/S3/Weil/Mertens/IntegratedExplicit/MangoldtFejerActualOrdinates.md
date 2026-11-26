# The limit of the largest admissible coefficient

## Abstract

Fejér averages tested at the positive zeta ordinates

At scale T, a probability measure μ on the interval from zero to one half is admissible if its cosine transform is nonnegative at γ/T for every positive ordinate γ of a nontrivial zeta zero. Its coefficient A is half the μ-average of b/2 − b².

**Theorem 1.1 (The bound on a common tail).**

$$A \le \frac{1}{48} + epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.eventually_fejer_averaging_coefficient_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive ε the scale threshold is uniform over the admissible measures. The unconditional cumulative Riemann–von Mangoldt law puts a scaled ordinate arbitrarily near each fixed positive harmonic. Every cosine transform here has Lipschitz constant at most one half. Use the nearby ordinates for a finite set of harmonics and the summable reciprocal-square bound for the remaining terms.

**Theorem 1.2 (The exact limit).**

$$\lim_{T\to\infty} \operatorname{supremum}\left(T\right) = \frac{1}{48}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.tendsto_sSup_fejerAveragingCoefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here supremum(T) ranges over the coefficients of all measures admissible at scale T. The triangular law is admissible at every scale and gives 1/48. The common upper bound proves convergence to that value.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.eventually_fejer_averaging_coefficient_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates.tendsto_sSup_fejerAveragingCoefficients`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality](MangoldtFejerOptimality.md)
- Dependency: [D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt](../../ZeroData/CumulativeRiemannVonMangoldt.md)
- Dependency: [D5/S3/Weil/ZetaRvm/NcountWindow](../../ZetaRvm/NcountWindow.md)
