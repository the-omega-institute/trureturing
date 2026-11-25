# An Infinite Spectrum for the Critical Missing-Window Bound

## Abstract

An infinite positive-weight spectrum realizes both mass hypotheses at once.

**Theorem 1.1 (An infinite spectrum with independent frequencies and positive weights).**

$$\exists S \in Spectrum,\; \exists w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{Infinite}\left(\operatorname{index}\left(S\right)\right) \land \left(\left(\forall j \in \operatorname{index}\left(S\right),\; 0 < \operatorname{w}\left(j\right)\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{Q}, \operatorname{gamma}\left(S\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \operatorname{HasSmallSquareTail}\left(S, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel.exists_infinite_critical_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose countably many members of a rational basis of the reals. Multiply the nth member by a nonzero rational so that its ordinate lies strictly between the fourth roots of n+1 and n+2. This is possible by rational density and preserves rational linear independence. The intervals order the ordinates and give local finiteness.

Take w(n) = log²(n+2) − log²(n+1), which is positive. If n is the last index below or at T, the mass telescopes to log²(n+2). The interval bounds give n+1 < T⁴ < n+3. Consequently |log(n+2) − 4 log T| ≤ 1, yielding a squared-logarithmic coefficient of 16 and error at most 9(1+log T) eventually.

The log increment is at most 1/(n+1), and the sum of the two logs is at most 32(n+1)^(1/8). Thus w(n) ≤ 32(n+1)^(−7/8), and (n+1)^(1/2)w(n)² has finite sum by comparison with a series of exponent 5/4. For ordinates above X ≥ 1, X² ≤ 2(n+1)^(1/2). The square tail is therefore O(X⁻²), uniformly in the finite upper cutoff. `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow`

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel.exists_infinite_critical_model`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow](SpectrumCriticalMissingWindow.md)
- Narrative reference: [D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow](SpectrumCriticalMissingWindow.md)
