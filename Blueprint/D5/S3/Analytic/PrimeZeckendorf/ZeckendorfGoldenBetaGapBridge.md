# Zeckendorf Golden Beta Gap Bridge

## Abstract

The least Zeckendorf digit selects the long or short consecutive golden Euler-layer step.

**Theorem 1.1 (The least digit selects the next golden beta gap).**

$$\forall v: \mathbb{N},\\(\neg(2 \in \operatorname{wdigits}(v)) \Rightarrow \operatorname{beta}(v+1)-\operatorname{beta}(v) = \varphi^{2}) \land\\(2 \in \operatorname{wdigits}(v) \Rightarrow \operatorname{beta}(v+1)-\operatorname{beta}(v) = \varphi).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/ZeckendorfGoldenBetaGapBridge.zeckendorf_selects_golden_beta_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absence of Fibonacci index two in the canonical Zeckendorf address gives the long phi-squared gap; presence gives the short phi gap.

The proof composes the existing Zeckendorf-Beatty bridge with the all-order golden beta-gap dichotomy. It records a layer transition code and does not claim that Zeckendorf encodes prime, phase, or continuous-scale coordinates.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/ZeckendorfGoldenBetaGapBridge.zeckendorf_selects_golden_beta_gap`
- Dependency: [D5/S1/Words/ZeckendorfBeattyBridge](../../../S1/Words/ZeckendorfBeattyBridge.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern](../EulerGerm/GoldenGermNextExponentPattern.md)
