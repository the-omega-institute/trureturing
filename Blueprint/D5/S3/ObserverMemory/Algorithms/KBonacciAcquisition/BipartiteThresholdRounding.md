# Bipartite Threshold Rounding

## Abstract

The finite opposite-colour threshold intersection has the exact positive-part count used by continuation VI.

**Theorem 1.1 (Opposite-colour threshold count).**

$$\operatorname{card}\left(\operatorname{crossThresholds}\left(N, a, b\right)\right) = a + b - N$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/BipartiteThresholdRounding.cross_threshold_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N, a and b with a <= N and b <= N, crossThresholds N a b contains exactly those finite uniform thresholds t with N-b <= t < a. Its cardinality is the truncated difference a+b-N, including the empty intersection and endpoint cases.

This is the discrete counting identity behind the expectation max(0,x+y-1) in the bipartite relaxation used by Theorem 183.2. It does not assert an acquisition strategy, a probability law, or the full conditioned all-word criterion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/BipartiteThresholdRounding.cross_threshold_card`
