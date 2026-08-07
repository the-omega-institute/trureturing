# Diagonal Escape Asymptotics

## Abstract

Finite diagonal escape ratios tend to one as listing size grows.

**Theorem 1.1 (The escape ratio tends to one).**

$$\lim_{N\to\infty}\left(1-\frac{k}{n^N}\right)^N=1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/EscapeAsymptotics.escape_ratio_tendsto_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed natural value count n at least two and fixed-point count k at most n, the N-th power of one minus k divided by n to the N-th power tends to one. This asymptotic statement is expressed as a real-valued ratio; the finite counting truth source remains the exact escaped-listing cardinality theorem in EscapeCount.

## References

- Truth anchor: `D5/S0/Diagonal/EscapeAsymptotics.escape_ratio_tendsto_one`
