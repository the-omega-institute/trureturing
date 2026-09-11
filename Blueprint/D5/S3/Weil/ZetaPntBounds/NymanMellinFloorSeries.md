# Floor-Series Mellin Identity

## Abstract

Floor-Series Mellin Identity.

**Theorem 1.1 (Floor-series Mellin identity).**

$$\forall k\in\mathbb{N},s\in\mathbb{C},1\le k\land1<\Re s\Rightarrow\int_{0}^{1}x^{s-1}\operatorname{fract}(\frac{k}{x})\,dx=\frac{k}{s(s-1)}+\frac{k^{s}}{s}(\sum_{m=0}^{k-1}(m+1)^{-s}-\zeta(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries.mellin_fractBasis` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

For positive natural k and real part of s greater than one, the source proof partitions the floor function into intervals, evaluates powers, and sums by parts to the actual zeta expression. The upstream argument and live prerequisites are retained.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries.mellin_fractBasis`
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers](NymanMellinHelpers.md)
