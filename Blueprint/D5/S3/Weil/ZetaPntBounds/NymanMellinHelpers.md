# Fractional Mellin Prerequisites

## Abstract

Fractional Mellin Prerequisites.

**Theorem 1.1 (Vanishing floor-series tail).**

$$\forall s\in\mathbb{C}, 1<\Re s\Rightarrow\lim_{N\to\infty}N(\frac{1}{N+1})^{s}=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.tail_vanishes` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

The power tail tends to zero when the real part of s exceeds one. This is the live FloorMellin source argument.

**Theorem 1.2 (Partial zeta limit).**

$$\forall s\in\mathbb{C}, 1<\Re s\Rightarrow\lim_{N\to\infty}\sum_{n=0}^{N-1}\frac{1}{(n+1)^{s}}=\zeta(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.partial_zeta_tendsto` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

The reciprocal-power partial sums converge to the actual riemannZeta on the half-plane of absolute convergence.

**Theorem 1.3 (Positive-base power quotient).**

$$\forall k,n\in\mathbb{N},s\in\mathbb{C}, 1\le k\land1\le n\Rightarrow(\frac{k}{n})^{s}=k^{s}n^{-s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.ofReal_div_cpow` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

The source helper is bound to the installed nonnegative-real complex-power quotient and negation APIs.

**Definition 1.4 (Restricted Mellin integral).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.mellinRestricted`

*Formalization.* `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.mellinRestricted` (`✓ std3`).

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

The source definition integrates x to the power s minus one times f over Ioc zero one with volume measure.

**Definition 1.5 (Fractional basis).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.fractBasisC`

*Formalization.* `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.fractBasisC` (`✓ std3`).

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

The source definition is the complex coercion of the real fractional part of k divided by x.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.fractBasisC`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.mellinRestricted`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.ofReal_div_cpow`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.partial_zeta_tendsto`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.tail_vanishes`
