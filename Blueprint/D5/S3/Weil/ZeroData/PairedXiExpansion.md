# Paired xi expansion away from poles

## Abstract

The paired logarithmic derivative expansion of xi is an explicit hypothesis.

**Definition 1.1 (Avoiding the paired spectral poles).**

Lean statement: `D5/S3/Weil/ZeroData/PairedXiExpansion.PoleFree`

*Formalization.* `D5/S3/Weil/ZeroData/PairedXiExpansion.PoleFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive spectrum, the pole-free set consists of complex points different from both i times each ordinate and its negative.

**Definition 1.2 (A convergent paired expansion).**

Lean statement: `D5/S3/Weil/ZeroData/PairedXiExpansion.PairedXiExpansion`

*Formalization.* `D5/S3/Weil/ZeroData/PairedXiExpansion.PairedXiExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume RH and use the positive zeta ordinate spectrum with analytic multiplicities. At every pole-free complex point s, require the sum of m times (1/(s-i gamma) + 1/(s+i gamma)) to converge to the logarithmic derivative of xiReading at 1/2+s.

Here xiReading is the repository's entire completed zeta function. HasSum asserts convergence as well as the value of the paired sum. This definition introduces a hypothesis and does not prove that hypothesis from RH or from zero counting.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/PairedXiExpansion.PairedXiExpansion`
- Truth anchor: `D5/S3/Weil/ZeroData/PairedXiExpansion.PoleFree`
- Dependency: [D5/S3/Analytic/Laplace/PairedPoleRegularity](../../Analytic/Laplace/PairedPoleRegularity.md)
- Dependency: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](PositiveOrdinateSpectrum.md)
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
