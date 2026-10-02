# Smooth1

## Abstract

Mellin convolution gives smooth threshold functions and their analytic bounds.

**Definition 1.1 (Smooth1).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

The smoothed indicator is the Mellin convolution of the indicator of (0, 1] with the dilation kernel.

**Theorem 1.2 (Smooth1Properties_below).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_below`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_below` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

A kernel supported in [1/2, 2] with unit multiplicative Haar mass gives a smoothed indicator equal to one for positive x at most 1 minus epsilon times log two, for every positive epsilon.

**Theorem 1.3 (Smooth1Properties_above).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_above`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_above` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For a kernel supported in [1/2, 2] and epsilon strictly between zero and one, the smoothed indicator vanishes when x is at least 1 plus twice epsilon times log two.

**Theorem 1.4 (MellinOfSmooth1a).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.MellinOfSmooth1a`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/Smooth1.MellinOfSmooth1a` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For a once continuously differentiable kernel supported in [1/2, 2], every positive epsilon and every complex s with positive real part, the Mellin transform of the smoothed indicator equals the Mellin transform of the kernel at epsilon times s divided by s.

**Theorem 1.5 (Smooth1ContinuousAt).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1ContinuousAt`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1ContinuousAt` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For a nonnegative once continuously differentiable kernel supported in [1/2, 2] and every positive epsilon, its smoothed indicator is continuous at every positive argument.

## References

- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.MellinOfSmooth1a`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1ContinuousAt`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_above`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/Smooth1.Smooth1Properties_below`
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/MellinCalculus](MellinCalculus.md)
