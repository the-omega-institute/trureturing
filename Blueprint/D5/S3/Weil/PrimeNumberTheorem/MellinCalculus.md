# MellinCalculus

## Abstract

Compactly supported Mellin kernels have uniform vertical-strip decay.

**Definition 1.1 (MellinConvolution).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinConvolution`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinConvolution` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

Multiplicative convolution integrates f(y) times g(x/y) against dy/y over the positive real axis.

**Theorem 1.2 (MellinOfPsi).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinOfPsi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinOfPsi` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For every once continuously differentiable real kernel supported in [1/2, 2], one positive constant bounds its complex Mellin transform by that constant divided by the norm of the transform parameter. The bound applies uniformly when the real part is positive and at most two.

**Definition 1.3 (DeltaSpike).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.DeltaSpike`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.DeltaSpike` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

The dilation kernel composes the input kernel with x raised to the reciprocal of epsilon, then divides its value by epsilon.

## References

- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.DeltaSpike`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinConvolution`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/MellinCalculus.MellinOfPsi`
