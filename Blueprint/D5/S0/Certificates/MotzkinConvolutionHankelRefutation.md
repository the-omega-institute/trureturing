# Motzkin convolution Hankel refutation

## Abstract

The printed universal first equality chain of Conjecture 7 in arXiv:2502.21050v1 is false at r = 4, n = 0. This does not refute a possibly intended restriction r >= 8.

Wang and Zhang, Hankel determinants for convolution powers of Motzkin numbers, arXiv:2502.21050v1, Conjecture 7, prints no lower bound on r. The authors may have intended r >= 8, since Theorems 1–6 cover r = 2 through 7. That interpretation is unverified. This module refutes the printed universal first chain and makes no claim that the authors' intended conjecture is false.

**Theorem 1.1 (The printed universal first chain is false).**

Lean statement: `D5/S0/Certificates/MotzkinConvolutionHankelRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MotzkinConvolutionHankelRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Motzkin numbers are defined by the source's Catalan-binomial sum. Cauchy convolution defines every natural power, and Matrix.det defines every Hankel size, including the empty determinant. At r = 4, n = 0, the conjectured common value would equate H0 = 1 with H4 = -1. The latter is a private kernel-checked numerical computation. The paper's Theorem 4 is corroboration only and is not a proof premise.

## References

- Truth anchor: `D5/S0/Certificates/MotzkinConvolutionHankelRefutation.result`
