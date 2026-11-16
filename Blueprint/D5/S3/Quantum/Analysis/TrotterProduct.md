# The General Banach-Algebra Lie-Trotter Formula

## Abstract

The Lie-Trotter product converges in every complete real normed algebra with norm-one identity, without a commutation hypothesis.

**Theorem 1.1 (Power differences in a normed ring).**

Lean statement: `D5/S3/Quantum/Analysis/TrotterProduct.norm_pow_sub_pow_le_of_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TrotterProduct.norm_pow_sub_pow_le_of_norm_le` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

In any normed ring with norm-one identity, if C is at least one and bounds the norms of S and T, then for every natural n the norm of S to the nth power minus T to the nth power is at most n times C to the nth power times the norm of S minus T. No normed-algebra structure or completeness is needed. At C equal to one this original supplier controls power differences of the continuous endomorphisms used in the original Gaussian uniform trace estimate. The proof and attribution are those of the selected original source.

**Theorem 1.2 (Noncommuting exponential products converge).**

Lean statement: `D5/S3/Quantum/Analysis/TrotterProduct.trotter_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TrotterProduct.trotter_product` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

Let A be any normed ring with a real normed-algebra structure, completeness and norm-one identity. For every pair X,Y in A, the nth power of the product (exp(n inverse times X) times exp(n inverse times Y)) converges in norm to exp(X+Y) as natural n tends to infinity. Multiplication need not commute. There is no matrix, finite-dimensional, skew-adjoint or Hermitian restriction.

Write s for the sum of the two input norms. For every natural n at least one, the proof bounds the norm error by n inverse times s squared times (3+s) times exp(2s). The quadratic exponential remainder gives a one-step defect of second order. Growth-controlled telescoping multiplies this defect by n times a uniformly bounded exponential factor. This is the inverse-step estimate used to obtain convergence.

The supplier note's General Lie-Trotter products section selects Zayn Blore's original TrotterGeneral proofs at immutable source revision ff2d274f684df1c500c9f4dae8541c57f236ca6a. Its independent partial-trace and entropy selection uses revision 13eda16971c66de4bc9f550e418dd4fdf59a5121. The receiver directly supplies the repeated-exponential identity through Mathlib's exp_nsmul after restricting scalars to the rationals; no additional algebra hypothesis is imposed on the theorem. No original-proof or mathematical-novelty claim is made for the source selection. The complete source license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TrotterProduct.norm_pow_sub_pow_le_of_norm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/TrotterProduct.trotter_product`
