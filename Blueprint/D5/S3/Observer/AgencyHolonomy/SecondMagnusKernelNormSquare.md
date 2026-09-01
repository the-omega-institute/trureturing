# Exact Second-Magnus Kernel Strength

## Abstract

Identify the exact squared strength of the alternating Fourier slot kernel.

**Theorem 1.1 (Exact alternating-kernel strength).**

$$\forall fp \in \mathbb{R}, fq \in \mathbb{R}, t1 \in \mathbb{R}, t2 \in \mathbb{R},\; \left\lVert \operatorname{K}\left(fp, fq, t1, t2\right) \right\rVert^{2} = 4 \times \operatorname{sin}\left((t1 - t2) \times \frac{(fp - fq)}{2}\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusKernelNormSquare.second_magnus_swap_kernel_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared norm of the alternating two-slot Fourier kernel is exactly four times the squared sine of the half time-frequency area.

Consequently every nonzero frequency gap has an explicit half-turn sample with squared response four. The result is pairwise and asserts no common sampling clock or zeta-zero comparison.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusKernelNormSquare.second_magnus_swap_kernel_norm_sq`
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](SecondMagnusSwapCurvature.md)
