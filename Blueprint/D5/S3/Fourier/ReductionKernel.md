# Cotangent Reduction Kernel

## Abstract

Reduction of a fourth-harmonic cotangent kernel to untwisted sine terms.

**Theorem 1.1 (The fourth-harmonic cotangent kernel reduces to sine terms).**

$$\forall x \in \mathbb{R},\quad \sin(x) \neq 0 \Rightarrow \operatorname{cos}(4x)\cdot\frac{\operatorname{cos}(x)}{\sin(x)} = \frac{\operatorname{cos}(x)}{\sin(x)} - 2\sin(2x) - \sin(4x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ReductionKernel.reduction_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing cotangent as cosine divided by sine, the nonzero denominator permits field reduction. Double-angle identities then show that both sides equal the same cubic expression in cosine times sine.

**Theorem 1.2 (The kernel reduction holds at golden-ratio multiples).**

$$\forall k \in \mathbb{N},\quad \sin(\pi k\varphi) \neq 0 \Rightarrow \operatorname{cos}(4\pi k\varphi)\cdot\operatorname{cot}(\pi k\varphi) = \operatorname{cot}(\pi k\varphi) - 2\sin(2\pi k\varphi) - \sin(4\pi k\varphi).$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ReductionKernel.reduction_kernel_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the universal identity at pi times an integer times the golden ratio yields the literal cotangent-kernel form under its nonzero-sine hypothesis.

## References

- Truth anchor: `D5/S3/Fourier/ReductionKernel.reduction_kernel`
- Truth anchor: `D5/S3/Fourier/ReductionKernel.reduction_kernel_golden`
