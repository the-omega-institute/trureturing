# Square-integrable kernels on complex L²

## Abstract

Bounded integral operators, their adjoints, and the Hilbert–Schmidt estimate.

**Definition 1.1 (Integral operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On an s-finite measure space, a square-integrable complex kernel defines a bounded linear operator on complex L².

**Theorem 1.2 (Section integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each vector f in L², the output at almost every x is the integral of K(x,y) f(y) in y.

**Theorem 1.3 (Operator norm estimate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator norm is bounded by the L² norm of the kernel. Apply Cauchy–Schwarz in each section and integrate the square of that bound.

**Theorem 1.4 (Product integral for the pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inner product of f with the operator applied to g is the product integral of the conjugate of f(x) times K(x,y) times g(y). The product belongs to L¹ by Cauchy–Schwarz on the product space.

**Theorem 1.5 (Independence of the representative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_congr_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_congr_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Kernels that agree almost everywhere for the product measure induce the same operator.

**Theorem 1.6 (Adjoint kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The adjoint is the integral operator with the conjugate transposed kernel. Exchange the product coordinates in the pairing.

**Definition 1.7 (Bounded multiplication).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

An essentially bounded complex function acts on L² by multiplication.

**Theorem 1.8 (Pointwise multiplication).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The multiplier output agrees almost everywhere with the pointwise product.

**Theorem 1.9 (Left and right multipliers).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_mulOp_both`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_mulOp_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Composing the kernel operator with a left multiplier g and a right multiplier h gives the kernel g(x) K(x,y) h(y), which is again square integrable.

**Theorem 1.10 (Hilbert–Schmidt membership).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hilbertSchmidt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hilbertSchmidt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each finite set of basis vectors, apply Bessel's inequality to the conjugate kernel section. Integrate this finite sum to bound it uniformly and obtain summability.

**Theorem 1.11 (Squared Hilbert–Schmidt norm estimate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hsSq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hsSq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared Hilbert–Schmidt norm is at most the integral of the squared kernel norm on the product space. This connects the square integrability of a kernel to the operator estimate used for Eq. (71) of Satishchandran and Sorce.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_adjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_congr_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hilbertSchmidt`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_hsSq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_mulOp_both`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.integralKernelOp_norm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS.mulOp_ae`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../TraceClass/HilbertSchmidt.md)
