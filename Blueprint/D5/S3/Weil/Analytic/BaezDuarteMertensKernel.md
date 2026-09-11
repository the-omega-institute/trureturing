# BaezDuarteMertensKernel

## Abstract

The original inverse-square kernel has a corrected beta integral and a uniform power bound.

Write B(u,v) for the public Complex.betaIntegral. For real x>=1 set kernel(k,x)=x^(-2)*(1-x^(-2))^k. The derivative in the formulas is -2*x^(-3)*(1-x^(-2))^k+2*k*x^(-5)*(1-x^(-2))^(k-1). Real powers use Real.rpow; k is natural. Every beta estimate quantifies one positive real C before all k>=1, so its constant is independent of k. Write weightedKernel(b,k)(x)=x^(-2*b-1)*(1-x^(-2))^k. The kernel integrals and their integrability are proved for every natural k, including zero, and every real b>0.

**Theorem 1.1 (Uniform beta power bound).**

$$b>0\Rightarrow \exists C>0, \forall k\ge 1, \operatorname{norm}\left(\operatorname{B}\left(b, k+1\right)\right)\le C \operatorname{rpow}\left(k, -b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The public GammaSeq identity and convergence bound the entire positive-index beta sequence. This directly reuses the existing Euler limit, with no new Gamma asymptotic.

**Theorem 1.2 (Correctly indexed derivative).**

$$k\ge 1\land x\ge 1\Rightarrow \operatorname{HasDerivAt}\left(\operatorname{kernel}\left(k\right), \operatorname{kernelDerivative}\left(k, x\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For k>=1 and x>=1 the stated derivative is a HasDerivAt certificate of the actual original kernel. The negative first term and k-1 exponent are retained.

**Theorem 1.3 (Integrability of the transformed kernel).**

$$b>0\Rightarrow \operatorname{IntegrableOn}\left(\operatorname{weightedKernel}\left(b, k\right), \operatorname{Ioi}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The inverse-square substitution maps x>1 to 0<y<1. The injective Jacobian theorem transports beta integrability; an integral value alone is never used as integrability evidence.

**Theorem 1.4 (The beta integral with its half factor).**

$$b>0\Rightarrow \operatorname{integralIoi}\left(1, \operatorname{weightedKernel}\left(b, k\right)\right)=\frac{\operatorname{Re}\left(\operatorname{B}\left(b, k+1\right)\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Here weightedKernel(b,k)(x)=x^(-2*b-1)*(1-x^(-2))^k. Its integral over x>1 is the real part of B(b,k+1) divided by two. This proves the factor missing in the printed square substitution.

**Theorem 1.5 (A common bound for both derivative terms).**

$$b>0\Rightarrow \exists C>0, \forall k\ge 1, \operatorname{Re}\left(\operatorname{B}\left(b, k+1\right)\right)+k \operatorname{Re}\left(\operatorname{B}\left(b+1, k\right)\right)\le C \operatorname{rpow}\left(k, -b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_combined_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The public beta recurrence identifies the sum of the two real beta terms with (1+b)*Re(B(b,k+1)). The preceding uniform bound supplies a single positive C for the full positive-index sequence.

## References

- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_bound`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_combined_bound`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_hasDerivAt`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integrable`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integral`
