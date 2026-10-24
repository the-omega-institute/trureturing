# Convergence of the original forward Mellin integral

## Abstract

The complete Chebyshev forward response has an absolutely convergent Mellin integral under a von Koch bound.

**Theorem 1.1 (Absorbing a logarithmic error into a small power).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.error_power_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.error_power_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C>=0, eta>0 and t>=2, the pointwise hypothesis |psi(t)-t|<=C*sqrt(t)*log(t)^2 implies |psi(t)-t|<=(C/eta^2)*t^(1/2+2*eta). This uses log(t)<=t^eta/eta and retains the complete Chebyshev psi.

**Theorem 1.2 (Growth of the literal normalized response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardResponse_power_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardResponse_power_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H(x)=x^(4/5), w(x)=(1+log(x))/(x^2*log(x)^2), E(x)=psi(x)-x and T(x)=sqrt(x)/H(x)^2*integral_0^H(x) (E(x+u)-E(x))*w(x+u)/w(x) du. Assume C>=0 and |E(t)|<=C*sqrt(t)*log(t)^2 for every t>=2. For x>=3 and eta>0, |T(x)|<=2*(C/eta^2)*2^(1/2+2*eta)*x^(1/5+2*eta). Indeed H(x)<=x, so x<=x+u<=2*x throughout the original window. The ratio of the positive decreasing weights lies between zero and one. The integral bound then uses the full interval of length H(x).

**Theorem 1.3 (Absolute convergence for Re(s)>1/5).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardMellin_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardMellin_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume there exists a finite real C with the von Koch bound |psi(t)-t|<=C*sqrt(t)*log(t)^2 for every t>=2. For every real x0>=3 and complex s with Re(s)>1/5, the function T(x)*x^(-s-1) is Lebesgue integrable on (x0,infinity). In particular the initially specified Mellin integral for Re(s)>1/2 is defined. Choosing eta=(Re(s)-1/5)/4 makes the real-power majorant integrable. Joint measurability follows by writing the variable interval integral as the difference of two measurable interval indicators and integrating with respect to the displacement. This conclusion does not assert the meromorphic continuation or its residues.

**Theorem 1.4 (Absolute integrability of the original kernel row volume).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.kernel_mellin_majorant_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.kernel_mellin_majorant_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=4 and Re(s)>1/2, the function |x^(-s-1)|*moment(x,0) is integrable on [x0,infinity). The zero-exponent moment is exactly the total volume of the original price-difference kernel. Its previously proved moving-window moment estimate implies |moment(x,0)|<=(5/2)*sqrt(x) for x>=4. The resulting majorant is (5/2)*x^(-Re(s)-1/2), which is integrable in the stated half-plane. Joint measurability of the original kernel gives measurability of its row volume. This analytic majorant does not require the von Koch hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.error_power_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardMellin_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.forwardResponse_power_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernelMellinConvergence.kernel_mellin_majorant_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernelTransport](ForwardKernelTransport.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutAggregate](OriginalMovingCutAggregate.md)
