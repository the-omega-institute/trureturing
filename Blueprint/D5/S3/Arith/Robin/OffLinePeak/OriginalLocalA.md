# The exact original local-A Robin5040 implication

## Abstract

The exact original local-A Robin5040 implication

Assume only rho is an actual nontrivial zero of Mathlib riemannZeta, 1/2<Re(rho) and 0<Im(rho). Set delta=Re(rho)-1/2, D=Im(rho)+10, m0=100*D^2/delta^2, m1=500*D^4/delta^2 and B0=exp(4*(28*m1+20)^2). No existence of such a zero is claimed.

FullZeroGaussianResponse.full_zero_gaussian_response and GaussianPeakLocalization.gaussian_peak_localization supply the existing full positive-peak mechanism. Instantiation with the actual conjugate occurrence family and exact mass produces A in [exp(4*m0),exp(28*m1)] with U(A)>sqrt(A)*(4*log(A)+9). This module does not re-advertise that old spectral or positive-peak mathematics as new.

Actual height gives D>20 and 0<delta<1/2, so m0>160000 and H=log(A)>640000. The actual signed endpoint applies at H=log(A) and selects y<=4*(log(A)+20)^2. WeightedTailTransport.transport_exp identifies its quotient at the same y with Q(exp(y))-I(exp(y))/r(exp(y)). CompleteMertensPeak.finite_mertens_peak_of_signed_endpoint then produces a strict finite Mertens peak and uses LcmRobinResponse.common_robin_response at the actual integer N=Nat.lcmUpto(floorNat(t)).

The result has t in [A,exp(4*(log(A)+20)^2)], 5040<N, divisorRatio(N)>exp(EulerGamma)*log(log(N)), and N<=exp(B0*log(B0)). divisorRatio is the actual divisor sum sigma_1(N)/N. Monotonicity of exp, log and their nonnegative product proves the original global bound after the local bound is established. Only the original hJY binder has been removed; no substitute analytic premise is introduced.

The substantive addition is the signed endpoint-to-finite-arithmetic chain and this original parameter conclusion. Standard Fubini and Gaussian analysis and previously merged zeta suppliers are reused. No RH proof, unconditional Robin counterexample, official Comparator acceptance, full first-pairing P^(1/12) saving or literature-priority claim follows. All results are analytic implications, not finite numerical certificates.

**Theorem 1.1 (The exact original local-A Robin5040 implication).**

Lean statement: `D5/S3/Arith/Robin/OriginalLocalA.original_zero_robin5040_localA`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalLocalA.original_zero_robin5040_localA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact original four-binder implication with its strict peak, strict 5040 cutoff, strict Robin violation, original local t interval and global N bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalLocalA.original_zero_robin5040_localA`
- Dependency: [D5/S3/Arith/Robin/OffLinePeak/FullZeroGaussianResponse](OffLinePeak/FullZeroGaussianResponse.md)
- Dependency: [D5/S3/Arith/Robin/OffLinePeak/GaussianPeakLocalization](OffLinePeak/GaussianPeakLocalization.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint](../../Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailTransport](../../Weil/Mertens/WeightedTailTransport.md)
