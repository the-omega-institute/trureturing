# Shifted zero kernel

## Abstract

A two-sided multiplicity count controls the shifted inverse-square kernel of the original zero configuration.

**Theorem 1.1 (Summability and the logarithmic bound).**

Lean statement: `D5/S3/Weil/ZetaExplicit/ShiftedZeroKernel.shifted_zero_kernel_summable_tsum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/ShiftedZeroKernel.shifted_zero_kernel_summable_tsum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be a ZeroConfig, with its original distinct complex carrier and natural multiplicities. Assume A>=1 and, for every real t, the multiplicity count Z.N(t,t+1) is at most A*log(|t|+3). For each real s, the family m(rho)/(1+(s-Re gammaOf(rho))^2) is summable over that carrier. Its real sum is at most 27*A*totalWeight*log(|s|+3), where totalWeight is the existing convergent integer sum of log(|j|+3)/(1+j^2).

First bound every finite subset of the carrier. Group it by k=ceil(Im rho)-1, so every fiber lies in the original half-open window (k,k+1]. The finite-window multiplicity estimate applies to the complete fiber. A displacement of at most one gives 1+(s-k)^2<=3*(1+(s-Im rho)^2). This keeps both signs of the ordinate and assigns an integral ordinate t to (t-1,t].

For the integer sum set n=ceil(s)-1 and translate each finite integer set by -n. Writing k=n+j gives 1+j^2<=3*(1+(s-k)^2) and log(|n+j|+3)<=2*log(|s|+3)+log(|j|+3). Since log(|j|+3)>=1, the unweighted finite inverse-square sum is bounded by totalWeight. The translated weighted sum is therefore at most 9*totalWeight*log(|s|+3). Combining this with the multiplicity-fiber estimate gives the factor 27. Nonnegative finite-sum boundedness proves summability before the actual infinite sum is bounded.

The estimate uses the local count, not RH or zero spacing. It is a scalar kernel estimate. Applying it to the original Weil form still requires a strip evaluation estimate and the appropriate integration and continuity arguments. It alone does not identify a form domain or core, prove global positivity, or prove RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaExplicit/ShiftedZeroKernel.shifted_zero_kernel_summable_tsum_le`
