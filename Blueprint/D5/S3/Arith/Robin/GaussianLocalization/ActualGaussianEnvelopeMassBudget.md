# The full signed envelope response

## Abstract

The full signed envelope response.

**Theorem 1.1 (The full signed envelope response).**

Lean statement: `D5/S3/Arith/Robin/GaussianLocalization/ActualGaussianEnvelopeMassBudget.full_Hv_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GaussianLocalization/ActualGaussianEnvelopeMassBudget.full_Hv_le_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>=1 and gamma>10, the actual V exchange expresses integral H*V as a full complex spectral response. Its polynomial norm is at most Im(rho)^2+gamma^2+5/2. The actual height gives Im(rho)^2>100, so the Gaussian suppresses this polynomial by (gamma+10)^2*exp(-100*m). Multiplication by the strip factor exp(17*m) and the reciprocal coefficient bound yields 2*(gamma+10)^2*exp(-83*m)*Im(rho)^(-2).

The complete inverse-square mass less than two pays absolute convergence of the response, and norm(sum)<=sum(norm) gives abs(integral Re(H)*V)<=4*(gamma+10)^2*exp(-83*m). This bounds the SIGNED integral; it does not bound the integral of abs(Re(H))*V by the same tiny quantity.

The consumed full_Hv_original relaxes four to the original constant 1000. OriginalPositiveUPeak uses it only after the signed localization debit has been retained. It is a consumed helper, rather than an additional independent result.

## References

- Truth anchor: `D5/S3/Arith/Robin/GaussianLocalization/ActualGaussianEnvelopeMassBudget.full_Hv_le_four`
- Dependency: [D5/S3/Weil/ZeroData/ActualGaussianZeroSum](../../../Weil/ZeroData/ActualGaussianZeroSum.md)
