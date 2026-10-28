# Weighted prime limits

## Abstract

Quantitative Chebyshev error decay gives convergence of the original weighted prime error.

**Theorem 1.1 (Absolute integrability of the actual error kernel).**

Lean statement: `D5/S3/Weil/Mertens/WeightedPrimeLimit.chebyshev_error_kernel_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedPrimeLimit.chebyshev_error_kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real function K(u)=(psi(u)-u)/u^2 is Lebesgue integrable on (1,infinity), where psi is the actual Chebyshev function. MediumPNT supplies positive c and D and an eventual bound |psi(u)-u| <= D*u*exp(-c*(log u)^(1/10)). For u above a threshold B>=2, this bounds |K(u)| by D*exp(-c*(log u)^(1/10))/u.

Mathlib's integrableOn_rpow_mul_exp_neg_mul_rpow at exponent s=0 makes exp(-c*v^(1/10)) integrable on v>0. The logarithmic substitution integrableOn_comp_log_Ioi makes its divided logarithmic pullback integrable on u>1. On (1,B], monotonicity makes psi measurable and bounds |K| by psi(B)+B. Integrating the bounded part and the dominated tail covers the full interval; continuity of the arithmetic step function is not assumed.

**Theorem 1.2 (Euler-normalized limit of the original Mangoldt error).**

Lean statement: `D5/S3/Weil/Mertens/WeightedPrimeLimit.E1Lambda_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedPrimeLimit.E1Lambda_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the real variable t tends to infinity, the original Mertens.E₁Λ(t) tends to minus Real.eulerMascheroniConstant. The original expression is sum(Lambda(n)/n,0<n<=floorNat(t))-log(t), with an inclusive upper endpoint and every prime power retained.

Absolute integrability supplies the premise of complete_chebyshev_tail_identity. For every real t>=2, rearrangement gives E₁Λ(t)=(psi(t)-t)/t-EulerGamma-integral(K(u),u>t). Quantitative MediumPNT makes the relative error tend to zero; the integral tail tends to zero. The constant minus one in the tail identity cancels with t/t=1.

**Theorem 1.3 (A finite limit at real infinity for the original prime error).**

Lean statement: `D5/S3/Weil/Mertens/WeightedPrimeLimit.exists_E1p_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/WeightedPrimeLimit.exists_E1p_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a real ell such that the original Mertens.E₁p(t) tends to ell as the real variable t tends to infinity. Here E₁p(t) is sum(log(p)/p,0<p<=floorNat(t),p prime)-log(t). No integrability, convergence or Riemann-hypothesis premise is imposed.

The original Estimates identity expresses E₁Λ(t)-E₁p(t) as the finite sum of nonprime Lambda(n)/n. Mathlib's vonMangoldt.summable_residueClass_non_primes_div at modulus one supplies summability of exactly these terms. Its natural partial sums converge, and composing with floorNat(t)+1 gives convergence for all real t. The term n=0 vanishes, so the range sum equals the inclusive positive-index sum. Subtracting this convergent residual from the Euler-normalized Mangoldt limit proves the existential conclusion; identification of the residual sum is unnecessary.

## References

- Truth anchor: `D5/S3/Weil/Mertens/WeightedPrimeLimit.E1Lambda_tendsto`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedPrimeLimit.chebyshev_error_kernel_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/WeightedPrimeLimit.exists_E1p_limit`
- Dependency: [D5/S3/Weil/Mertens/CompleteChebyshevTailIdentity](CompleteChebyshevTailIdentity.md)
- Dependency: [D5/S3/Weil/Mertens/Estimates](Estimates.md)
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/MediumPNT](../PrimeNumberTheorem/MediumPNT.md)
