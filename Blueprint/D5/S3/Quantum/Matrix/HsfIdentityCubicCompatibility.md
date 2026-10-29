# Actual endpoint derivatives

## Abstract

Actual cubic HSF compatibility at identity in arbitrary finite complex dimension

**Theorem 1.1 (Actual positive-direction inequality).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.positive_direction_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.positive_direction_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex U,H,K with H,U-H,K,I-K PSD, the original CFC sandwich curve has actual third derivative at zero at most its actual second derivative. This consumes both the four-Gram polynomial certificate and the dimension-free CFC derivative supplier.

**Theorem 1.2 (Actual signed endpoint transfer).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.signed_derivative_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.signed_derivative_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Hermitian K put Hplus=(U+H)/2, Kplus=(I+K)/2, f=curve(U,H,K), g=curve(U,Hplus,Kplus). The actual derivatives satisfy f_second=4 g_second and f_third=12 g_second+8 g_third. The proof identifies both actual CFC curves with their ordered coefficients and proves the transfer identities there, including every noncommuting term.

**Theorem 1.3 (Arbitrary-dimensional actual cubic compatibility at identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.identity_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.identity_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex matrix size, Hermitian K and PSD endpoints U+H,U-H,I+K,I-K, the actual function f(t)=Re Tr(((I+tK)^(-1/3)(U+tH)(I+tK)^(-1/3))^3) satisfies f_second(0)>=0 and abs(f_third(0))<=5 f_second(0). This includes every positive definite U and Hermitian H, arbitrary noncommuting U,H,K, singular endpoints and zero Hessian. The derivative inequality also holds for PSD U. The denominator base point is identity.

**Theorem 1.4 (The sharp scalar direction).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.sharp5`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.sharp5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension one U=H=I,K=-I gives actual second derivative 24 and actual third derivative 120. Thus constant five is attained by an endpoint-feasible positive definite scalar center.

The target is He, Saunderson and Fawzi, arXiv:2502.05627v1 Conjecture 6.2, journal DOI 10.1007/s10107-025-02314-0 Conjecture 1. The formal result has alpha=3 and Y=I; no full-general-Y or literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.identity_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.positive_direction_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.sharp5`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility.signed_derivative_transfer`
- Dependency: [D5/S3/Quantum/Matrix/HsfContractionCubic](HsfContractionCubic.md)
- Dependency: [D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives](HsfIdentityCubicDerivatives.md)
