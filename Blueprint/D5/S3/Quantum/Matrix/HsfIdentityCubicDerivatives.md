# Affine Hermitian power derivatives

## Abstract

Actual finite dimensional CFC power derivatives at the identity.

**Theorem 1.1 (Differentiation on a fixed spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed Hermitian matrix K of arbitrary finite size, the derivative of cfc(f(t),K) is cfc(g,K) whenever the scalar derivatives of f(t) at each eigenvalue of K equal g there. The proof uses the fixed spectral unitary and a finite dimensional continuous linear map.

**Theorem 1.2 (The actual affine matrix power derivative).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real p,t and Hermitian K, assume 1+t*x>0 for every real spectral value x of K. Then the actual CFC function s maps to (I+sK)^p has derivative p K (I+tK)^(p-1). Positivity persists in a neighborhood because the fixed spectrum is finite. No Taylor premise is used.

**Theorem 1.3 (The original sandwich trace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.sandwich_trace_germ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.sandwich_trace_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite matrices X,H and Hermitian K, the real trace of ((I+tK)^(-1/3)(X+tH)(I+tK)^(-1/3))^3 agrees near zero with the real trace of ((X+tH)(I+tK)^(-2/3))^3. Powers are actual CFC powers. The proof uses scalar powers on the fixed positive spectrum and cyclicity of trace, without commuting X,H with K.

**Theorem 1.4 (Differentiating a cubic trace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.cubic_trace_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.cubic_trace_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If B has nearby actual first and second matrix derivatives B1,B2, and B2 has derivative B3 at zero, cyclicity gives the exact second and third derivatives of Re Tr(B^3). The second is Re Tr(3 B2 B^2+6 B1^2 B), and the third is Re Tr(3 B3 B^2+9 B2 B1 B+9 B2 B B1+6 B1^3), all at zero.

**Theorem 1.5 (Actual derivatives of the reduced trace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.affine_power_cubic_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.affine_power_cubic_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite matrices X,H, Hermitian K and any real p, put L=H+pXK, M=2pHK+p(p-1)XK^2 and N=3p(p-1)HK^2+p(p-1)(p-2)XK^3. The actual reduced trace Re Tr(((X+tH)(I+tK)^p)^3) has second derivative Re Tr(3M X^2+6L^2 X) and third derivative Re Tr(3N X^2+9MLX+9MXL+6L^3) at zero. The nearby derivatives are proved from the actual CFC curve.

**Theorem 1.6 (The original ordered coefficients).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite X,H and Hermitian K, the actual CFC sandwich trace with exponent -1/3 has second derivative twice coefficient2 and third derivative six times coefficient3 at zero. The coefficients are exactly the original ordered trace words of HsfQubitMixedCubic, not a renamed jet expression or a Taylor assumption.

**Theorem 1.7 (The physical qubit estimate at identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X=diag(a,b) with a,b>0, and let H,K be arbitrary complex Hermitian two by two matrices. Assume X+H,X-H,I+K,I-K are PSD. Then for the actual CFC function phi(t)=Re Tr(((I+tK)^(-1/3)(X+tH)(I+tK)^(-1/3))^3), phi''(0)>=0 and |phi'''(0)|<=5 phi''(0). The PSD endpoints may be singular, and no trace or phase constraint is imposed on H or K. This is the alpha=3, Y=I, diagonal-X qubit restriction, not the arbitrary-denominator or arbitrary-dimension result.

**Theorem 1.8 (Every positive definite qubit numerator).**

Lean statement: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite complex Hermitian two by two X, and Hermitian H,K satisfying X+H,X-H,I+K,I-K PSD, the same actual CFC sandwich trace satisfies phi''(0)>=0 and |phi'''(0)|<=5 phi''(0). Unitary diagonalization preserves the original ordered trace coefficients and transports all four PSD endpoints. The actual derivative bridge is applied to the original X,H,K. Repeated eigenvalues and singular endpoints are included. The denominator base point remains Y=I and the dimension is two.

The motivating compatibility question is due to He, Saunderson and Fawzi: arXiv:2502.05627v1, Conjecture 6.2; published DOI 10.1007/s10107-025-02314-0, Conjecture 1. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.affine_power_cubic_derivatives`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.cubic_trace_derivatives`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_affine_rpow`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.hasDerivAt_cfc`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.qubit_posdef_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives.sandwich_trace_germ`
- Dependency: [D5/S3/Quantum/Matrix/HsfQubitMixedCubic](HsfQubitMixedCubic.md)
