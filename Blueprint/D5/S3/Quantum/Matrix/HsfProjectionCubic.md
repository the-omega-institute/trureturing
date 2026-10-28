# Finite dimensional projection certificate

## Abstract

Projection directions and signed Hermitian involutions for the actual cubic sandwiched trace.

**Definition 1.1 (A positive trace localizer).**

Lean statement: `D5/S3/Quantum/Matrix/HsfProjectionCubic.traceLocalizer`

*Formalization.* `D5/S3/Quantum/Matrix/HsfProjectionCubic.traceLocalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite complex square matrices A,B,q, traceLocalizer(A,B,q) is Re Tr(A q* B q). Its positivity proof assumes A and B are PSD, uses the square root of A and PSD congruence by q sqrt(A), then applies cyclicity and nonnegativity of a PSD trace. It allows singular weights and arbitrary q; the product A q* B q is not asserted PSD.

**Definition 1.2 (Eleven positive rational trace squares).**

Lean statement: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projectionSOS`

*Formalization.* `D5/S3/Quantum/Matrix/HsfProjectionCubic.projectionSOS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write L=I-P and Lambda(A,B,q)=Re Tr(A q* B q). The certificate is the sum of these eleven weighted localizers: 84 Lambda(P,H,LH-(31/84)G-(11/84)PG); (4247/84) Lambda(P,H,G+(5707/4247)PG); (107292/4247) Lambda(P,H,PG); 30 Lambda(P,G,LH-(4/5)G-(13/30)PG); (729/5) Lambda(P,G,G+(388/729)PG); (24881/1458) Lambda(P,G,PG); 60 Lambda(L,H,PH-(7/20)PG); (1053/20) Lambda(L,H,PG); 81 Lambda(L,G,H-(20/81)PH-(43/81)PG); (1382/81) Lambda(L,G,PH-(187/691)PG); (11003/691) Lambda(L,G,PG). All weights are positive. Nonnegativity follows when H,G are PSD and P is Hermitian idempotent.

**Theorem 1.3 (The exact actual coefficient identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, Hermitian complex matrices H,G,P with P*P=P, 27(coefficient2(H+G,H,P)-3 coefficient3(H+G,H,P)) equals projectionSOS(H,G,P). The coefficients are the original ordered coefficients in HsfQubitMixedCubic. The proof expands the eleven rational squares and uses only trace cyclicity, Hermitian adjoint reversal in the real trace, and P*P=P. Distinct letters are never commuted. Positivity is not needed for this identity.

**Theorem 1.4 (Actual derivatives in a projection direction).**

Lean statement: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X,H,P be finite complex square matrices, with H and X-H PSD and P Hermitian idempotent. Define g(t)=Re Tr(((I+tP)^(-1/3)(X+tH)(I+tP)^(-1/3))^3), using actual CFC powers. Then g'''(0)<=g''(0). The eleven-term identity proves the coefficient gap nonnegative, and HsfIdentityCubicDerivatives.identity_cubic_trace_derivatives identifies g''(0)=2 coefficient2 and g'''(0)=6 coefficient3. No Taylor premise, rank restriction, invertibility of the directions, or commutation assumption is used. Empty index types and singular PSD endpoints are included. The statement also permits singular X; positive definite X gives the intended positive-center application.

**Theorem 1.5 (The signed constant-five estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfProjectionCubic.involution_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfProjectionCubic.involution_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X,A,J be finite complex square matrices, with X+A and X-A PSD and J Hermitian with J*J=I. For the actual CFC sandwich f(t)=Re Tr(((I+tJ)^(-1/3)(X+tA)(I+tJ)^(-1/3))^3), one has f''(0)>=0 and |f'''(0)|<=5 f''(0). Put H=(X+A)/2 and P=(I+J)/2. Exact ordered coefficient identities give signed coefficient2=4 positive coefficient2 and signed coefficient3=4 positive coefficient2+8 positive coefficient3. Apply the projection certificate and repeat with -A,-J, whose projection is I-P. The actual Taylor theorem supplies the derivatives. All finite dimensions and singular endpoints are included, with no pairwise commutation.

This is the alpha=3 identity-denominator projection subclass and its signed involution consequence of the compatibility problem of He, Saunderson and Fawzi, arXiv:2502.05627v1, Conjecture 6.2; published DOI 10.1007/s10107-025-02314-0, Conjecture 1. Arbitrary noncommuting positive contractions, independent denominator centers, other exponents, and the full HSF conjecture remain open here. No literature priority is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfProjectionCubic.involution_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projectionSOS`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_certificate`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfProjectionCubic.projection_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfProjectionCubic.traceLocalizer`
- Dependency: [D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives](HsfIdentityCubicDerivatives.md)
