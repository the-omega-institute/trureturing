# Regularized covariance transport

## Abstract

Signed covariance in physical four-point coordinates

**Definition 1.1 (Normal covariance in the physical coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.physicalCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.physicalCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either upperA, any chart c, real x, punctures p and q, and complex u and v, evaluate chartCovariance at the two inverse coordinates using the native flags of p and q. If p = q, subtract η(1 + βγ)/(2βγ(β + γ)²), where η is the lowering parameter of p and β and γ are the inverse roots at the two arguments of that puncture. The correction is zero for distinct punctures. Divide the resulting covariance by the product of the two derivatives of the lifted coordinate maps. At a puncture with lowering parameter λ the lift is t ↦ scaleRoot·t/β(t), where t is the native half-coordinate and β(t)² = 1 − λt² with β(0) = 1. Its derivative halfJacobian = scaleRoot/β(t)³ is evaluated at the inverse root.

**Theorem 1.2 (Signed covariance germs with the period discrepancy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take lattice data D with unit Gram determinant, either upperA, real 0 < x < 1, a chart c and any punctures p and q. Let σ_c be 1 in A, (−i√x)⁻¹ in B and i⁻¹ in D. The puncture signs ρ_c are all +1 in A. In the order (P,Q,R,S), they are (+1,+1,+1,−1) in B and (+1,−1,−1,+1) in D. Write P_A = slitPeriod(1 − 1/x), P_B = slitPeriod(x), P_f = slitPeriod(1 − x) and P_D = dPeriod(upperA,1/x). The spatial source uses the chosen lower D root. The D period uses the lower radial lip for upperA = true and the upper lip for false.

Set δ_A = 0, δ_B = 1/(π P_f P_B) and δ_D = 1/(π P_A P_D). Write C_c for physicalCovariance and M_A for physicalSource in A. On a neighborhood of (u,v) = (0,0), C_A(p,q,u,v) − δ_c (σ_c M_A(p,u))(σ_c M_A(q,v)) = ρ_c(p)ρ_c(q) C_c(p,q,u,v).For repeated punctures, the native Cauchy term plus its regular lowering correction, divided by the product of the half-Jacobians, equals (u+v)/(2(u−v)²) off the diagonal. Thus the two chart subtractions differ by exactly the difference of the normalized lowering corrections. Both regularized sides are analytic. Density and continuity extend the identity to the product neighborhood, including coincident evaluations and the center.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.physicalCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport](OriginalFourMOccupationTransport.md)
