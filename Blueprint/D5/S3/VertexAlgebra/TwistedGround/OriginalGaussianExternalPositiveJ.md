# The original Hilbert mode sums and the positive J equation

## Abstract

Spatial regularity and positive J equality for the original Gaussian kernel

**Theorem 1.1 (Joint spatial differentiability).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.kernelMode_joint_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.kernelMode_joint_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Booleans square, out and out′ and complex u, v and z with ‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1, the original kernelMode is complex Fréchet differentiable at (u,v) jointly in its two external coordinates with z fixed. The flag square selects T when true and J when false.

For either sign ε, let Xε(w,z) = ∑ₙ wⁿ • externalVector(ε,n,z) in the original Hilbert space H, where the sum is over the natural numbers. For each w in the convergence disk, choose a radius ρ with ‖w‖ < ρ < 1 − ‖z‖. The norms of the terms at ρ form a summable majorant throughout the open disk of radius ρ. Local normal convergence of the vector polynomials gives complex differentiability of each Hilbert-valued sum.

The kernel is the continuous complex bilinear pairing of Xout(u,z) with A(z) applied to Xout′(v,z), where A(z) is the square resolvent for T and the odd resolvent for J. Passing the two sums through the continuous linear maps in the pairing recovers the original mode coefficients by the explicit contraction identities. Absolute summability identifies the iterated sum with the joint sum over ℕ × ℕ. The bilinear chain rule gives the joint derivative, and the strict inequalities ensure the factorization holds on a neighborhood of (u,v).

**Theorem 1.2 (Native positive J kernel equality).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.positiveJ_eq_candidateJ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.positiveJ_eq_candidateJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real r with 0 < r < 1 and complex u and v with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, kernelMode(false, true, true, u, v, (√r : ℂ)) = candidateJ(u, v, (r : ℂ)). These hypotheses include the diagonal and zero external coordinates.

For fixed r, let F be the original positive J kernel minus the regular candidate on the bidisk of radius 1 − √r. The inequality r ≤ √r places that bidisk inside the candidate's spatial domain, where nonvanishing of its W sum gives joint analyticity. The literal kernel is jointly differentiable by the Hilbert mode factorization. Subtracting the candidate equation from the literal displacement equation cancels the common source and the constant 1/4. The difference satisfies a(1−a) ∂₁F(a,b) + b(1−b) ∂₂F(a,b) + (1−3(a+b)/2) F(a,b) = 0.

For real 0 ≤ t ≤ 1, set D_w(t) = 1 − w + tw and φ_w(t) = tw/D_w(t) for w equal to u or v. Both denominators stay nonzero and ‖φ_w(t)‖ ≤ ‖w‖, so the path stays inside the bidisk. Along this path the chain rule and the homogeneous equation give zero derivative for t² F(φ_u(t),φ_v(t))² / (D_u(t)³ D_v(t)³). This expression is constant on [0,1]. Its value is zero at t = 0 and equals F(u,v)² at t = 1, which forces F(u,v) = 0.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.kernelMode_joint_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalPositiveJ.positiveJ_eq_candidateJ`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate](OriginalGaussianExternalAnalyticCandidate.md)
