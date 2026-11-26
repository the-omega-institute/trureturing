# Physical qubit Petz tangent entries

## Abstract

The physical Petz residual entry is an arcsine average of the arithmetic BKM residual.

**Theorem 1.1 (Arcsine identity and quadratic bound for one spectral pair).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be Hermitian on a retained qubit times a finite environment, and let H be an arbitrary complex matrix. The actual partial trace P of Z is positive definite. Choose joint and marginal unitary diagonalizations U and V, with joint eigenvalues λ and positive marginal eigenvalues p₀, p₁ summing to one. Select a joint pair i, j with λᵢ, λⱼ > 0 and set u = (λᵢ + λⱼ)/2, β = (λᵢ − λⱼ)/(λᵢ + λⱼ), g = sqrt(λᵢ λⱼ)/u and δ = 2 sqrt(p₀ p₁).

Let F(z) be the (i, j) entry of the native arithmetic BKM residual at (z + 1)/2 in the U basis. Let Y be the corresponding entry of H minus the actual square-root Petz sandwich of the partial trace of H. Then Y equals g times the arcsine average of F(z)/(1 − βz). Its squared modulus is at most K(δ) times the Lebesgue integral of |F(z)|²/(2(1 − βz)) on (−1, 1). Here K(1) = 1 and K(δ) = max(2, (3 − δ)/(1 + δ)) for 0 < δ < 1.

Expanding the marginal response in matrix units leaves the two opposite coherences in the same complex entry. The ordinary Petz sandwich replaces each affine marginal inverse by 1/sqrt(pₐ p_b), which is its arcsine average. The even and odd profiles use the two nodes 1 and δ, with the equal-node case included. The substitution t = z⁻² − 1 in the uniform energy produces the two integrals of the paired reciprocal Gram estimate.

**Theorem 1.2 (Sum over the faithful joint spectrum).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.faithful_weighted_tangent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.faithful_weighted_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be positive definite with its qubit marginal P of trace one. Let H be an arbitrary complex tangent and M its partial trace. In the spectral basis of Z, sum the squared moduli of the Petz residual entries Yᵢⱼ divided by (λᵢ + λⱼ)/2. The sum is at most K(2 sqrt(p₀ p₁)) times the joint BKM quadratic form of H minus the marginal BKM quadratic form of M. Each quadratic form is the real trace pairing of the tangent with its logarithmic derivative. The native conditional identity identifies the difference with the integral of the residual energy.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.faithful_weighted_tangent`
- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiConditionalBKM](../../Divergence/UmegakiConditionalBKM.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../BKMFlagRefinementPetz.md)
- Dependency: [D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine](PetzTangentArcsine.md)
- Dependency: [D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram](PetzTangentReciprocalGram.md)
