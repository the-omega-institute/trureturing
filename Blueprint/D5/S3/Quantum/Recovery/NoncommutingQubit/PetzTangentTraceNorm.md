# Full trace-norm bound for the faithful qubit Petz tangent

## Abstract

The faithful physical tangent bound in the full trace norm.

**Theorem 1.1 (Full trace norm and conditional BKM form).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be positive definite with trace one on a retained qubit times a nonempty finite environment. Write P for its actual partial trace and M for the partial trace of an arbitrary complex tangent H. If p₀ and p₁ are the eigenvalues of P, the full trace norm of H minus the Petz recovery of M, squared, is at most K(2 sqrt(p₀ p₁)) times the joint BKM quadratic form of H minus the marginal form of M.

Take a single unitary attaining trace-norm duality and express it in the joint spectral basis. The sum of its squared entry moduli weighted by (λᵢ + λⱼ)/2 is one by the row and column norm identities. Weighted Cauchy–Schwarz then applies the faithful sum over the joint spectrum.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent`
- Dependency: [D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical](PetzTangentPhysical.md)
