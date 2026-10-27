# Uniform integrability of literal low restrictions

## Abstract

Uniform integrability of literal low restrictions

**Theorem 1.1 (Uniform integrability of literal low restrictions).**

Lean statement: `D5/S3/Topology/Measures/L1Biting.uniformIntegrable_complements`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Biting.uniformIntegrable_complements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. Assume mu is finite. Let f be an L1 sequence bounded in norm by a real B, let K be a natural sequence with n < K(n), and let c be a real sequence tending to a real alpha. Suppose every fixed tailNorm(k,f(n)) tends to c(k) and the moving tailNorm(K(n),f(n)) tends to alpha. Then the coerced sequence of literal restrictions of f(n) to the complements of tailSet(K(n),f(n)) is UniformIntegrable at exponent one. Exact nested-tail subtraction gives the late-index bounds. The finite initial family is controlled separately before invoking the hard-tail characterization. No weak convergence is assumed.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1Biting.uniformIntegrable_complements`
- Dependency: [D5/S3/Topology/Measures/L1TailConcentration](L1TailConcentration.md)
