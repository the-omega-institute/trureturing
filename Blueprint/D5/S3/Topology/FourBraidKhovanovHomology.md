# Integral cohomology from a chain contraction

## Abstract

Integral cohomology from a chain contraction

**Theorem 1.1 (A contraction identifies cycles modulo boundaries).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovHomology.cohomologyEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovHomology.cohomologyEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The middle cohomology of an integral three-term complex is the actual kernel of the outgoing map modulo the restricted image of the incoming map. Projection onto the residual free group descends because it annihilates boundaries. Inclusion sends each residual vector to a cycle. Their first composition is the identity on residual vectors. On a cycle, the chain homotopy identifies the second composition with the original vector modulo boundaries. This is an integral linear equivalence.

## References

- Truth anchor: `D5/S3/Topology/FourBraidKhovanovHomology.cohomologyEquiv`
- Dependency: [D5/S3/Topology/FourBraidKhovanovCube](FourBraidKhovanovCube.md)
