# Actual triangle structural row interval 10240 to 12288

## Abstract

Complete actual structural checks for one original EJM row interval.

This module checks every original triangle row with index at least 10240 and below 12288. Each split retains all four actual values, earlier child indices, stored lower inequalities and full partial-assignment symmetry transport. Terminal rows retain exact completed events. Only kernel checkpoint boundaries change.

**Theorem 1.1 (The whole original row interval passes its exact structural check).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4.accepted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4.accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The receipt covers the entire interval and is consumed by EJMStructureCertificates. It supplies structural checks only; terminal score bounds, complete global acceptance and nonlocality require their separate full proofs.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock4.accepted`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport](EJMPartialBoundTransport.md)
