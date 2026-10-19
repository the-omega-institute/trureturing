# Actual triangle structural row interval 0 to 4096

## Abstract

Complete actual structural checks for one original EJM row interval.

This module checks every original triangle row with index at least 0 and below 4096. Each split retains all four actual values, earlier child indices, stored lower inequalities and full partial-assignment symmetry transport. Terminal rows retain exact completed events. The split changes kernel checkpoint boundaries while preserving every original obligation.

**Theorem 1.1 (The whole original row interval passes its exact structural check).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock0.accepted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock0.accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The receipt quantifies over the entire finite interval and is consumed by EJMStructureCertificates. It supplies structural checks only; terminal score bounds, global search acceptance and nonlocality require their separate full proofs.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock0.accepted`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport](EJMPartialBoundTransport.md)
