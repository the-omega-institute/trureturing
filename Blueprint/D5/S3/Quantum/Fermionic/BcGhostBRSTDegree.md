# Ghost degree of the original cubic charge

## Abstract

Ghost degree of the original cubic charge

The number operator is the original locally finite bc ghost-number operator. The cubic is normally ordered with the original b and c vacuum cuts; no intercept is added.

**Theorem 1.1 (The cubic has ghost degree one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostBRSTDegree.ghost_number_Qg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRSTDegree.ghost_number_Qg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the original complex countable occupation Fock space, ghostNumber * Qg - Qg * ghostNumber = Qg. Each normally ordered cubic has two c factors of degree one and one b factor of degree minus one. The commutator passes through the statewise finite cubic sums, using finite support at both v and ghostNumber v.

This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTDegree.ghost_number_Qg`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](BcGhostCharge.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCubic](BcGhostCubic.md)
