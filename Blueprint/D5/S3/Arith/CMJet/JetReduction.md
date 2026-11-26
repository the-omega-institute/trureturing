# Reduction of the integer lemniscatic section jets

## Abstract

Coefficient reduction on the curve extends to both polynomial variables.

**Theorem 1.1 (Reduction commutes with differentiation).**

Lean statement: `D5/S3/Arith/CMJet/JetReduction.jetReduction_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/JetReduction.jetReduction_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient derivative and the ordinary polynomial derivative both commute with the lifted ring homomorphisms.

**Theorem 1.2 (Exact residue of every integer jet).**

Lean statement: `D5/S3/Arith/CMJet/JetReduction.jet_reduce_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/JetReduction.jet_reduce_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The section, all derivative orders, and evaluation commute with reduction, for every modulus.

## References

- Truth anchor: `D5/S3/Arith/CMJet/JetReduction.jetReduction_deriv`
- Truth anchor: `D5/S3/Arith/CMJet/JetReduction.jet_reduce_cast`
- Dependency: [D5/S3/Arith/CMJet/ActualRestrictedRecurrence](ActualRestrictedRecurrence.md)
