# Actual principal units

## Abstract

Principal units in the actual original-label kernel.

**Theorem 1.1 (The actual elementary abelian subgroup).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup.actual_principal_unit_structure`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup.actual_principal_unit_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any odd prime and K any finite field, in an arbitrary universe, of order p^n over F=ZMod p. For every F-linear q with q(1)=0, the actual original-group label-projection kernel consists of invertible commuting operators paired with the identity original label. The unit group of the actual commutant algebra is canonically isomorphic to this kernel: retain the operator and add the identity label; the inverse retains the operator and its inverse.

Transport the leading-one principal units through this native group equivalence. The theorem states jointly that all pairs of elements of this actual subgroup commute, every element has p-th power one, and the subgroup has order p^(n(p−2)+n²). All F-linear top endomorphisms are included. The characteristic-p and radical arguments apply to p=3, and the cardinality counts every normalized parameter q. No additional literature novelty is asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup.actual_principal_unit_structure`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup](OddPrimeJetGroup.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits](OddPrimeJetRadicalUnits.md)
