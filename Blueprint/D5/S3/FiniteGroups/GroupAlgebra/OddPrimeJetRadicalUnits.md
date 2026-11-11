# Principal units

## Abstract

The principal units of the actual odd-prime commutant.

Let p be any odd prime and K any field, in any universe, over F=ZMod p. For every F-linear q with q(1)=0, take the actual commutant algebra on polynomials of degree less than p. Its leading-zero ideal is J. Principal units are its invertible operators with leading scalar one.

**Theorem 1.1 (Commutativity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_commute`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the identity from each principal unit gives two elements of the commutative ideal J, so the original units commute under actual composition.

**Theorem 1.2 (Prime exponent).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_pow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each principal unit has p-th power one. For u=1+j, the characteristic-p binomial identity gives u^p=1+j^p=1. This includes p=3 and requires no logarithm or exponential construction.

**Theorem 1.3 (The exact order).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If K is finite of order p^n, the principal unit group has order p^(n(p−2)+n²). Subtracting the identity identifies its underlying set with J. The actual commutant coordinate equivalence leaves p−2 free K-valued coefficients and one arbitrary F-linear endomorphism of K, of prime-field dimension n². No condition on T(1) or trace(T) is imposed. These statements use classical nilpotent-ideal and characteristic-p calculus and make no literature-novelty assertion.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_cardinality`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_commute`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits.principalUnits_pow`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical](OddPrimeJetRadical.md)
