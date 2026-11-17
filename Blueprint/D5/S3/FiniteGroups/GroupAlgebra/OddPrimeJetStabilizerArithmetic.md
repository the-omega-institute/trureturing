# Arithmetic of the actual jet label stabilizer

## Abstract

The arithmetic divisor constraint on actual odd-prime jet labels.

**Theorem 1.1 (The stabilizer divisor constraint).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.labelGroup_card_dvd_weighted_ambient`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.labelGroup_card_dvd_weighted_ambient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field K of order p^n over F=ZMod p, the actual label stabilizer is identified with a subgroup of the weighted semilinear group Kˣ ⋊ Gal(K/F). Lagrange's theorem therefore gives |labelGroup(q)| dividing (p^n−1)n. This is the arithmetic restriction on label symmetries; the unrestricted commutant factor is separate.

**Theorem 1.2 (The full jet-group divisor constraint).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_dvd_weighted_ambient`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_dvd_weighted_ambient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the exact full-group count with the stabilizer divisor constraint gives |G(q)| dividing (p^n−1)p^(n(p−2)+n²)(p^n−1)n. The result is intended for subsequent orbit-size and exceptional-symmetry arguments.

**Theorem 1.3 (Primitive-coordinate rigidity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.labelGroup_subsingleton_of_primitive_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.labelGroup_subsingleton_of_primitive_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n≥3, A(0)=1, and A(1) generates Kˣ by powers, the weight-one equation kills the scalar part of every stabilizing label. The second coordinate then fixes a generator, hence the entire field automorphism; the label formula makes every actual label the identity.

**Theorem 1.4 (Exact order on the primitive stratum).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_of_primitive_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_of_primitive_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trivial label stabilizer removes the label factor from the full count, yielding |G(q)|=(p^n−1)p^(n(p−2)+n²). This is the exact generic group order supplied by the weighted action.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.labelGroup_subsingleton_of_primitive_coordinates`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_dvd_weighted_ambient`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.full_cardinality_of_primitive_coordinates`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic.labelGroup_card_dvd_weighted_ambient`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup](OddPrimeJetGroup.md)
