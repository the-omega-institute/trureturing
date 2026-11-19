# A larger envelope for actual algebraic values

## Abstract

Actual singular algebraic value pairs have a uniform subpower count with coordinates up to the original prime.

**Theorem 1.1 (Count actual value pairs without the former cubic coordinate cutoff).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope.actual_fixed_factor_value_pairs_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope.actual_fixed_factor_value_pairs_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, one positive constant C works for all primes p>=18, actual integer anchors, baselines and finite ordered endpoint sets with every coordinate bounded by p. Choose an occurring endpoint pair whose actual pencil is nonzero, and a primitive integer factor F of that pencil irreducible over the rationals. If F has the original modular root and the two baseline product factors are units at that root, then the finite image of actual scaled algebraic value pairs associated to F has at most C*p^epsilon elements.

Use the real height parameter T=p squared while retaining p for modular relevance. The literal pencil coefficients are bounded by 18p cubed, hence by T squared for p>=18. The existing integer cubic factor inequality gives coefficients of F at most T cubed. Every baseline coefficient is at most T squared and every actual coordinate is at most T. Apply the existing field-uniform value-pair envelope with exponent epsilon/2; T^(epsilon/2)=p^epsilon. The constant remains uniform over all number fields of degree at most three. No new number-field divisor estimate is introduced.

This expands the permitted coordinate envelope beyond the former condition 18J1 cubed<=p squared. It counts genuine algebraic value pairs; common-factor covers and the physical multiplicity of actual integer endpoints must still be proved by their respective counting modules. It does not assert a full arbitrary-modulus conjecture or establish literature priority.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope.actual_fixed_factor_value_pairs_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners](PascadiOriginalSingularPartners.md)
