# Actual Zeckendorf Prefix Cylinders

## Abstract

Actual padded Nat.zeckendorf prefix values and the forward canonical seam splice.

**Theorem 1.1 (The literal prefix value has exactly its prescribed digits).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every length m and internally nonadjacent binary prefix w, the canonical Zeckendorf digits of its Fibonacci value agree with w below m and vanish at every index above. The proof builds a finitely supported raw digit string, proves it canonical from internal nonadjacency, computes its Fibonacci value, and applies Mathlib's uniqueness.

This establishes the exact zero-tail digits of the prefix value. The inverse seam split, occupied-index coordinate identity, literal real-cutoff count, density, and extension ratio remain open.

**Theorem 1.2 (A shifted canonical tail preserves the actual prefix).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every internally nonadjacent binary prefix w and every natural tail t, the actual Zeckendorf digits of the literal sum of the prefix value and the seam-adjusted iterated substitution start agree with w. The proof uses the existing digit-shift theorem, proves the cross-seam gap, joins the canonical occupied-index lists, and applies uniqueness.

This is the forward inclusion in source 116.4. It does not prove the inverse, bijection, coordinate identity, or 116.5 count and density.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift`
- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits`
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](../GoldenBase4AutomataOracle.md)
- Dependency: [D5/S1/Digit/Raw](../Raw.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](../../Words/Powers/GoldenDesubstitutionZeckendorf.md)
