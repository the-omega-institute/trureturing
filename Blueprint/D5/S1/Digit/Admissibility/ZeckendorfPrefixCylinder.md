# Actual Zeckendorf Prefix Cylinders

## Abstract

Canonical Zeckendorf prefix cylinders, their composition coordinates, and natural density.

**Theorem 1.1 (The literal prefix value has exactly its prescribed digits).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every length m and internally nonadjacent binary prefix w, the canonical Zeckendorf digits of its Fibonacci value agree with w below m and vanish at every index above. The proof builds a finitely supported raw digit string, proves it canonical from internal nonadjacency, computes its Fibonacci value, and applies Mathlib's uniqueness.

The zero-tail result supplies the low side of the canonical inverse split.

**Theorem 1.2 (A shifted canonical tail preserves the actual prefix).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every internally nonadjacent binary prefix w and every natural tail t, the actual Zeckendorf digits of the literal sum of the prefix value and the seam-adjusted iterated substitution start agree with w. The proof uses the existing digit-shift theorem, proves the cross-seam gap, joins the canonical occupied-index lists, and applies uniqueness.

This supplies forward inclusion for every actual canonical tail, including zero.

**Theorem 1.3 (Every actual prefix member has one ordered canonical tail).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_has_tail`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_has_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each legal prefix and every number satisfying its actual padded Zeckendorf digit predicate, the proof partitions occupied indices at the seam, excludes the forced adjacent bit, lowers the high indices to a canonical tail, and reconstructs the original number. The tail is unique and the parameter map is strictly increasing. The same digit partition proves the exact composition identity for the integer matrix [[0,1],[1,1]] and seed (-1,1).

**Theorem 1.4 (Literal prefix counts have density and compatible refinement ratios).**

Lean statement: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_real_cutoff_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_real_cutoff_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal prefix, the literal finite cardinality below each nonnegative real cutoff differs from the golden-ratio main term by a fixed-prefix constant. The proof bijects the counted numbers with their unique canonical tail parameters and sandwiches the count between two real thresholds using the existing substitution-start error window. It derives natural density and the ratio for every legal appended prefix, including the empty extension. The denominator is eventually positive because its density is positive.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_has_tail`
- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_of_shift`
- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixCylinder_real_cutoff_discrepancy`
- Truth anchor: `D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder.prefixValue_has_canonical_digits`
- Dependency: [D5/S1/Deficit/Displacement/GoldenSubstStartSharpness](../../Deficit/Displacement/GoldenSubstStartSharpness.md)
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](../GoldenBase4AutomataOracle.md)
- Dependency: [D5/S1/Digit/Raw](../Raw.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](../../Words/Powers/GoldenDesubstitutionZeckendorf.md)
