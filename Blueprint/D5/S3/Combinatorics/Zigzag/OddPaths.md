# Odd Balanced-Choice Correspondence

## Abstract

The odd central singleton has its own complete inverse, so the literal balance-only count is obtained in both parities.

**Theorem 1.1 (Reflection negates the odd path charge).**

Lean statement: `D5/S3/Combinatorics/Zigzag/OddPaths.oddPathReflection_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/OddPaths.oddPathReflection_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The opposite sector has different form labels at the central singleton as well as at the interior steps. The explicit reflection is an equivalence and sends the accumulated charge to its negative; therefore both signed zero-charge sectors have equal cardinality.

**Definition 1.2 (Balanced odd choices are exactly zero-charge paths).**

Lean statement: `D5/S3/Combinatorics/Zigzag/OddPaths.oddBalancedChoicesEquiv`

*Formalization.* `D5/S3/Combinatorics/Zigzag/OddPaths.oddBalancedChoicesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r>=1, balanced Choices (2r+1), where n=6r+3, are equivalent to the two signed OddPath sectors with 3r-1 interior steps and zero charge. Surjectivity classifies each low/high label pair of an arbitrary balanced choice, then separately classifies the singleton terminal. The final nonzero semitone balance equation forces charge zero; DecodedBalance gives injectivity. The odd case is not inferred from the even antipodal proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/OddPaths.oddBalancedChoicesEquiv`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/OddPaths.oddPathReflection_charge`
- Dependency: [D5/S3/Combinatorics/Zigzag/DecodedBalance](DecodedBalance.md)
