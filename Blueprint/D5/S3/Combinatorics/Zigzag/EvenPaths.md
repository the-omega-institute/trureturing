# Even Balanced-Choice Correspondence

## Abstract

Every balanced choice with even parameter has a unique signed zero-charge path, including its antipodal terminal pair.

**Theorem 1.1 (Reflection negates the even path charge).**

Lean statement: `D5/S3/Combinatorics/Zigzag/EvenPaths.evenPathReflection_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/EvenPaths.evenPathReflection_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reflection changes every start, transition, and antipodal terminal to its explicitly labelled opposite-sector partner. It negates the accumulated integer charge, yielding an equivalence of the two zero-charge path sets while preserving labelled multiplicity.

**Definition 1.2 (Balanced even choices are exactly zero-charge paths).**

Lean statement: `D5/S3/Combinatorics/Zigzag/EvenPaths.evenBalancedChoicesEquiv`

*Formalization.* `D5/S3/Combinatorics/Zigzag/EvenPaths.evenBalancedChoicesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r>=1, this is an equivalence from literal balanced Choices (2r) to the disjoint union of positive and negative EvenPaths with 3r-3 interior steps and charge zero. Its surjectivity proof decodes arbitrary choice labels using retired-vertex zero flow and the exhaustive transition table; the even terminal labels are forced at the antipode. At the remaining semitone vertex, balance forces charge zero. Injectivity is supplied by DecodedBalance.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/EvenPaths.evenBalancedChoicesEquiv`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/EvenPaths.evenPathReflection_charge`
- Dependency: [D5/S3/Combinatorics/Zigzag/DecodedBalance](DecodedBalance.md)
