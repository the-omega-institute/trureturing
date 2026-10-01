# Canonical Prefix Count

## Abstract

The connected source matchings reduce to canonical prefix pairs, whose finite fibers give the polynomial count.

**Theorem 1.1 (Count canonical pairs).**

Lean statement: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

The canonical prefix pairs split into finite families whose cardinalities can be counted directly.

**Theorem 1.2 (Polynomial arithmetic).**

Lean statement: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_count_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_count_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

The canonical family count simplifies to the second-diagonal polynomial after substituting n minus four.

## References

- Truth anchor: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_card`
- Truth anchor: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.canonical_count_arithmetic`
- Dependency: [D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage4](Stage4.md)
