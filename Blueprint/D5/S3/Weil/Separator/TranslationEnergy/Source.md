# Canonical translation partition

## Abstract

Canonical translation partition.

**Theorem 1.1 (A mesh bound after inserting breakpoints).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Source.cellAt_gap_le_mesh`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Source.cellAt_gap_le_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural radius R, a rational shift s, and a natural depth d, the source points are the sorted distinct union of a relative dyadic mesh and the ten original and translated cutoff breakpoints. The support hull runs from min(-2R,s-2R) to max(2R,s+2R).

If cellAt returns adjacent endpoints a and b, then a<b, both endpoints lie in the support hull, and b-a is at most the hull length divided by 2^d. If a gap were larger, the next mesh point obtained by a floor operation would lie strictly inside that gap, contradicting adjacency.

The first and last points are the hull endpoints. The sourceCells list contains exactly the adjacent pairs, with one fewer cell than source points, and its list indices agree with cellAt.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Source.cellAt_gap_le_mesh`
