# The square spiral by shells

## Abstract

Every positive index of the reflected square spiral belongs to its computed shell and side.

Reflect the horizontal coordinate of the Irwin walk to start east, north, west and south in the source coordinates. The origin has label zero. Each positive shell comprises four half-open sides, with each corner assigned to one side.

**Definition 1.1 (A position on a shell).**

$$\forall (r : \mathbb{Z}), \forall (d : \mathbb{Z}), \operatorname{shellPoint}\left(r, d\right) = (if d < 2 \cdot r then (r, d - r + 1) else (if d < 4 \cdot r then (3 \cdot r - 1 - d, r) else (if d < 6 \cdot r then (-r, 5 \cdot r - 1 - d) else (d - 7 \cdot r + 1, -r))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.shellPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

The four clauses run up the right edge, left along the top, down the left edge and right along the bottom.

**Definition 1.2 (The source spiral walk).**

$$\forall (n : \mathbb{N}), \operatorname{spiral}\left(n\right) = (-(\operatorname{walk}\left(n\right)).cell.1, (\operatorname{walk}\left(n\right)).cell.2)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.spiral` (`✓ std3`).

*Citation.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

Use the cell of the original Irwin walk at the given index and reverse its horizontal coordinate.

**Theorem 1.3 (Shell and side of a positive index).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\exists (k : \mathbb{N}), \exists (d : \mathbb{N}), (n = (2 \cdot k + 1) \cdot (2 \cdot k + 1) + d) \land ((d < 8 \cdot (k + 1)) \land (\operatorname{spiral}\left(n\right) = \operatorname{shellPoint}\left((k : \mathbb{Z}) + 1, (d : \mathbb{Z})\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.spiral_shells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

The first label of shell k+1 is the odd square (2k+1) squared. The next start is greater by 8(k+1). Irwin’s two-leg layer lemma gives the cells on the four sides after reflection.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.shellPoint`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.spiral`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/SquareSpiralShells.spiral_shells`
- Dependency: [D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum](IrwinA138099HookSum.md)
