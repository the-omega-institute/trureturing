# The four-lag recurrence for OEIS A395348

## Abstract

The literal alternating spiral-queens play exists uniquely and satisfies the four-lag recurrence.

The Black label at sequence index n is the chronological label at turn 2n. Red moves at odd turns.

**Definition 1.1 (Queen lines).**

$$\forall (q : (\mathbb{Z} \times \mathbb{Z})), \forall (p : (\mathbb{Z} \times \mathbb{Z})), (\operatorname{Attacks}\left(q, p\right)) \Leftrightarrow ((q.1 = p.1) \lor ((q.2 = p.2) \lor ((q.1 + q.2 = p.1 + p.2) \lor (q.1 - q.2 = p.1 - p.2))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.Attacks` (`✓ std3`).

*Citation.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

A queen attacks along either coordinate axis and along each of the two diagonal projections.

**Definition 1.2 (Legal labels).**

$$\forall (f : \mathbb{N} \to \mathbb{N}), \forall (t : \mathbb{N}), \forall (n : \mathbb{N}), (\operatorname{SpiralLegal}\left(f, t, n\right)) \Leftrightarrow (\forall (j : \mathbb{N}), (j < t) \Rightarrow ((f\left(j\right) \neq n) \land (((j : \mathbb{Z}) \bmod 2 \neq (t : \mathbb{Z}) \bmod 2) \Rightarrow (\neg (\operatorname{Attacks}\left(\operatorname{spiral}\left(f\left(j\right)\right), \operatorname{spiral}\left(n\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.SpiralLegal` (`✓ std3`).

*Citation.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

Every earlier turn forbids overlap. The row, column and diagonal tests apply to earlier turns of the other parity.

**Definition 1.3 (Least legal label).**

$$\forall (f : \mathbb{N} \to \mathbb{N}), (\operatorname{SpiralGreedy}\left(f\right)) \Leftrightarrow (\forall (t : \mathbb{N}), (\operatorname{SpiralLegal}\left(f, t, f\left(t\right)\right)) \land (\forall (n : \mathbb{N}), (n < f\left(t\right)) \Rightarrow (\neg (\operatorname{SpiralLegal}\left(f, t, n\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.SpiralGreedy` (`✓ std3`).

*Citation.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

At every turn the chosen label is legal and all smaller natural labels are illegal.

**Theorem 1.4 (Existence, uniqueness and the four-lag recurrence).**

$$(\operatorname{ExistsUnique}\left(((f : \mathbb{N} \to \mathbb{N}) \mapsto \operatorname{SpiralGreedy}\left(f\right))\right)) \land (\forall (f : \mathbb{N} \to \mathbb{N}), (\operatorname{SpiralGreedy}\left(f\right)) \Rightarrow (\forall (n : \mathbb{N}), (2 \le n) \Rightarrow (f\left(2 \cdot (n + 4)\right) = f\left(2 \cdot n\right) + 8 \cdot n + 34)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.a395348_four_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jonas Karlsson and N. J. A. Sloane (2026). *OEIS A395348 and Rahid Zaman’s spiral-queens recurrence*. URL: <https://oeis.org/A395348>.

*Commentary.*

The opening proof checks all fourteen turns inside a radius-four box. From shell five onward, the earlier opposing rows, columns and two diagonal projections exclude smaller labels on each of the four turns. Two shells preserve parity. The two Black slots give increments 16r+10 and 16r+18, with the n=2 case coming from the opening. The lower bound is necessary because in the unique least-label play a(0)=0 and a(4)=38, whereas the claimed increment would give 34. Also a(1)=2 and a(5)=52, whereas the claimed increment would give 44.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.Attacks`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.SpiralGreedy`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.SpiralLegal`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/OeisA395348FourLag.a395348_four_lag`
- Dependency: [D5/S3/Combinatorics/Polyomino/SquareSpiralShells](SquareSpiralShells.md)
