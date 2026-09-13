# Square Positions and Values in a Square-Counting Recurrence

## Abstract

The square positions and square values in Zumkeller's recurrence follow a nine-term pattern.

**Definition 1.1 (Zumkeller's square-counting recurrence).**

$$(\operatorname{a}\left(1\right) = 1) \land (\forall j \in \mathbb{N},\; \operatorname{a}\left(j + 2\right) = \operatorname{a}\left(j + 1\right) + \operatorname{card}\left(\operatorname{filter}\left(\operatorname{Icc}\left(1, j + 1\right), (k \mapsto \operatorname{IsSquare}\left(\operatorname{a}\left(k\right)\right))\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.a` (`✓ std3`).

*Citation.* Reinhard Zumkeller; Vladeta Jovovic (2004). *OEIS A097602, a(n+1) = a(n) + number of squares so far; a(1) = 1*. URL: <https://oeis.org/A097602>.

*Commentary.*

The source recurrence begins at index one. The Lean body assigns a(0)=0 only as a sentinel outside the source. Its strong-recursive filter carries the guard k<j+2; every k in Icc(1,j+1) satisfies this guard.

**Theorem 1.2 (Jovovic's square-position assertion).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{IsSquare}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow (n \bmod 9 = 1 \lor n \bmod 9 = 4))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.jovovic_a097602_positions` (`✓ std3`). ∎

*Citation.* Reinhard Zumkeller; Vladeta Jovovic (2004). *OEIS A097602, a(n+1) = a(n) + number of squares so far; a(1) = 1*. URL: <https://oeis.org/A097602>.

*Commentary.*

For every positive index, the corresponding term is a square exactly when the index is congruent to one or four modulo nine. The nine-term block pattern separates every other term strictly between consecutive squares.

**Theorem 1.3 (Zumkeller's square-value conjecture).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow ((\exists n \in \mathbb{N},\; 1 \le n \land \operatorname{a}\left(n\right) = m^{2}) \Leftrightarrow m \bmod 3 \ne 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.zumkeller_a097602` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a097602-square-counting-recurrence-square-values` (proved) by `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.zumkeller_a097602`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a097602-square-counting-recurrence-square-values","declaration_gid":"D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.zumkeller_a097602","resolution_kind":"proved"} -->

*Citation.* Reinhard Zumkeller; Vladeta Jovovic (2004). *OEIS A097602, a(n+1) = a(n) + number of squares so far; a(1) = 1*. URL: <https://oeis.org/A097602>.

*Commentary.*

For every positive root m, its square occurs as a sequence value exactly when m is not divisible by three. The two square positions in each block carry the roots 3k+1 and 3k+2.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.jovovic_a097602_positions`
- Truth anchor: `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.zumkeller_a097602`
