# ON cells of the Rule 79 cellular automaton

## Abstract

The elementary cellular automaton with Wolfram rule 79, started from a single ON cell at the origin and updated at every cell of the integers, has n + 1 ON cells among the cells -n, ..., n of row 2n and 3n + 2 of them in row 2n + 1, as conjectured by Ctibor O. Zizka for OEIS A266981; the counts therefore satisfy Colin Barker's closed form (3 + (-1)^n - 2 (-2 + (-1)^n) n) / 4, his recurrence a(n) = 2 a(n - 2) - a(n - 4) for n > 3 and his generating function (1 + 2x + x^3) / ((1 - x)^2 (1 + x)^2).

**Definition 1.1 (Rule 79).**

$$\operatorname{rule79}\left(l, c, r\right) = \operatorname{testBit}\left(79, 4 \cdot \operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{toNat}\left(c\right) + \operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.rule79` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266981>.

*Commentary.*

The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 79, the Wolfram numbering; toNat sends false and true to 0 and 1.

**Definition 1.2 (Rows from a single ON cell).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Z},\; \operatorname{cell}\left(0, x\right) = \operatorname{decide}\left(x = 0\right) \land \operatorname{cell}\left(n + 1, x\right) = \operatorname{rule79}\left(\operatorname{cell}\left(n, x - 1\right), \operatorname{cell}\left(n, x\right), \operatorname{cell}\left(n, x + 1\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.cell` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266981>.

*Commentary.*

Row 0 has exactly the cell at the origin ON, and every cell of the integers is updated from its three neighbours at every step, so cells far from the origin follow the background, which alternates because 000 goes to 1 and 111 goes to 0 under rule 79.

**Definition 1.3 (The sequence A266981).**

$$\operatorname{onCount}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(x \mapsto \operatorname{cell}\left(n, x\right) = \operatorname{true}, \operatorname{Icc}\left(-(n: \mathbb{Z}), (n: \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.onCount` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266981>.

*Commentary.*

A266981, the number of ON (black) cells in the n-th iteration: the cells x of row n with -n ≤ x ≤ n that are ON, with n cast to the integers.

**Definition 1.4 (The conjectures of Barker and Zizka).**

$$claim \Leftrightarrow (\left(\forall n \in \mathbb{N},\; (\operatorname{onCount}\left(n\right): \mathbb{Q}) = \frac{3 + (-1)^{n} - 2 \cdot (-2 + (-1)^{n}) \cdot n}{4}\right) \land \left(\left(\forall n \in \mathbb{N},\; 3 < n \Rightarrow ((\operatorname{onCount}\left(n\right): \mathbb{Z}) = 2 \cdot (\operatorname{onCount}\left(n - 2\right): \mathbb{Z}) - (\operatorname{onCount}\left(n - 4\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{onCount}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)^{2}(1 + X)^{2}) = 1 + 2 \cdot X + X^{3} \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{onCount}\left(2 \cdot n\right) = n + 1\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{onCount}\left(2 \cdot n + 1\right) = 3 \cdot n + 2\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.claim` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266981>.

*Commentary.*

Barker's closed form, read in the rationals; his recurrence for n > 3 and his generating function, read in the integers, with the generating function stated as the product of the series with its denominator, which has constant term 1; and Zizka's formulas for even and odd indices.

**Theorem 1.5 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a266981-rule79-barker-zizka` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a266981-rule79-barker-zizka","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2016). *OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266981>.

*Commentary.*

By induction on n, row 2k is ON exactly at the even x with 0 ≤ x ≤ 2k, and row 2k + 1 is OFF exactly at the odd x with 1 ≤ x ≤ 2k + 1. Rule 79 sends lcr to 1 exactly when l = 0, or c = 1 and r = 0. From row 2k, a cell whose left neighbour is one of the ON cells 0, 2, ..., 2k is itself OFF, so it turns OFF, which covers the odd x from 1 to 2k + 1; every other cell has an OFF left neighbour, so it turns ON. From row 2k + 1, a cell whose left neighbour is one of the OFF cells 1, 3, ..., 2k + 1 turns ON, which covers the even x from 2 to 2k + 2; a cell with an ON left neighbour turns ON only if it is ON and its right neighbour is OFF, which happens exactly at the even x from 0 to 2k, and every other cell turns OFF. Counting, the window of row 2k holds the k + 1 even cells from 0 to 2k, and the window of row 2k + 1, which has 4k + 3 cells, holds k + 1 OFF cells. The closed form follows by parity, the recurrence by parity of n - 4, and comparing coefficients, the recurrence makes every coefficient of the product with (1 - x)^2 (1 + x)^2 = 1 - 2x^2 + x^4 vanish from x^4 on, while the first four coefficients come from the values 1, 2, 2, 5.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.cell`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.onCount`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.rule79`
