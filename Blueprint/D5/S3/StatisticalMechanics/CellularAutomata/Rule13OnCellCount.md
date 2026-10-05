# ON cells of the Rule 13 cellular automaton

## Abstract

The elementary cellular automaton with Wolfram rule 13, started from a single ON cell at the origin and updated at every cell of the integers, has n + 1 ON cells among the cells -2n, ..., 2n of row 2n and 3n + 1 ON cells among the cells -(2n + 1), ..., 2n + 1 of row 2n + 1, as conjectured by Ctibor O. Zizka for OEIS A266285; the counts therefore satisfy Colin Barker's closed form ((-1)^n (3 - 2n) + 4n + 1) / 4, his recurrence a(n) = 2 a(n - 2) - a(n - 4) for n > 3 and his generating function (1 + x + 2x^3) / ((1 - x)^2 (1 + x)^2).

**Definition 1.1 (Rule 13).**

$$\operatorname{rule13}\left(l, c, r\right) = \operatorname{testBit}\left(13, 4 \cdot \operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{toNat}\left(c\right) + \operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.rule13` (`✓ std3`).

*Citation.* Robert Price (2015). *OEIS A266285, ON cells of the Rule 13 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266285>.

*Commentary.*

The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 13, the Wolfram numbering; toNat sends false and true to 0 and 1.

**Definition 1.2 (The sequence A266285).**

$$\operatorname{onCount}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(x \mapsto \operatorname{row}\left(\operatorname{rule13}, n, x\right) = \operatorname{true}, \operatorname{Icc}\left(-(n: \mathbb{Z}), (n: \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.onCount` (`✓ std3`).

*Citation.* Robert Price (2015). *OEIS A266285, ON cells of the Rule 13 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266285>.

*Commentary.*

A266285, the number of ON (black) cells in the n-th iteration: the cells x of row n with -n ≤ x ≤ n that are ON, with n cast to the integers. The rows are the frozen single-seed evolution row g of RuleThirtyTwentyTwoMersenneSignRefutation with g = rule13: row g 0 x is true exactly for x = 0, and row g (m + 1) x = g (row g m (x - 1)) (row g m x) (row g m (x + 1)) for every integer x, so every cell of the integers is updated at every step and cells far from the origin follow the background, which alternates because 000 goes to 1 and 111 goes to 0 under rule 13.

**Definition 1.3 (The conjectures of Barker and Zizka).**

$$claim \Leftrightarrow (\left(\forall n \in \mathbb{N},\; (\operatorname{onCount}\left(n\right): \mathbb{Q}) = \frac{(-1)^{n} \cdot (3 - 2 \cdot n) + 4 \cdot n + 1}{4}\right) \land \left(\left(\forall n \in \mathbb{N},\; 3 < n \Rightarrow ((\operatorname{onCount}\left(n\right): \mathbb{Z}) = 2 \cdot (\operatorname{onCount}\left(n - 2\right): \mathbb{Z}) - (\operatorname{onCount}\left(n - 4\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{onCount}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)^{2}(1 + X)^{2}) = 1 + X + 2 \cdot X^{3} \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{onCount}\left(2 \cdot n\right) = n + 1\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{onCount}\left(2 \cdot n + 1\right) = 3 \cdot n + 1\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.claim` (`✓ std3`).

*Citation.* Robert Price (2015). *OEIS A266285, ON cells of the Rule 13 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266285>.

*Commentary.*

Barker's closed form, read in the rationals; his recurrence for n > 3 and his generating function, read in the integers, with the generating function stated as the product of the series with its denominator, which has constant term 1; and Zizka's formulas for even and odd indices.

**Theorem 1.4 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a266285-rule13-barker-zizka` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a266285-rule13-barker-zizka","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2015). *OEIS A266285, ON cells of the Rule 13 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures*. URL: <https://oeis.org/A266285>.

*Commentary.*

By induction on n, row 2k is ON exactly at the even x with 0 ≤ x ≤ 2k, and row 2k + 1 is OFF exactly at the odd x with -1 ≤ x ≤ 2k + 1. Rule 13 sends lcr to 1 exactly when l = 0 and either c = 1 or r = 0. From row 2k, a cell whose left neighbour is one of the ON cells 0, 2, ..., 2k turns OFF, which covers the odd x from 1 to 2k + 1; the cell -1 has an OFF left neighbour, an OFF centre and the ON right neighbour 0, so it turns OFF; every other cell has an OFF left neighbour and either an ON centre or an OFF right neighbour, so it turns ON. From row 2k + 1, a cell can turn ON only if its left neighbour is one of the OFF cells -1, 1, ..., 2k + 1, that is, x is even with 0 ≤ x ≤ 2k + 2, and each such cell has an ON centre, so it turns ON. Counting, the window of row 2k holds the k + 1 even cells from 0 to 2k, and the window of row 2k + 1, which has 4k + 3 cells, holds k + 2 OFF cells. The closed form follows by parity, the recurrence by parity of n - 4, and comparing coefficients, the recurrence makes every coefficient of the product with (1 - x)^2 (1 + x)^2 = 1 - 2x^2 + x^4 vanish from x^4 on, while the first four coefficients come from the values 1, 1, 2, 4.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.onCount`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.rule13`
- Dependency: [D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation](../../../S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.md)
