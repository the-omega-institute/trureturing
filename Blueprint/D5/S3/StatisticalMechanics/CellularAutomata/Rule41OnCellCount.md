# ON cells of the Rule 41 cellular automaton

## Abstract

The elementary cellular automaton with Wolfram rule 41, started from a single ON cell at the origin and updated at every cell of the integers, has 1, 8k, 2 and 8k + 3 ON cells among the cells -n, ..., n of row n = 4k, 4k + 1, 4k + 2 and 4k + 3; the counts therefore satisfy Colin Barker's conjectured recurrence a(n) = a(n - 2) + a(n - 4) - a(n - 6) for n > 5 and generating function (1 + x^2 + 3x^3 - 2x^4 + 5x^5) / ((1 - x)^2 (1 + x)^2 (1 + x^2)) for OEIS A266614.

**Definition 1.1 (Rule 41).**

$$\operatorname{rule41}\left(l, c, r\right) = \operatorname{testBit}\left(41, 4 \cdot \operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{toNat}\left(c\right) + \operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.rule41` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266614, ON cells of the Rule 41 elementary cellular automaton: recurrence and generating-function conjectures*. URL: <https://oeis.org/A266614>.

*Commentary.*

The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 41, the Wolfram numbering; toNat sends false and true to 0 and 1.

**Definition 1.2 (The sequence A266614).**

$$\operatorname{onCount}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(x \mapsto \operatorname{row}\left(\operatorname{rule41}, n, x\right) = \operatorname{true}, \operatorname{Icc}\left(-(n: \mathbb{Z}), (n: \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.onCount` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266614, ON cells of the Rule 41 elementary cellular automaton: recurrence and generating-function conjectures*. URL: <https://oeis.org/A266614>.

*Commentary.*

A266614, the number of ON (black) cells in the n-th iteration: the cells x of row n with -n ≤ x ≤ n that are ON, with n cast to the integers. The rows are the frozen single-seed evolution row g of RuleThirtyTwentyTwoMersenneSignRefutation with g = rule41: row g 0 x is true exactly for x = 0, and row g (m + 1) x = g (row g m (x - 1)) (row g m x) (row g m (x + 1)) for every integer x, so every cell of the integers is updated at every step and cells far from the origin follow the background, which alternates because 000 goes to 1 and 111 goes to 0 under rule 41.

**Definition 1.3 (The conjectures of Barker).**

$$claim \Leftrightarrow (\left(\forall n \in \mathbb{N},\; 5 < n \Rightarrow ((\operatorname{onCount}\left(n\right): \mathbb{Z}) = (\operatorname{onCount}\left(n - 2\right): \mathbb{Z}) + (\operatorname{onCount}\left(n - 4\right): \mathbb{Z}) - (\operatorname{onCount}\left(n - 6\right): \mathbb{Z}))\right) \land \operatorname{mk}\left(n \mapsto (\operatorname{onCount}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)^{2}(1 + X)^{2}(1 + X^{2})) = 1 + X^{2} + 3 \cdot X^{3} - 2 \cdot X^{4} + 5 \cdot X^{5})$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.claim` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A266614, ON cells of the Rule 41 elementary cellular automaton: recurrence and generating-function conjectures*. URL: <https://oeis.org/A266614>.

*Commentary.*

Barker's recurrence for n > 5 and his generating function, read in the integers, with the generating function stated as the product of the series with its denominator, which has constant term 1.

**Theorem 1.4 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a266614-rule41-barker` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a266614-rule41-barker","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2016). *OEIS A266614, ON cells of the Rule 41 elementary cellular automaton: recurrence and generating-function conjectures*. URL: <https://oeis.org/A266614>.

*Commentary.*

By induction on n, the background of row n is OFF for even n and ON for odd n, and row n differs from it exactly at {n}, {n - 2, n - 1, n}, {n - 2, n} or {n - 4, n - 3, n - 1, n} according as n is 0, 1, 2 or 3 mod 4. Rule 41 sends lcr to 1 exactly for 000, 011 and 101. From phase 0, 000 switches the background ON and the neighbourhoods 001, 010 and 100 around the ON cell n turn the cells n - 1, n and n + 1 OFF. From phase 1, 111 switches the background OFF, and around the OFF cells n - 2, n - 1, n only 000 at n - 1 and 011 at n + 1 turn ON. From phase 2, 000 switches the background ON; around the ON cells n - 2 and n the neighbourhoods 001, 010, 010 and 100 turn the cells n - 3, n - 2, n and n + 1 OFF, while 101 keeps n - 1 ON. From phase 3, 111 switches the background OFF, and around the OFF cells n - 4, n - 3, n - 1, n only 011 at n + 1 turns ON. All the exceptional cells lie in the window, so the counts are 1, 2n - 2 = 8k, 2 and 2n - 3 = 8k + 3 for n = 4k, 4k + 1, 4k + 2, 4k + 3. The recurrence follows phase by phase, and comparing coefficients, it makes every coefficient of the product with (1 - x)^2 (1 + x)^2 (1 + x^2) = 1 - x^2 - x^4 + x^6 vanish from x^6 on, while the first six coefficients come from the values 1, 0, 2, 3, 1, 8.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.onCount`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.rule41`
- Dependency: [D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation](../../../S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.md)
