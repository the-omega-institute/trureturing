# Centre column, rows and ON cells of the Rule 54 cellular automaton

## Abstract

The elementary cellular automaton with Wolfram rule 54, started from a single ON cell at the origin, has its centre column (OEIS A259661), its rows read as decimal digits (A118109) and its running total of ON cells (A265225) satisfying the recurrences and generating functions conjectured by Colin Barker, the floor formula conjectured by Karl V. Keller, Jr. for A118109, and the closed forms conjectured by Barker and by Wesley Ivan Hurt for A265225. Rule 54 is the elementary rule behind the interacting integrable reversible cellular automaton of Bobenko, Bordemann, Gunn and Pinkall, here applied to every cell at once.

**Definition 1.1 (Rule 54).**

$$\operatorname{rule54}\left(l, c, r\right) = \operatorname{testBit}\left(54, 4 \cdot \operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{toNat}\left(c\right) + \operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.rule54` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 54, the Wolfram numbering; toNat sends false and true to 0 and 1.

**Definition 1.2 (Rows from a single ON cell).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Z},\; \operatorname{cell}\left(0, x\right) = \operatorname{decide}\left(x = 0\right) \land \operatorname{cell}\left(n + 1, x\right) = \operatorname{rule54}\left(\operatorname{cell}\left(n, x - 1\right), \operatorname{cell}\left(n, x\right), \operatorname{cell}\left(n, x + 1\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.cell` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

Row 0 has exactly the cell at the origin ON, and every cell of the integers is updated from its three neighbours at every step; since 000 goes to 0 the cells far from the origin stay OFF.

**Definition 1.3 (The sequence A259661).**

$$\operatorname{centreColumn}\left(n\right) = \sum_{k\in\operatorname{range}\left(n + 1\right)} \operatorname{toNat}\left(\operatorname{cell}\left(k, 0\right)\right) \cdot 10^{n - k}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.centreColumn` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

The centre cells of rows 0, ..., n are read as decimal digits, row 0 most significant: the binary representation of the middle column.

**Definition 1.4 (The sequence A118109).**

$$\operatorname{binaryRow}\left(n\right) = \sum_{j\in\operatorname{range}\left(2 \cdot n + 1\right)} \operatorname{toNat}\left(\operatorname{cell}\left(n, (n: \mathbb{Z}) - (j: \mathbb{Z})\right)\right) \cdot 10^{j}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.binaryRow` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

The cells -n, ..., n of row n are read as decimal digits, the cell at -n most significant: the binary representation of the n-th iteration, with n and j cast to the integers.

**Definition 1.5 (The sequence A265225).**

$$\operatorname{totalOn}\left(n\right) = \sum_{k\in\operatorname{range}\left(n + 1\right)} \left|\{x\in\mathbb{Z} \mid \operatorname{cell}\left(k, x\right) = \operatorname{true}\}\right|$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.totalOn` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

The number of ON cells of rows 0, ..., n together; each row has finitely many ON cells, and the count of a set of integers is its cardinality (Set.ncard).

**Definition 1.6 (The conjectures of Barker, Keller and Hurt).**

$$claim \Leftrightarrow (\left(\forall n \in \mathbb{N},\; 3 < n \Rightarrow ((\operatorname{centreColumn}\left(n\right): \mathbb{Z}) = 11 \cdot (\operatorname{centreColumn}\left(n - 1\right): \mathbb{Z}) - 11 \cdot (\operatorname{centreColumn}\left(n - 2\right): \mathbb{Z}) + 11 \cdot (\operatorname{centreColumn}\left(n - 3\right): \mathbb{Z}) - 10 \cdot (\operatorname{centreColumn}\left(n - 4\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{centreColumn}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)(1 - 10 \cdot X)(1 + X^{2})) = 1 \land \left(\left(\forall n \in \mathbb{N},\; 3 < n \Rightarrow ((\operatorname{binaryRow}\left(n\right): \mathbb{Z}) = 10001 \cdot (\operatorname{binaryRow}\left(n - 2\right): \mathbb{Z}) - 10000 \cdot (\operatorname{binaryRow}\left(n - 4\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{binaryRow}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)(1 + X)(1 - 100 \cdot X)(1 + 100 \cdot X)) = 1 + 111 \cdot X \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{binaryRow}\left(n\right) = (10000 + 1100 \cdot (n \operatorname{mod} 2)) \cdot 100^{n} \operatorname{div} 9999\right) \land \left(\left(\forall n \in \mathbb{N},\; (\operatorname{totalOn}\left(n\right): \mathbb{Q}) = \frac{(n + 1) \cdot (2 \cdot n - (-1)^{n} + 5)}{4}\right) \land \left(\left(\forall n \in \mathbb{N},\; 4 < n \Rightarrow ((\operatorname{totalOn}\left(n\right): \mathbb{Z}) = (\operatorname{totalOn}\left(n - 1\right): \mathbb{Z}) + 2 \cdot (\operatorname{totalOn}\left(n - 2\right): \mathbb{Z}) - 2 \cdot (\operatorname{totalOn}\left(n - 3\right): \mathbb{Z}) - (\operatorname{totalOn}\left(n - 4\right): \mathbb{Z}) + (\operatorname{totalOn}\left(n - 5\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{totalOn}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)^{3}(1 + X)^{2}) = 1 + 3 \cdot X \land \left(\forall n \in \mathbb{N},\; \operatorname{totalOn}\left(n\right) = n + 1 + (n + 1) \cdot ((n + 1) \operatorname{div} 2)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.claim` (`✓ std3`).

*Citation.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

Barker's recurrences and generating functions for the three sequences; Keller's floor formula for A118109, with natural-number division; Barker's closed form for A265225 read in the rationals and Hurt's closed form with natural-number division. Each denominator has constant term 1, so each generating function is stated as the product of the series with its denominator in the integer power series.

**Theorem 1.7 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a259661-rule54-barker-keller-hurt` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a259661-rule54-barker-keller-hurt","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price; Eric W. Weisstein (2015). *OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A259661>.

*Commentary.*

By induction on n, the cell at x of row n is ON exactly when |x| is at most n and x is congruent to n modulo 4 for even n, or x is not congruent to n + 1 modulo 4 for odd n: the rule table sends 100, 101, 001 and 010 to 1 and the other four neighbourhoods to 0. Hence the centre cell of row k is ON exactly when k is 0 or 1 modulo 4, so the centre column satisfies a(n+1) = 10 a(n) + c(n+1) with a period-4 digit c whose alternating sum over four consecutive steps vanishes, which gives its recurrence. The same invariant shows that digit j + 4 of row n + 2 equals digit j of row n and that the first four digits of row n + 2 are 1, 0, 0, 0 for even n and 1, 1, 1, 0 for odd n; reading the digits in base b, the value of row n + 2 is 1 or 1 + b + b^2 plus b^4 times the value of row n. For b = 10 this gives 9999 a(n) = 10000 * 100^n - 1 for even n and 11100 * 100^n - 111 for odd n, hence Keller's floor formula and Barker's recurrence for A118109. Every ON cell of row k lies in [-k, k], so with b = 1 the ON cells of row k number k/2 + 1 for even k and 3(k + 1)/2 for odd k; summing gives Hurt's formula, which equals Barker's closed form, and each is annihilated by (1 - x)^3 (1 + x)^2. The generating functions follow by comparing coefficients: from x^5 on they vanish by the recurrences, and the first five come from the values 1, 11, 110, 1100, 11001; 1, 111, 10001, 1110111, 100010001; and 1, 4, 6, 12, 15.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.binaryRow`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.cell`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.centreColumn`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.rule54`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.totalOn`
