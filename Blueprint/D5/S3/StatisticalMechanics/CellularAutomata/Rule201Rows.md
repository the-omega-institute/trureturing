# Rows of the Rule 201 cellular automaton

## Abstract

The elementary cellular automaton with Wolfram rule 201, started from a single ON cell at the origin and updated at every cell of the integers, has row n read on the cells -n, ..., n equal to 2 * 4^n - (2 [n odd] + 5 [n > 0]) * 2^(n-1) - 1 in base 2, as conjectured by M. F. Hasler for OEIS A267681; both the base-2 reading (A267681) and the decimal-digit reading (A267680) satisfy the order-4 recurrences and generating functions conjectured by Colin Barker. Rule 201 is the local update rule of the Floquet-PXP cellular automaton, here applied to every cell at once.

**Definition 1.1 (Rule 201).**

$$\operatorname{rule201}\left(l, c, r\right) = \operatorname{testBit}\left(201, 4 \cdot \operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{toNat}\left(c\right) + \operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.rule201` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

The new state of a cell whose left neighbour, own state and right neighbour are l, c, r is bit 4l + 2c + r of 201, the Wolfram numbering; toNat sends false and true to 0 and 1.

**Definition 1.2 (Rows from a single ON cell).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Z},\; \operatorname{cell}\left(0, x\right) = \operatorname{decide}\left(x = 0\right) \land \operatorname{cell}\left(n + 1, x\right) = \operatorname{rule201}\left(\operatorname{cell}\left(n, x - 1\right), \operatorname{cell}\left(n, x\right), \operatorname{cell}\left(n, x + 1\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.cell` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

Row 0 has exactly the cell at the origin ON, and every cell of the integers is updated from its three neighbours at every step, so cells far from the origin follow the background: 000 goes to 1 under rule 201.

**Definition 1.3 (The window of row n).**

$$\operatorname{windowValue}\left(b, n\right) = \sum_{j\in\operatorname{range}\left(2 \cdot n + 1\right)} \operatorname{toNat}\left(\operatorname{cell}\left(n, (n: \mathbb{Z}) - (j: \mathbb{Z})\right)\right) \cdot b^{j}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.windowValue` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

The cells -n, ..., n of row n are read as digits in base b, the cell at -n most significant; the cell at n - j carries weight b^j, with n and j cast to the integers.

**Definition 1.4 (The sequence A267681).**

$$\operatorname{decimalRepresentation}\left(n\right) = \operatorname{windowValue}\left(2, n\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.decimalRepresentation` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

A267681, the decimal representation of the n-th iteration: the window read as a binary number.

**Definition 1.5 (The sequence A267680).**

$$\operatorname{binaryRepresentation}\left(n\right) = \operatorname{windowValue}\left(10, n\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.binaryRepresentation` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

A267680, the binary representation of the n-th iteration: the window read as a string of decimal digits.

**Definition 1.6 (The conjectures of Barker and Hasler).**

$$claim \Leftrightarrow (\left(\forall n \in \mathbb{N},\; (\operatorname{decimalRepresentation}\left(n\right): \mathbb{Z}) = 2 \cdot 4^{n} - ((n \operatorname{mod} 2: \mathbb{Z}) \cdot 2 + [0 < n] \cdot 5) \cdot 2^{n - 1} - 1\right) \land \left(\left(\forall n \in \mathbb{N},\; 4 < n \Rightarrow ((\operatorname{decimalRepresentation}\left(n\right): \mathbb{Z}) = 5 \cdot (\operatorname{decimalRepresentation}\left(n - 1\right): \mathbb{Z}) - 20 \cdot (\operatorname{decimalRepresentation}\left(n - 3\right): \mathbb{Z}) + 16 \cdot (\operatorname{decimalRepresentation}\left(n - 4\right): \mathbb{Z}))\right) \land \left(\operatorname{mk}\left(n \mapsto (\operatorname{decimalRepresentation}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)(1 - 2 \cdot X)(1 + 2 \cdot X)(1 - 4 \cdot X)) = 1 - 5 \cdot X + 21 \cdot X^{2} + 14 \cdot X^{3} - 40 \cdot X^{4} \land \left(\left(\forall n \in \mathbb{N},\; 4 < n \Rightarrow ((\operatorname{binaryRepresentation}\left(n\right): \mathbb{Z}) = 101 \cdot (\operatorname{binaryRepresentation}\left(n - 1\right): \mathbb{Z}) - 10100 \cdot (\operatorname{binaryRepresentation}\left(n - 3\right): \mathbb{Z}) + 10000 \cdot (\operatorname{binaryRepresentation}\left(n - 4\right): \mathbb{Z}))\right) \land \operatorname{mk}\left(n \mapsto (\operatorname{binaryRepresentation}\left(n\right): \mathbb{Z})\right) \cdot ((1 - X)(1 - 10 \cdot X)(1 + 10 \cdot X)(1 - 100 \cdot X)) = 1 - 101 \cdot X + 10101 \cdot X^{2} + 89910 \cdot X^{3} - 101000 \cdot X^{4}\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.claim` (`✓ std3`).

*Citation.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

Hasler's closed form for A267681, with [n odd] = n mod 2 and [0 < n] the value of if 0 < n then 1 else 0; Barker's recurrences for n > 4 and his generating functions for both sequences. Each denominator has constant term 1, so the generating function is stated as the product of the series with its denominator; all values are cast to the integers.

**Theorem 1.7 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a267681-rule201-barker-hasler` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a267681-rule201-barker-hasler","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Price (2016). *OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures*. URL: <https://oeis.org/A267681>.

*Commentary.*

By induction on n, every row n at least 1 has the cell at x ON exactly when |x| is at least 2, or x = 0 and n is even: the rule table sends 111, 011 and 110 to 1, keeps the cells at x = -1 and x = 1 off through 001, 101 and 100, and flips the centre through 000 to 1 and 010 to 0; row 1 comes from row 0 through 000, 001, 100 and 010. Hence the window of row n at least 1 in base b is the geometric sum of b^j for j < 2n + 1 minus b^(n+1), b^(n-1) and, for odd n, b^n. With (b - 1) times the geometric sum equal to b^(2n+1) - 1 and 2 [n odd] = 1 - (-1)^n, for every base b at least 1, twice (b - 1) times the window is a fixed combination of b^(2n), b^n, (-b)^n and 1, each annihilated by (1 - x)(1 - bx)(1 + bx)(1 - b^2 x); for b = 2 and b = 10 this gives the two recurrences for n > 4, and for b = 2 the same evaluation is Hasler's formula. Comparing coefficients, the recurrence makes every coefficient of the product with the denominator vanish from x^5 on, and the first five coefficients come from the values 1, 0, 21, 99, 471 and 1, 0, 10101, 1100011, 111010111.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.binaryRepresentation`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.cell`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.decimalRepresentation`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.rule201`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.windowValue`
