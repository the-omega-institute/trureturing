# Dyadic Rows At Powers Of Two

## Abstract

The rows at powers of two are linear plus quadratic, which contradicts a printed sum.

The row polynomials R(n, x) satisfy R(2n+1, x) = x R(n, x) and, for positive n, R(2n, x) = x (R(n, x+1) - R(n, x)), starting from R(0, x) = x. Their coefficients form the table T of OEIS A373183, and the values at x = 1 form OEIS A329369. Mikhail Kurkov printed on June 5, 2024 a sum expressing a value at index 2^m n + q through values at the indices 2^m (2^(i-1) - 1) + q, quantified over all natural n, m and q. The rows at a positive power of two are computed here in closed form, and they make the two sides of that sum differ.

Indices are natural numbers and subtraction of indices is natural subtraction. Coefficients and values are integers, so the subtractions inside them are integer subtractions. The letter v denotes the two-adic valuation and w the number of ones in the binary expansion. The summation index i runs over an interval of natural numbers.

**Definition 1.1 (Values of the rows at one).**

$$\forall n \in \mathbb{N}, \operatorname{b}\left(n\right) = \operatorname{eval}\left(1, \operatorname{R}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

Evaluating a row polynomial at one adds up its coefficients. This is the quantity the printed sum relates across indices.

**Definition 1.2 (The printed sum).**

$$\forall n,m,q \in \mathbb{N}, \operatorname{S}\left(n, m, q\right) = \sum_{{1 + \operatorname{v}\left(n + 1\right) \le i \le \operatorname{w}\left(n\right) + 1}} \operatorname{T}\left(n, i\right) \cdot \operatorname{b}\left(2^{m} \cdot \left(2^{i - 1} - 1\right) + q\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.kurkovSum` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

The lower limit is one plus the two-adic valuation of n+1 and the upper limit is one plus the binary weight of n, which is the length of row n. The summand pairs the row coefficient at i with the value at the index obtained from i.

**Definition 1.3 (The printed sum read for every triple).**

$$\forall n,m,q \in \mathbb{N}, \operatorname{b}\left(2^{m} \cdot n + q\right) = \operatorname{S}\left(n, m, q\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.KurkovRowRecurrence` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

This is the printed reading, in which q ranges over all natural numbers with no relation to m. It is stated as a proposition so that its negation can be proved.

**Lemma 1.4 (The value at zero).**

$$\operatorname{b}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

The row at zero is x, whose value at one is one.

**Lemma 1.5 (The odd step).**

$$\forall r \in \mathbb{N}, \operatorname{b}\left(2 \cdot r + 1\right) = \operatorname{b}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_odd_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

Multiplying a row by x does not change its value at one, so the odd step of the printed recurrence holds for these values.

**Lemma 1.6 (The even step).**

$$\forall r \in \mathbb{N}, 0 < r \implies \operatorname{b}\left(2 \cdot r\right) = \operatorname{b}\left(r\right) + \operatorname{b}\left(r - 2^{\operatorname{v}\left(r\right)}\right) + \operatorname{b}\left(2 \cdot r - 2^{\operatorname{v}\left(r\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_even_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

The even step is the value at one of the row identity already carried in this repository for the same table. So the two printed recurrences that define the sequence are consequences here, not assumptions.

**Lemma 1.7 (Closed form at powers of two).**

$$\forall k \in \mathbb{N}, 0 < k \implies \operatorname{R}\left(2^{k}\right) = \left(2^{k} - 1\right) \cdot x + 2^{k} \cdot x^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.R_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on k. The row at index two is x + 2x^2. Passing from the row at 2^k to the row at 2^(k+1) applies x (P(x+1) - P(x)) to a polynomial a x + c x^2, which yields (a + c) x + 2c x^2. Starting from a = 2^k - 1 and c = 2^k reproduces the same shape one step up.

**Lemma 1.8 (Values at powers of two).**

$$\forall k \in \mathbb{N}, \operatorname{b}\left(2^{k}\right) = 2^{k + 1} - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding the two coefficients of the closed form gives 2^(k+1) - 1. The index zero is separate: the row at one is x^2, whose value is one.

**Lemma 1.9 (Values just after powers of two).**

$$\forall k \in \mathbb{N}, 0 < k \implies \operatorname{b}\left(2^{k} + 1\right) = 2^{k} - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_two_pow_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index 2^k + 1 is odd, so the odd step reduces it to the index 2^(k-1), whose value is 2^k - 1.

**Theorem 1.10 (The two sides differ at every power of two).**

$$\forall k \in \mathbb{N}, 0 < k \implies \operatorname{b}\left(2^{0} \cdot 2^{k} + 1\right) \neq \operatorname{S}\left(2^{k}, 0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.printed_recurrence_ne_at_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

Take n = 2^k, m = 0 and q = 1. The lower limit is one because 2^k + 1 is odd, and the upper limit is two because the binary weight is one, so the sum has the two terms i = 1 and i = 2. The closed form gives the coefficients 2^k - 1 and 2^k, and the values at the indices one and two are one and three. The sum is therefore 2^(k+2) - 1 while the left side is 2^k - 1. Every triple produced here has q at least 2^m, so the family says nothing about the reading in which q stays below 2^m.

**Theorem 1.11 (The printed reading is false).**

$$\neg (\forall n,m,q \in \mathbb{N}, \operatorname{b}\left(2^{m} \cdot n + q\right) = \operatorname{S}\left(n, m, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.not_kurkovRowRecurrence` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a329369-printed-row-sum-range` (refuted) by `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.not_kurkovRowRecurrence`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a329369-printed-row-sum-range","declaration_gid":"D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.not_kurkovRowRecurrence","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

One instance of the previous family, at k = 1, contradicts the printed reading. What is settled is that reading alone. The reading in which q stays below 2^m is a different assertion and is not settled here.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.KurkovRowRecurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.R_two_pow`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_even_index`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_odd_index`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_two_pow`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_two_pow_add_one`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.b_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.kurkovSum`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.not_kurkovRowRecurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.printed_recurrence_ne_at_two_pow`
- Dependency: [D5/S1/Digit/DyadicRowPolynomialRecurrence](../../Digit/DyadicRowPolynomialRecurrence.md)
