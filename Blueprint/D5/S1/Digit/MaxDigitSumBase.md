# The Least Base Maximizing the Digit Sum Is the First Base Above Half

## Abstract

Past eight, the least base maximizing the digit sum of a number is the first base above half of it, because every base at most half loses more than half of the number to carries while the first base above half keeps all but half.

**Definition 1.1 (Digit sum in a base).**

$$s_{b}(n) = \sum_{d\in \operatorname{digits}(b, n)} d$$

*Formalization.* `D5/S1/Digit/MaxDigitSumBase.digitSum` (`✓ std3`).

*Citation.* Jean-Marc Rebert; Sean A. Irvine (2026). *OEIS A394431, The smallest base b < n where the sum of the digits for the number n in the base b is the largest*. URL: <https://oeis.org/A394431>.

*Commentary.*

The digit sum of a natural number in a base is the sum of the list of its digits in that base, least significant first. The number zero has the empty list and so digit sum zero.

**Definition 1.2 (Least base maximizing the digit sum).**

$$(L(n, b)) \Leftrightarrow (1<b<n \land \forall c, {1<c<n \Rightarrow s_{c}(n)\leq s_{b}(n)} \land \forall c, {1<c<b \Rightarrow s_{c}(n)<s_{b}(n)})$$

*Formalization.* `D5/S1/Digit/MaxDigitSumBase.IsLeastMaxDigitSumBase` (`✓ std3`).

*Citation.* Jean-Marc Rebert; Sean A. Irvine (2026). *OEIS A394431, The smallest base b < n where the sum of the digits for the number n in the base b is the largest*. URL: <https://oeis.org/A394431>.

*Commentary.*

A base is the least maximizing base of a number when it lies strictly between one and the number, no base in that range gives a larger digit sum, and every smaller base in that range gives a strictly smaller one. This is the value the source entry records for every number above two.

**Definition 1.3 (The conjecture).**

$$(claim) \Leftrightarrow (\forall n, (8<n) \Rightarrow (L(n, \operatorname{ceil}(\frac{n+1}{2}))))$$

*Formalization.* `D5/S1/Digit/MaxDigitSumBase.claim` (`✓ std3`).

*Citation.* Jean-Marc Rebert; Sean A. Irvine (2026). *OEIS A394431, The smallest base b < n where the sum of the digits for the number n in the base b is the largest*. URL: <https://oeis.org/A394431>.

*Commentary.*

The source asserts that for every number above eight the least maximizing base is the ceiling of the number plus one, halved. At eight the assertion fails, since bases three and five both give digit sum four.

**Theorem 1.4 (The conjecture holds).**

$$\forall n, (8<n) \Rightarrow (L(n, \operatorname{ceil}(\frac{n+1}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/MaxDigitSumBase.result` (`✓ std3`). ∎

*Resolves.* `Problems/irvine-least-maximal-digit-sum-base` (proved) by `D5/S1/Digit/MaxDigitSumBase.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"irvine-least-maximal-digit-sum-base","declaration_gid":"D5/S1/Digit/MaxDigitSumBase.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Marc Rebert; Sean A. Irvine (2026). *OEIS A394431, The smallest base b < n where the sum of the digits for the number n in the base b is the largest*. URL: <https://oeis.org/A394431>.

*Commentary.*

The ceiling of the number plus one, halved, is the least base exceeding half of the number. For a base above half and below the number, the number has exactly two digits, one and the number minus the base, so its digit sum is the number minus the base plus one; this is largest at the least such base, where it equals the number minus its floor half. For a base at most half, write the number as the base times a quotient of at least two plus a remainder below the base, so the digit sum is the remainder plus the digit sum of the quotient. A digit sum never exceeds its argument, and when the quotient is at least the base, one more expansion shows that its digit sum is smaller by at least the base minus one. When the quotient is below the base, the base is at least four, since bases two and three with such a quotient force the number to be at most eight. In either case twice the digit sum is below the number, so the digit sum itself is below the number minus its floor half, which is the value at the first base above half. The only case of equality in these bounds is base three with quotient and remainder two, the number eight that the conjecture excludes.

## References

- Truth anchor: `D5/S1/Digit/MaxDigitSumBase.IsLeastMaxDigitSumBase`
- Truth anchor: `D5/S1/Digit/MaxDigitSumBase.claim`
- Truth anchor: `D5/S1/Digit/MaxDigitSumBase.digitSum`
- Truth anchor: `D5/S1/Digit/MaxDigitSumBase.result`
