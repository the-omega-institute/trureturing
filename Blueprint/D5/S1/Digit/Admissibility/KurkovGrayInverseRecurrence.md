# Kurkov's Inverse Gray-Code Recurrence

## Abstract

The inverse Gray-code sequence OEIS A006068 satisfies Kurkov's highest-bit recurrence.

All indices n and all values lie in the natural numbers N. The function a is the inverse Gray-code sequence A006068; msb is the most significant bit A053644 on positive inputs, and complementSecondBit is A063946, which toggles the second bit from the left and fixes zero and one. The imported frozen function gray from GrayCodeBinaryRecurrenceClosedForm is gray(n)=xor(n,div(n,2)). Here xor is bitwise exclusive-or, div is natural-number floor division, and log(b,n) is Lean's natural-number floor logarithm Nat.log b n, with log(2,0)=0. The operator ite(c,x,y) returns x when c holds and y otherwise. Addition and powers are natural-number operations; every subtraction is truncated at zero.

**Definition 1.1 (Hanna's XOR-prefix definition).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{ite}\left((n = 0), 0, \operatorname{xor}\left(n, \operatorname{a}\left(\operatorname{div}\left(n, 2\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.a` (`✓ std3`).

*Citation.* N. J. A. Sloane; Paul D. Hanna; Mikhail Kurkov (2023). *OEIS A006068, inverse Gray code, with Kurkov's recurrence*. URL: <https://oeis.org/A006068>.

*Commentary.*

The definition of a is Hanna's XOR-prefix formula written as the recursion n XOR a(n/2), terminating at zero. Repeated substitution gives the XOR of n and its successive dyadic quotients. The inverse property is proved below; it is not assumed in this definition.

**Definition 1.2 (The highest binary place).**

$$\forall n: \mathbb{N}, \operatorname{msb}\left(n\right) = 2^{\operatorname{log}\left(2, n\right)}$$

*Formalization.* `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.msb` (`✓ std3`).

*Citation.* N. J. A. Sloane; Paul D. Hanna; Mikhail Kurkov (2023). *OEIS A006068, inverse Gray code, with Kurkov's recurrence*. URL: <https://oeis.org/A006068>.

*Commentary.*

For positive n, this is A053644(n). The displayed totalized formula has msb(0)=1, whereas OEIS A053644(0)=0. The positive recurrence uses msb only at positive arguments, including complementSecondBit(n).

**Definition 1.3 (Complementing the second bit from the left).**

$$\forall n: \mathbb{N}, \operatorname{complementSecondBit}\left(n\right) = \operatorname{ite}\left((n < 2), n, \operatorname{xor}\left(n, 2^{(\operatorname{log}\left(2, n\right) - 1)}\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.complementSecondBit` (`✓ std3`).

*Citation.* N. J. A. Sloane; Paul D. Hanna; Mikhail Kurkov (2023). *OEIS A006068, inverse Gray code, with Kurkov's recurrence*. URL: <https://oeis.org/A006068>.

*Commentary.*

This is A063946, including its values zero at zero and one at one. Both OEIS %F cases are proved and used inside result: for every natural k, 2*2^k <= n < 3*2^k gives n+2^k, while 3*2^k <= n < 4*2^k gives n-2^k. Thus toggling the second bit preserves the highest bit.

**Theorem 1.4 (The inverse property and Kurkov's recurrence).**

$$(\forall n: \mathbb{N}, \operatorname{gray}\left(\operatorname{a}\left(n\right)\right) = n) \land ((\operatorname{a}\left(0\right) = 0) \land (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(n\right) = \operatorname{a}\left(\operatorname{complementSecondBit}\left(n\right) - \operatorname{msb}\left(\operatorname{complementSecondBit}\left(n\right)\right)\right) + \operatorname{msb}\left(n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a006068-kurkov-gray-inverse-recurrence` (proved) by `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a006068-kurkov-gray-inverse-recurrence","declaration_gid":"D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.result","resolution_kind":"proved"} -->

*Citation.* N. J. A. Sloane; Paul D. Hanna; Mikhail Kurkov (2023). *OEIS A006068, inverse Gray code, with Kurkov's recurrence*. URL: <https://oeis.org/A006068>.

*Commentary.*

The first clause is the OEIS %N property: a(n) is Gray-coded into n, using the frozen gray. The second clause supplies a(0)=0. The last clause proves Kurkov's September 9, 2023 conjecture for every positive natural n: A053645 subtracts the highest bit from A063946(n), and A053644(n) supplies the added highest bit. Live strong inductions establish commutation with division by two, inverse identities, and dyadic upper bounds; the two second-bit cases complete the recurrence.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.a`
- Truth anchor: `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.complementSecondBit`
- Truth anchor: `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.msb`
- Truth anchor: `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.result`
- Dependency: [D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm](GrayCodeBinaryRecurrenceClosedForm.md)
