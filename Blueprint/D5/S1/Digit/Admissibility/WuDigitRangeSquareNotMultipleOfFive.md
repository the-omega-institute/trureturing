# Digit Extrema Five and Nine Exclude Multiples of Five

## Abstract

Wu's A254074 conjecture excludes multiples of five from the specified decimal digit range.

**Definition 1.1 (Decimal digit range from five through nine).**

$$\forall n \in \mathbb{N},\; (DigitRangeFiveNine\left(n\right)) \Leftrightarrow ((min\left(digits\left(10, n\right)\right) = some\left(5\right)) \land (max\left(digits\left(10, n\right)\right) = some\left(9\right)))$$

*Formalization.* `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.DigitRangeFiveNine` (`✓ std3`).

*Citation.* Felix Fröhlich; Chai Wah Wu (2017). *OEIS A254074, Numbers k such that the decimal expansions of both k and k^2 have 5 as the digit with the smallest value and 9 as the digit with the largest value*. URL: <https://oeis.org/A254074>.

*Commentary.*

DigitRangeFiveNine(n) means that Mathlib's least-significant-first decimal digit list has List.min? equal to some 5 and List.max? equal to some 9.

**Theorem 1.2 (No term in the digit range is a multiple of five).**

$$\forall k \in \mathbb{N},\; (k > 0) \Rightarrow \left((DigitRangeFiveNine\left(k\right)) \Rightarrow \left((DigitRangeFiveNine\left(k^{2}\right)) \Rightarrow \left(\neg (5 \mid k)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a254074-wu-digit-range-square-not-multiple-of-five` (proved) by `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a254074-wu-digit-range-square-not-multiple-of-five","declaration_gid":"D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Felix Fröhlich; Chai Wah Wu (2017). *OEIS A254074, Numbers k such that the decimal expansions of both k and k^2 have 5 as the digit with the smallest value and 9 as the digit with the largest value*. URL: <https://oeis.org/A254074>.

*Commentary.*

If five divides k, the lower digit bound forces its units digit to be 5. Writing k as 10q+5 makes its square congruent to 25 modulo 100. The maximum digit 9 in k makes k at least 59, so the tens digit 2 is present in the square and contradicts its minimum digit 5.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.DigitRangeFiveNine`
- Truth anchor: `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.result`
