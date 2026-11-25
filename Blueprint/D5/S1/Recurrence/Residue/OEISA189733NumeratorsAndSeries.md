# Numerators and generating functions for OEIS A189733

## Abstract

The reduced numerators of the zeroth row of Curtz's rational triangle repeat the block (0, 1, 1, 1, 0, −1) with least period six, and the numerators and denominators have the stated rational generating functions and recurrences.

**Definition 1.1 (The numerator sequence).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.p`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.p` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

Write b_n = B(0,n) = T(0,n) for the zeroth row of the triangle of the denominator module and p_n for the reduced integer numerator of b_n, with p_n = 0 when b_n = 0. The denominator a_n is the reduced positive denominator from the same module, with a_n = 1 when b_n = 0.

**Theorem 1.2 (Numerator period, recurrences and generating functions).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For every k ≥ 0, (p_{6k}, …, p_{6k+5}) = (0, 1, 1, 1, 0, −1), so p has period six; every d ≥ 0 with p_{n+d} = p_n for all n is a multiple of six. For n ≥ 12, a_n = 2a_{n−6} − a_{n−12}. In the integer formal power series ring, (∑ a_n z^n)(1 − z⁶)² = 1 + z + z² + 2z³ + z⁴ + 6z⁵ − z⁶ + 2z⁷ + z⁸ + z⁹ − z¹⁰, which is Barker's generating function because 1 − z⁶ has constant term one and is invertible. Likewise (∑ p_n z^n)(1 − z⁶) = z + z² + z³ − z⁵ and (∑ p_n z^n)(1 − z)(1 − z + z²)(1 + z + z²) = z(1 + z² − z³). For every n ≥ 0, with integer floors, p_n = (1 + (−1)^⌊(n−1)/3⌋)/2 − ⌊(n+1)/6⌋ + ⌊n/6⌋, where ⌊−1/3⌋ = −1 at n = 0. For n ≥ 5, p_n = p_{n−1} − p_{n−2} + p_{n−3} − p_{n−4} + p_{n−5}. The proof reads all values from the six residue formulas for b_n and a_n. The denominator series is compared coefficientwise using the recurrence, and the reduced numerator series follows by cancelling 1 + z. These are Corollaries 2 and 5 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584).

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.p`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture](OEISA189733DenominatorConjecture.md)
