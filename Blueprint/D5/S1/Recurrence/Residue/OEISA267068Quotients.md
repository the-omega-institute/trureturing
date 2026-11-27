# The A267068 quotient formulas

## Abstract

The quotients c_n = (n + 1)/a_n of Curtz's denominators are integers with six affine residue formulas, Barker's recurrence and generating function, and the three sequence identifications of A267068.

**Definition 1.1 (The quotient sequence).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.c`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA267068Quotients.c` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For the reduced denominators a_n of the zeroth row of Curtz's triangle, c_n is the natural-number quotient (n + 1)/a_n; the theorem shows the division is exact.

**Definition 1.2 (A130196).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A130196`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA267068Quotients.A130196` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A130196 has offset 0 and repeats the period [1, 2, 2].

**Definition 1.3 (A047245).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047245`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047245` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A047245 has offset 1 and lists the numbers congruent to 1, 2 or 3 modulo 6; its n-th term is 6⌊(n − 1)/3⌋ + ((n − 1) mod 3) + 1.

**Definition 1.4 (A052901).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A052901`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA267068Quotients.A052901` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A052901 has offset 0, period 3, value 3 at multiples of 3 and value 2 elsewhere.

**Definition 1.5 (A047238).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047238`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047238` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A047238 has offset 1 and lists the numbers congruent to 0 or 2 modulo 6; its n-th term is 6⌊(n − 1)/2⌋ + 2((n − 1) mod 2).

**Theorem 1.6 (Quotient values, recurrence and series).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA267068Quotients.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA267068Quotients.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For every n, a_n divides n + 1, and for every k ≥ 0 (c_{6k}, …, c_{6k+5}) = (6k + 1, 2, 3, 2, 6k + 5, 1). For n ≥ 12, c_n = 2c_{n−6} − c_{n−12}. In the integer formal power series ring, (∑ c_n z^n)(1 − z⁶)² = 1 + 2z + 3z² + 2z³ + 5z⁴ + z⁵ + 5z⁶ − 2z⁷ − 3z⁸ − 2z⁹ + z¹⁰ − z¹¹. Since (1 − z⁶)² has constant term one, this is Barker's generating function. Moreover c_{2n+1} = A130196(n + 1), c_{A047245(n+1)} = A052901(n + 2) and c_{3n} + c_{3n+1} + c_{3n+2} = A047238(n + 3) for every n ≥ 0. The residue values come from dividing n + 1 by the frozen six denominator formulas. The recurrence follows because each residue subsequence is affine, and the series follows by comparing coefficients. The identifications are checked on residues modulo 6. This is Corollary 6 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584).

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047238`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A047245`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A052901`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.A130196`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.c`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA267068Quotients.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture](OEISA189733DenominatorConjecture.md)
