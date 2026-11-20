# The fourth diagonal of the A194767 second-kind array

## Abstract

The fourth diagonal of the A194767 second-kind array has reduced denominators (m + 1)(m + 2)/gcd(3, m + 2), and its numerators are A146535 at the shifted index.

**Definition 1.1 (The fourth diagonal).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.C3`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.C3` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

The second-kind array is C(m, n) = 2B(m, n + 1) − B(m, n), where B is Curtz's rational array. Its fourth diagonal is C(m, m + 3) = 2B(m, m + 4) − B(m, m + 3), written with the frozen upper entries triangle m 4 and triangle m 3.

**Definition 1.2 (Its reduced denominators).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.d`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.d` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

d_m is the reduced positive denominator of C(m, m + 3).

**Definition 1.3 (A051176).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A051176`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A051176` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A051176(r) = r/gcd(r, 3) from offset 0: r/3 when 3 divides r, and r otherwise.

**Definition 1.4 (A146535).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A146535`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A146535` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A146535(r) is the reduced numerator of (2r − 1)/3, indexed from r = 1. The value at r = 0 is not used.

**Definition 1.5 (A306368).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A306368`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A306368` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A306368(r) is the reduced numerator of (r + 3)(r + 4)/((r + 1)(r + 2)), from offset 0.

**Theorem 1.6 (Value, denominators and the numerator index correction).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For every m ≥ 0, C(m, m + 3) = (−1)^{m+1}(2m + 1)/((m + 1)(m + 2)) and d_m = (m + 1)(m + 2)/gcd(3, m + 2). For every k ≥ 0, (d_{3k}, d_{3k+1}, d_{3k+2}) = ((3k + 1)(3k + 2), (k + 1)(3k + 2), 3(k + 1)(3k + 4)). The integer power series of d_m times (1 − z³)³ is 2(1 + z + 6z² + 7z³ + 2z⁴ + 3z⁵ + z⁶). For every m ≥ 0, d_m = (m + 1)A051176(m + 2) and d_{m+2} = 2A306368(m). Finally, C(m, m + 3) = (−1)^{m+1}A146535(m + 1)/d_m for every m, while the unshifted formula with A146535(m) fails at m = 2. The value follows from the array recurrence. The denominators come from explicit Bézout certificates in each residue class modulo 3. The generating function follows from the resulting order-nine recurrence. The A306368 formula uses Bézout certificates in each residue class modulo 6. This is Corollary 7 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584).

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A051176`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A146535`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.A306368`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.C3`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.d`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture](OEISA189733DenominatorConjecture.md)
