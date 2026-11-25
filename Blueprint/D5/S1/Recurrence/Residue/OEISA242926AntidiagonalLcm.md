# Antidiagonal denominator lcm of the zero-diagonal arrays

## Abstract

On every strict upper antidiagonal of Curtz's signed and unsigned arrays, the reduced denominators have lcm lcm(1, …, ⌊(s + 1)/2⌋) = A139550(s + 1).

**Definition 1.1 (Upper entries with arbitrary seeds).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.V`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.V` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

V w m d is V(m, m + d) for the zero-diagonal array with first-superdiagonal seeds w m = V(m, m + 1) and V(m, n) = V(m, n − 1) + V(m + 1, n − 1).

**Definition 1.2 (The antidiagonal lcm).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.antiLcm`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.antiLcm` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

antiLcm A s is the lcm of the reduced denominators of A(m, s − m) over m < s − m, with the empty lcm equal to one.

**Definition 1.3 (A139550).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.A139550`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.A139550` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

A139550(r) = lcm(1, …, ⌊r/2⌋).

**Theorem 1.4 (The antidiagonal lcm).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For every s ≥ 0 and for both the signed array B and the unsigned array U, the antidiagonal lcm equals lcm(1, …, ⌊(s + 1)/2⌋) = A139550(s + 1). For arbitrary seeds and d ≥ 1, V(m, m + d) = ∑_{j=0}^{d−1} C(d − 1 − j, j) w_{m+j}. The entries of the antidiagonal are therefore a unit upper-triangular integer combination of w_0, …, w_{h−1} with h = ⌊(s + 1)/2⌋. An integer N makes every N·V(m, s − m) an integer exactly when it makes every N·w_k an integer; passing from cleared entries to cleared seeds is a downward induction on the seed index. For both arrays the seeds are ±1/(k + 1), so N clears them exactly when 1, …, h all divide N. Two natural numbers with the same multiples are equal, which gives the lcm identity. This is Corollary 11 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584).

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.A139550`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.V`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.antiLcm`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733Reflection](OEISA189733Reflection.md)
- Dependency: [D5/S1/Recurrence/Residue/OEISA242926UnsignedLucasRow](OEISA242926UnsignedLucasRow.md)
