# Finite sums for the entries of Curtz's array

## Abstract

Every upper entry of Curtz's rational array is an explicit alternating binomial sum.

**Theorem 1.1 (Upper entries as binomial sums).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA189733FiniteSums.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA189733FiniteSums.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For m ≥ 0 and d ≥ 1, the entry B(m, m + d), which is triangle m d in the frozen denominator module, equals (−1)^m times the sum over 0 ≤ j ≤ ⌊(d − 1)/2⌋ of (−1)^j C(d − 1 − j, j)/(m + j + 1). Write F(m, e) for the same sum with j running up to e. Terms with j > ⌊e/2⌋ vanish, because then e − j < j. Splitting off the first and last terms and applying Pascal's rule gives F(m, e + 2) = F(m, e + 1) − F(m + 1, e). This is the defining recursion of the array, so the formula follows by induction on d, with the cases d = 1 and d = 2 checked directly. This is the finite-sum formula (10) of Corollary 4 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584). The accompanying remark that B(m, m) = 0 and the reflection B(m, n) = (−1)^{m+n+1} B(n, m) determine the whole square array concerns the lower-triangular branch and is not formalized here.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733FiniteSums.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture](OEISA189733DenominatorConjecture.md)
