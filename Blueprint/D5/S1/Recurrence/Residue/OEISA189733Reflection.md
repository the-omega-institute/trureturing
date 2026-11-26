# Reflection and inverse binomial transform for Curtz's array

## Abstract

Curtz's full rational square array satisfies the signed reflection identity, and its zeroth column is the inverse binomial transform of its zeroth row.

**Definition 1.1 (The full square array).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA189733Reflection.B`

*Formalization.* `D5/S1/Recurrence/Residue/OEISA189733Reflection.B` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For m ≤ n the entry B(m, n) is the upper entry triangle m (n − m) of the frozen denominator module. For m > n it is defined by the lower branch B(m, n) = B(m − 1, n + 1) − B(m − 1, n), as in the A189733 programs.

**Theorem 1.2 (Reflection and the inverse binomial transform).**

Lean statement: `D5/S1/Recurrence/Residue/OEISA189733Reflection.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/OEISA189733Reflection.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011*. DOI: [10.5281/zenodo.23957584](https://doi.org/10.5281/zenodo.23957584). URL: <https://zenodo.org/records/23957584>.

*Commentary.*

For all m and d, B(m, m + d) is the frozen entry triangle m d. For all m and n: B(m, m) = 0, B(m, n) = (−1)^{m+n+1} B(n, m), and B(m + 1, n) = B(m, n + 1) − B(m, n). Moreover, for every n ≥ 0, B(n, 0) = ∑_{j=0}^{n} (−1)^{n−j} C(n, j) b_j = (−1)^{n+1} b_n, where b_j = B(0, j). The reflection is proved by induction on m for m ≥ n. At m = n + 1 the lower branch gives B(n, n + 1). For larger m, the upper recurrence B(n, m) = B(n, m − 1) + B(n + 1, m − 1) matches the lower branch after the sign change. The difference identity is the lower branch below the diagonal and the rearranged upper recurrence above it. Iterating it expresses B(m, ·) as the m-th forward difference of the zeroth row. Setting n = 0 and applying reflection gives the last identity. This is Corollary 3 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584). Together with the finite sums of Corollary 4, the zero diagonal and the reflection determine every entry of the array.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733Reflection.B`
- Truth anchor: `D5/S1/Recurrence/Residue/OEISA189733Reflection.result`
- Dependency: [D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture](OEISA189733DenominatorConjecture.md)
