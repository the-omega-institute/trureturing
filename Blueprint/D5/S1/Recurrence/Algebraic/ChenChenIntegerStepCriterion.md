# Integer steps with nonnegative even rows

## Abstract

For integer m, the positive even rows of the step-m Eulerian triangle are nonnegative exactly when m ≤ −3 or m ≥ 0, and then strictly positive.

**Theorem 1.1 (The integer-step criterion).**

Lean statement: `D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proof of Chen and Chen's parity-positivity conjectures: OEIS A392664–A392666, COMMENTS, and Conjecture 2 (p. 1)*. DOI: [10.5281/zenodo.23957560](https://doi.org/10.5281/zenodo.23957560). URL: <https://zenodo.org/records/23957560>.

*Commentary.*

For every integer m, every solution of the step-m recursion has entrywise nonnegative positive even rows if and only if m ≤ −3 or m ≥ 0, and for these m the positive even rows are strictly positive. For m ≥ 0 both coefficients m(n−k)+1 and m(k−1)+1 are at least one, so induction on rows makes every entry of every row positive. For m ≤ −3 the sign theorem for real r=−m ≥ 3 applies. For m=−1 and m=−2, every solution has T(4,2)=2m+1+2(m+1)²=2m²+6m+3=−1, and a solution exists, so the even row n=4 is not nonnegative. This is Corollary 3 of H. Ma and W. Zhang's proof of Chen and Chen's parity-positivity conjectures (DOI 10.5281/zenodo.23957560).

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion.result`
- Dependency: [D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns](ChenChenRealStepSigns.md)
