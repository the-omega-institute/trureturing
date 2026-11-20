# Signs of the real-step Eulerian triangle

## Abstract

For real r ≥ 3, the step −r Eulerian triangle has positive even rows and negative odd-row interiors.

**Theorem 1.1 (The second column in even rows).**

Lean statement: `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.second_even_positive`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.second_even_positive` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proof of Chen and Chen's parity-positivity conjectures: OEIS A392664–A392666, COMMENTS, and Conjecture 2 (p. 1)*. DOI: [10.5281/zenodo.23957560](https://doi.org/10.5281/zenodo.23957560). URL: <https://zenodo.org/records/23957560>.

*Commentary.*

For real r ≥ 3 and every solution T of the step −r recursion, T(n,2)>0 for every even n ≥ 2 (Lemma 2 of the source). Applying the recursion twice at k=2 gives T(n+2,2)=(r−1)²T(n,2)+r(r−2)n+2−r². Since T(2,2)=1, the case n=2 gives T(4,2)=2r(r−3)+3>0. For n ≥ 4 the forcing term equals r(r−2)(n−4)+3r(r−3)+r+2>0, and induction over even n finishes.

**Theorem 1.2 (Even rows positive, odd interiors negative).**

Lean statement: `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proof of Chen and Chen's parity-positivity conjectures: OEIS A392664–A392666, COMMENTS, and Conjecture 2 (p. 1)*. DOI: [10.5281/zenodo.23957560](https://doi.org/10.5281/zenodo.23957560). URL: <https://zenodo.org/records/23957560>.

*Commentary.*

For every real r ≥ 3 the step −r recursion has a solution, and every solution T satisfies T(n,k)>0 for every positive even n and 1 ≤ k ≤ n, and T(n,k)<0 for every odd n ≥ 3 and 1<k<n. If row n is positive, both coefficients −r(n+1−k)+1 and −r(k−1)+1 are negative at each interior position of row n+1, so that row's interior is negative. In the next even row both products at positions 3 through n are then positive. The second position uses the column bound above, the penultimate one the reflection T(n,k)=T(n,n+1−k), and the two boundary entries equal 1. This is Theorem 1 of H. Ma and W. Zhang's proof of Chen and Chen's parity-positivity conjectures (DOI 10.5281/zenodo.23957560) for all real r ≥ 3. The even-row positivity for integer r ≥ 3, which includes the conjectures of OEIS A392664–A392666 at r=3,4,5, is already formalized over ℤ in ChenChenParityPositivity.even_rows_positive.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.second_even_positive`
- Dependency: [D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums](ChenChenRealStepRowSums.md)
