# The absolute Hermite mode and its interlacing with the signed mode

## Abstract

The absolute Hermite mode has a quadratic threshold and a floor formula, its differences form blocks (1,−1) and (1,1,−1), ties sit at b and b + 2, and it interlaces the signed mode.

**Definition 1.1 (The offset h_k).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.hOffset`

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.hOffset` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

h_k is the least j with (j + 1)(j + 2) ≥ 4k.

**Definition 1.2 (The block start m_k).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absStart`

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absStart` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

m_k = 2k + h_k, so m_0 = 0.

**Definition 1.3 (The long-block indices).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.L`

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.L` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

L_j = ⌊(j + 1)(j + 2)/4⌋.

**Definition 1.4 (The signed maximum B(n)).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.signedMax`

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.signedMax` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

B(n) is the coefficient of H_n at the signed mode a(n).

**Definition 1.5 (The absolute maximum M(n)).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absMax`

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absMax` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

M(n) is the absolute value of the coefficient of H_n at the absolute mode b(n).

**Theorem 1.6 (Threshold, floor formula, blocks, ties and interlacing).**

Lean statement: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)*. DOI: [10.5281/zenodo.23957586](https://doi.org/10.5281/zenodo.23957586). URL: <https://zenodo.org/records/23957586>.

*Commentary.*

Let b(n) be the least exponent of a largest absolute coefficient of the physicists' H_n and t(n) = (n − b(n))/2. Then b(n) ≡ n (mod 2), and for j ≡ n (mod 2), b(n) ≤ j exactly when j² + 5j + 2 ≥ 2n. Every degree has a unique absolute maximum or exactly two, and the maximum is unique exactly off the tie degrees N_m. Moreover t(n) = ⌊(2n + 5 − √(8n + 17))/4⌋, b(n)² ≤ 2n and −5/2 < b(n) − √(2n). The difference b(n + 1) − b(n) is −1 exactly when n + 1 = m_k; m_0 = 0, m_1 = 3 and m_{k+1} − m_k ∈ {2, 3}, with gap three exactly when k = L_j, m_{L_j} = 2L_j + j, and gap two strictly between consecutive L_j. At a tie degree the maximizing exponents are b(n) and b(n) + 2, their coefficients have opposite signs and B(n) = M(n); in general B(n) = M(n) exactly at tie degrees or when t(n) is even; and a(n) − b(n) ∈ {−2, 0, 2}.

The coefficient at exponent n − 2r is (−1)^r times its absolute value U_{n,r}, and the ratios U_{n,r}/U_{n,r−1} = (j + 1)(j + 2)/(4r), j = n − 2r, strictly decrease. So U rises strictly up to t(n) − 1, weakly to t(n), and strictly falls afterwards; the threshold and the floor formula follow from solving (2j + 5)² ≥ 8n + 17. The signed maximum is the largest U at an even index; by the shape of U that index is t(n) or a neighbour, giving the interlacing, and it equals M(n) exactly when t(n) is even or, at a tie degree, when the second maximizing index t(n) − 1 is even. Substituting n = 2k + j in the threshold gives the block starts m_k, and (j + 1)(j + 2) increases by 2j + 4 ≥ 4, so h_{k+1} − h_k ∈ {0, 1}, with a jump exactly at k = L_{h_k}. The bound b(n)² ≤ 2n uses the failure of the threshold at b(n) − 2. This covers Corollary 4 and the clauses of Theorem 3 not already in the frozen HermiteAbsoluteMode and HermiteAbsoluteTieOrders results, from H. Ma and W. Zhang (DOI 10.5281/zenodo.23957586), on questions of Mike Sheppard in OEIS A381423, A381524 and A381737.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.L`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absMax`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.absStart`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.hOffset`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.result`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.signedMax`
- Dependency: [D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders](HermiteAbsoluteTieOrders.md)
