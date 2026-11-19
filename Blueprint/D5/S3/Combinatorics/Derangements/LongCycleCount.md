# Derangements with a unique long cycle

## Abstract

For 2 ≤ k ≤ n with 2k > n, the derangements of n labels with a k-cycle number C(n,k)(k−1)! D_(n−k).

**Theorem 1.1 (The long-cycle count).**

Lean statement: `D5/S3/Combinatorics/Derangements/LongCycleCount.long_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/LongCycleCount.long_cycle` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *OEIS A378495, FORMULA (revision #70): refutation and correction*. DOI: [10.5281/zenodo.23903309](https://doi.org/10.5281/zenodo.23903309). URL: <https://doi.org/10.5281/zenodo.23903309>.

*Commentary.*

For 2 ≤ k ≤ n with 2k > n, T(n,k) + C(n,k)(k−1)! D_(n−k) = D_n, so D_n − T(n,k) = C(n,k)(k−1)! D_(n−k) = n! D_(n−k)/(k (n−k)!), with D_0 = 1 and D_1 = 0. A derangement with a k-cycle has cycle type k ::ₘ m′, where m′ is the cycle type of a derangement of n−k labels; since every part of m′ is at most n−k < k, the part k occurs once. The class sizes from Perm.card_of_cycleType_mul_eq then satisfy #(k ::ₘ m′)·k(n−k)! = n!·#m′, and summing over m′ gives the count. This is Lemma 2 of H. Ma and W. Zhang; the identity was proved earlier by L.-H. Su (Proposition 7.4) and later by A. Kallat (Theorem 4.1(c)-(d)).

## References

- Truth anchor: `D5/S3/Combinatorics/Derangements/LongCycleCount.long_cycle`
- Dependency: [D5/S3/Combinatorics/Derangements/TerminalDifference](TerminalDifference.md)
