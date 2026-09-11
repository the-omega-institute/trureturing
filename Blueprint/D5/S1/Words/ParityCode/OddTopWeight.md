# The odd-order boundary of A398720

## Abstract

Odd square binary matrices of top even row and column weight are counted by factorial.

**Theorem 1.1 (The factorial count).**

$$\forall n\in\mathbb{N}, \operatorname{Odd}\left(n\right) \implies \operatorname{card}\left(\operatorname{Top}\left(n\right)\right)=n!$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ParityCode/OddTopWeight.spcp_odd_top_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Gordon Thompson (2026). *A398720 — weight distribution of square single parity check product codes*. URL: <https://oeis.org/A398720>.

*Commentary.*

Top(n) is the set of functions from Fin(n) to Fin(n) to Bool whose every row and every column has an even number of true entries and whose total number of true entries is n times (n minus one). Both indices use the n by n matrix convention in the OEIS comment and data. The entry explicitly conjectures this factorial count.

A row of odd length and even weight contains at least one zero. Equality in the sum of the row bounds forces exactly one zero in each row; transposing proves the same statement for columns. The unique zero positions form a permutation. Conversely, setting precisely the permutation positions to false gives a matrix with n minus one true entries in every row and column. The constructions are inverse, and the standard count of permutations completes the proof.

The proof covers every odd natural n, including n equal to one, where the only matrix is the single false entry and has weight zero.

## References

- Truth anchor: `D5/S1/Words/ParityCode/OddTopWeight.spcp_odd_top_weight`
