# High-rank constraints at odd parity budgets

## Abstract

A lower bound from high ranks in the odd uniform parity matrix.

**Theorem 1.1 (Two rank constraints bound the total weighted intersection count).**

$$\operatorname{OddUniformMargins}\left(n, k, m, b\right) \Rightarrow 1 + \operatorname{PositivePart}\left(n + 1 - \operatorname{Twice}\left(k\right)\right) + \operatorname{PositivePart}\left(\operatorname{Choose}\left(n, 2\right) + 1 - n \cdot k\right) \le \operatorname{IntersectionCount}\left(n, m, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds.fixed_from_odd_margins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension n is even and at least six, and k is odd. The natural-number matrix m is indexed by even and odd subsets of Fin(n) and has every row and column sum equal to k. The natural-number vector b is bounded by the all-ones row, and positive at some column. These are the conditions denoted by OddUniformMargins.

IntersectionCount weights each cell by the size of the intersection of its two subsets and by its multiplicity modulo two. In the all-ones row it uses b in place of the multiplicity modulo two. PositivePart truncates a negative difference to zero.

Columns of size n minus one can use the zero and all-ones rows to meet their parity demand. Rows of size n minus two can use singleton columns. The remaining demands each force a positive intersection. Any cell used by both demands has intersection size at least n minus three. A positive entry of b in a singleton column consumes capacity in both counts. A positive entry elsewhere contributes at least three to the bound directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds.fixed_from_odd_margins`
