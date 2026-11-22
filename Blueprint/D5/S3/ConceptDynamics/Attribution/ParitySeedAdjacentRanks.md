# A fixed-seed budget that requires an edge skipping a rank

## Abstract

Refute adjacent-rank compression at an eight-coordinate fixed-seed budget of 36.

**Definition 1.1 (The adjacent-rank assertion at budget 36).**

$$\operatorname{AxisFactorWithin}\left(3, 0, 36\right) \Rightarrow \operatorname{AdjacentAxisFactorWithin}\left(3, 0, 36\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix coordinate zero in dimension eight and multiplier three. The assertion says that a factor within budget 36 still exists when each ordinary allowed edge either joins two copies of the same subset or adds exactly one element. The exceptional row of the full subset keeps all its outgoing edges except the deleted marked edge. The two full-subset vertices use the same choice of parity and cap, namely even degrees at most two or odd degrees at most one. All other degrees are odd and at most three. The cost is four times the sum of one plus the number of ordinary chosen edges joining two odd subsets.

**Theorem 1.2 (The adjacent-rank assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit unrestricted factor has score at most 36. The kernel checks the row and column degrees, inclusion on ordinary edges, the absent marked edge and the total cost.

Under the adjacent-rank restriction, ordinary paid edges are diagonal. Columns of ranks zero and one force at least three paid edges in rank one. Rows of ranks five and six and the capacity of columns of ranks six and seven force at least five paid edges in rank five. With at most eight paid edges, there can be no rank-three diagonal and the full-subset row must send two edges into ranks zero and one, using all its capacity.

The 35 odd-degree rows of rank three now force an odd number of edges from rank three to four. Equal parity of the row and column degree sums through rank three makes that number even, since the only edges entering those columns from above are the two edges from the full-subset row. The contradiction forces at least nine paid edges and hence cost 40 or more under the restriction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.result`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](ParitySeedAxisFactor.md)
