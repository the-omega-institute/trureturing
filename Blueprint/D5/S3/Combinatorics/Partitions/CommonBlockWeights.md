# Common weights for grouped allocations

## Abstract

One integer weight family for all compatible grouped allocations.

**Theorem 1.1 (The digit budget gives one weight family for all compatible allocations).**

$$\forall k n q, 0 < k \land k\cdot q+1 \le (k+1)^n \Rightarrow \operatorname{CommonWeights}\left(k, n, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_weights_for_allocations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a positive natural number, and let n and q be natural numbers. CommonWeights(k,n,q) means there exist n natural weights with total q. For every positive number t of groups, every nonnegative natural U with U at least k times the predecessor of t, and every natural demand vector with total U times q, the same weights admit an allocation. Each weight has U identical copies to distribute, and each group must receive exactly its demand.

Choose powers of k plus one and clip at total q. If d is the next positive weight and T is the earlier total, then d minus one is at most k times T. The residual capacity after dividing the group demands by d and rounding down can discard at most t times d minus t units of mass. A total capacity below U would contradict the lower bound on U times T. After allocating the new copies, use the earlier weights for the remaining demands.

The scalar growth condition comes from Rødseth, Minimal r-Complete Partitions, Journal of Integer Sequences 10 (2007), Article 07.8.3, Lemmas 3.1–3.2.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_weights_for_allocations`
