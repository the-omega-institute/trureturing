# Common weights for grouped allocations

## Abstract

Common weight families for integer and fractional grouped demands.

**Theorem 1.1 (The digit budget gives one weight family for all compatible allocations).**

$$\forall k n q, 0 < k \land k\cdot q+1 \le (k+1)^n \Rightarrow \operatorname{CommonWeights}\left(k, n, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_weights_for_allocations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a positive natural number, and let n and q be natural numbers. CommonWeights(k,n,q) means there exist n natural weights with total q. For every positive number t of groups, every nonnegative natural U with U at least k times the predecessor of t, and every natural demand vector with total U times q, the same weights admit an allocation. Each weight has U identical copies to distribute, and each group must receive exactly its demand.

Choose powers of k plus one and clip at total q. If d is the next positive weight and T is the earlier total, then d minus one is at most k times T. The residual capacity after dividing the group demands by d and rounding down can discard at most t times d minus t units of mass. A total capacity below U would contradict the lower bound on U times T. After allocating the new copies, use the earlier weights for the remaining demands.

The scalar growth condition comes from Rødseth, Minimal r-Complete Partitions, Journal of Integer Sequences 10 (2007), Article 07.8.3, Lemmas 3.1–3.2.

**Theorem 1.2 (A fractional weight can be allocated in bundles).**

$$\forall k n A b K, 0 < k \land 0 < b \land 0 < K \land K\cdot b = k \land b \le A \land \operatorname{DoesNotDivide}\left(b, A\right) \land K\cdot A+1 \le (K+1)\cdot(k+1)^n \Rightarrow \operatorname{FractionalWeights}\left(k, n, A, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_fractional_allocations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All scalar parameters are natural numbers. FractionalWeights(k,n,A,b) means there exist n plus one natural weights, of total A, with the following simultaneous allocation property. For every positive number t of groups, every U divisible by b and at least k times the predecessor of t, and every natural demand vector x with b times its total equal to U times A, there is an allocation of U copies of every weight. The mass assigned to each group is b times its demand.

Take T to be the smaller of the integer part of A divided by b and the sum of the first n powers of k plus one, starting with power zero. The capacity inequality makes the remaining weight A minus b times T small enough to allocate its U copies in bundles of b. Each bundle pays an integer demand in units of b. The remainder is covered by the common integer weight family of total T, scaled by b. The weights are chosen before the group demands.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_fractional_allocations`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_weights_for_allocations`
