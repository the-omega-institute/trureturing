# Original Prime Sources: Legal Exchange and Inventory Order

## Abstract

Literal original maxima have ordered clocks and nested complete Euler inventories.

**Theorem 1.1 (Complete-label adjacency excludes every internal prime).**

Lean statement: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_label_window_no_internal_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_label_window_no_internal_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p<r in originalLabelWindow(ell), assume no label of that entire literal window lies strictly between p and r. Then no ordinary prime lies strictly between them. Any such prime would satisfy the same lower exponential bound as p and the same upper bound as r. Completeness of the label interval is essential; an arbitrary prime subsequence does not suffice.

**Theorem 1.2 (A strict positive integer inventory change pays the source-clock gap).**

Lean statement: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.inventory_gap_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.inventory_gap_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p<r be ordinary consecutive primes, U,V positive natural numbers, U dividing V and U different from V. Then log(r*V)-log(p*U)<=2*(log(V)-log(U)). Bertrand gives log(r)-log(p)<=log(2). Writing V=U*k, positivity and strict change force k>=2, hence log(V)-log(U)>=log(2). Exact logarithmic factorization combines the two increments. OriginalInventoryNormalizerLoss consumes this charge on every omitted edge of the complete original label chain.

**Theorem 1.3 (Full source maximality supplies the charged complete inventories).**

Lean statement: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_inventory_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_inventory_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primes p<r and original maximizing ties N,M, assume 243<=log(N), 243<=log(M), log(N)<p, log(M)<p and no internal ordinary prime. The exact source-order theorem supplies N=p*U and M=r*V with positive U,V retaining 5040 and U dividing V. A strict change U!=V implies log(M)-log(N)<=2*(log(V)-log(U)). The quotient identification and complete-window consumer are in OriginalInventoryNormalizerLoss. No normalizer smallness or signed prime-moment estimate is assumed or concluded here.

The source geometry is the late, large-label branch of AVB10-AVB14 in Library/ArithSums/nicolas2025comparison.md. The source objective is exactly log(sigma(n)/n)-log(log(log(n))), and originalMaximizes compares every positive integer divisible by the full 5040*p floor. The prime layer marginal, strict optimalLayerCount and actual price g(t)=1/(t*log(t)) are the existing project definitions.

**Theorem 1.4 (Two-prime exchange orders actual sources and supplies equal-inventory intervals).**

Lean statement: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p<r be primes and let N,M be arbitrary original maximizing ties in their respective p and r classes. Assume 243<=log(N), 243<=log(M), log(N)<p and log(M)<p. Then there are complete positive inventories U,V with N=p*U, M=r*V, 5040 dividing both, and both p and r absent from each inventory. One has U dividing V and log(r)-log(p)<=log(M)-log(N), hence log(N)<log(M). Every natural direction, including absent and nonprime directions, has its exact strict layer count at its own endpoint clock. If U=V, the same inventory has those counts at every t in the full closed interval [log(N),log(M)], including both endpoints.

Own-clock classification supplies complete U and V. The actual first-clock bound excludes the other forcing label from each inventory. The completed integers p*V and r*U are legal opposite-class competitors, retaining every mandatory 5040 layer. All swapped prime layers are first layers, so their summed Euler increments cancel exactly. If the clock gap were smaller than log(r)-log(p), their swapped clocks would be strictly more spread with the same sum. The existing strict log-log rectangle, on clocks greater than one certified by the mandatory core, would then contradict the two actual maximality inequalities. Only after this exchange obstruction establishes clock order is decreasing price used to nest strict inventories. Equal endpoint inventories sandwich the strict inventory at every intermediate clock by divisibility.

This is an unbounded theorem for arbitrary prime labels and integers satisfying the explicit source premises, rather than a bounded certificate or a reduction with an assumed order conclusion. Its new mathematical step is the legal exchange obstruction, consumed in the inventory nesting and closed-interval supplier. The closed interval is the inventory clause needed by OriginalFirstClockTransport.GoodEdge. Attainment, cofinal existence of good edges, signed-moment bounds, normalizer transfer and RH remain outside this conclusion.

The supporting results original_label_window_no_internal_prime, inventory_gap_log_bound and original_prime_source_inventory_gap have no Reg mirror. Their four-slot escape audits remain unfinished under https://github.com/the-omega-institute/trureturing/issues/23015. No completed registration is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.inventory_gap_log_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_label_window_no_internal_prime`
- Truth anchor: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_inventory_gap`
- Truth anchor: `D5/S3/Arith/Robin/OriginalPrimeSourceOrder.original_prime_source_order`
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](ActualTwoPriceDefect.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMaximumPurePackets](OriginalMaximumPurePackets.md)
- Dependency: [D5/S3/Arith/Robin/RestrictedDivisorStrictInventory](RestrictedDivisorStrictInventory.md)
