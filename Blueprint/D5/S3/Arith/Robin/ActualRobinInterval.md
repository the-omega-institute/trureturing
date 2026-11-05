# Original Robin interval transfer

## Abstract

Original Robin margins transfer across actual optimizer intervals; all-price endpoint estimates remain explicit.

Write W(n)=log(sigma(n)/n) and Phi(A)=gamma+log(log(A)). The original margin is Phi(log(n))-W(n). The same objective, sigma and original integers are retained.

**Theorem 1.1 (Transfer between actual same-price optimizers).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q and original optimizers B,U at q with 3<=B<=n<=U, the margin at n is at least the convex combination of the endpoint margins, and strictly greater in the genuine interior. The weight t is (log(n)-log(B))/(log(U)-log(B)), with the source's zero convention at coincident endpoints. Objective optimality proves the W chord bound. Strict log-log concavity is proved rather than supplied as a final hypothesis; endpoint signs are not assumed in this transfer theorem.

**Theorem 1.2 (Every integer through an actual maximal endpoint).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any positive q0. Assume positive original Robin margins for every actual strict or maximal endpoint above 5040 at every price q>=q0. Then every natural integer 5040<n<=maximalInteger(q0) satisfies sigma(n)<exp(gamma)*n*log(log(n)). Natural-order coverage constructs the interval. If its price is below q0, actual prime-layer divisibility forces maximalInteger(q0)<=strictInteger(q)<=n<=maximalInteger(q0), so n equals the checked upper endpoint. Otherwise the two supplied margins and interval concavity apply. The remaining finite boundary is computed as 55440 inside the proof, using the same q11 identification as the full global reduction. The upper-price margins remain explicit hypotheses of this general theorem.

**Theorem 1.3 (The exact unpaid all-price obligation).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive original margins for every natural n>5040 are equivalent to EndpointRobinEstimates: for every positive real q with strictInteger(q)>5040, both strictInteger(q) and maximalInteger(q) have positive original margin. The constructed coverage supplies the reverse implication. Its finite branch identifies the chosen boundary price as the first layer at prime 11, with strict product 5040 and maximal product 55440, and invokes the existing finite Robin theorem there. No separate finite-boundary premise remains. This equivalence does not prove EndpointRobinEstimates.

**Theorem 1.4 (Consume endpoint estimates in the original inequality).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming EndpointRobinEstimates, every natural n>5040 satisfies sigma(n)<exp(gamma)*n*log(log(n)). The final logarithm/exponential transport pays its positivity conditions and retains the original sigma, integer factor and iterated logarithm. This conditional reduction proves neither the all-price endpoint estimates nor RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal`
- Dependency: [D5/S3/Arith/GoldenResource/ThresholdChainReduction](../GoldenResource/ThresholdChainReduction.md)
- Dependency: [D5/S3/Arith/Robin/ActualGlobalBracketing](ActualGlobalBracketing.md)
- Dependency: [D5/S3/Arith/Robin/FewDistinctPrimes](FewDistinctPrimes.md)
