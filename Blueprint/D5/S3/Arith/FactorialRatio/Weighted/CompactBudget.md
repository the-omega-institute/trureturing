# Weighted compact products and their exact excess

## Abstract

Actual weighted compact products share the ordinary compact compression budget.

Let r>=2 and H=rs+r-1. The legal parameter family is 0<=b<=floor(s/r). For nonnegative integer weights c(p,j), with j>=1 denoting p^j, write B(n) for the weighted factorial with cutoff H. The actual compact product at b is the product over 0<=i<r of B((i+1)b)/B(b) times B(s-ib). Every quotient is an integer because weighted factorials increase in divisibility.

For a number field K of degree D, take c(p,j)=normWeight(K,p,j-1) and d(p,j)=D-normWeight(K,p,j-1) for positive j. Then shiftedWeights(c) is normWeight(K), and shiftedWeights(d) is its degree complement. For legal b and 0<=i<r, the arguments b, (i+1)b and s-ib lie between 0 and s<=H. CompositionGcd.NumberFieldNorm.fullRingFactorialIdeal_norm therefore identifies every factor of the actual compact norm product with the corresponding weightedValue factor; complement_eq_weightedValue does the same for normComplement. Equality at every legal b identifies their compact gcds with G_c and G_d. The original number_field_norm_and_complement theorem identifies their full-composition gcds with T_c and T_d. Its degree bound gives c+d=D on all prime powers, so the shared budget is E_+ E_- | E^D and the chain is T_- | G_- | G^D/G_+ | T_- E^D. Here G_+ and G_- are gcds of the products of actual ideal norms and actual normComplement values at the same legal compact parameters. The identification is factor by factor before taking gcds; no commutation of ideal norm with gcd is used. The ideal is the explicitly defined prime-ideal Euler product. A separate p-ordering or integer-valued-polynomial factorial carrier and a correspondence with it are not asserted.

**Definition 1.1 (One common compact parameter).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedProduct`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

compactWeightedProduct is the actual product of weightedValue quotients and weightedValue factors, with one and the same b throughout. The adapter shiftedWeights sends the zero-based coefficient at index j in CompositionGcd to the coefficient c(p,j+1). Thus c(p,1) weights division by p, and the unused index c(p,0) has no effect.

**Definition 1.2 (The actual gcd quotient).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess`

*Formalization.* `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let G_B be the gcd of the actual compact products over all legal b, and let T_B be weightedTail(H,r-1,shiftedWeights(c)). The exact weighted composition theorem identifies T_B with the gcd over all r-part compositions of rs. The floor lower bounds prove T_B divides every compact term, so compactWeightedExcess is the exact positive integer E_B=G_B/T_B. This includes s=0 and the zero weight system.

**Theorem 1.3 (Exact primewise exponents).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>=2, any s, any natural weight system c and any p in primesLE(H), the exponent of p in E_B equals weightedPrimeLoss(r,s,p,log_p(s)+1,c(p,-)). The product valuation is the weighted sum of the paired floor sums. Subtracting the tail valuation gives the weighted sum of nonnegative floor defects. Powers above s contribute zero at every legal b. Taking the gcd takes the minimum over b of that whole sum, without choosing a different b for each prime power.

**Theorem 1.4 (Identification with the defect product).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_eq_weightedExcess`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_eq_weightedExcess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>=2 and all s,c, the actual quotient E_B is exactly weightedExcess(r,s,primesLE(H),c). Primes outside this finite set have exponent zero in every compact weighted term, hence also in its gcd and exact quotient. Equality of all prime exponents gives the integer identity.

**Theorem 1.5 (A shared budget for two actual weighted families).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_shared_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_shared_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>=2, s<r^2 and C>=0, suppose c(p,j)+d(p,j)<=C for every p in primesLE(H) and 1<=j<=log_p(s). The actual quotients E_c and E_d then satisfy E_c E_d | E^C, where E is the ordinary factorial compact excess for the same r,s and the same legal parameter family. The primewise argument evaluates both weighted costs at a single parameter minimizing the ordinary cost; separate weighted minimizers are never identified. If additionally c(p,j)+d(p,j)=C for every p in primesLE(H) and 1<=j<=H+1, the same theorem gives the exact chain T_d | G_d | G^C/G_c | T_d E^C, with G=selbergGcd(r,s). It also states G_c is nonzero, G_c divides G^C, and the displayed integer quotient is nonzero. The tail partition laws give T_c T_d=T^C, and exact division gives G_c=T_c E_c, G_d=T_d E_d and G=T E. Multiplying the shared excess divisibility by T^C proves G_c G_d | G^C. Cancelling the nonzero G_c proves the middle arrow. Since T_c | G_c, division reverses this divisor inclusion inside G^C, and G^C/T_c=T_d E^C proves the last arrow. This construction covers C=0 and s=0 as well.

**Theorem 1.6 (The bounded-weight budget).**

Lean statement: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>=2 and s<r^2, if c(p,j)<=C on the same finite prime-power range, then the actual weighted compact excess E_c divides E^C. The zero system is the second family in the shared-budget theorem. No extra realization hypothesis or assumed valuation formula appears in this statement.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_budget`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.actual_weighted_shared_budget`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_eq_weightedExcess`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedExcess_factorization`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.compactWeightedProduct`
- Dependency: [D5/S3/Arith/FactorialRatio/Compression/SharpLoss](../Compression/SharpLoss.md)
- Dependency: [D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd](CompositionGcd.md)
