# Fixed support and own clock

## Abstract

The exact nonlinear own-clock gap on a fixed prime support.

Let S be any finite set of natural primes with cardinal at least three. Real vectors satisfy x_p>=1 on S. Define theta=sum_S log p, L(x)=sum_S x_p log p, g(L)=log(log L), and Phi(x)=EulerGamma+g(L(x))-sum_S f_p(x_p), with the literal Euler factors of BoundaryPrimePrice. R_S is sInf of the image of this same Phi on this same domain; attainment and uniqueness are not asserted. The canonical reciprocal-log kernel gives lambda=1/(L log L), b_p=max(1,log(1+lambda^-1)/log p-1), T=L(b). T need not equal L.

**Theorem 1.1 (The fixed-support clock domain).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_gt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime bases are at least two. The canonical logarithm lower bound gives log 2>=1/2, so cardinal S>=3 implies theta>1.

**Theorem 1.2 (Every admissible clock lies above theta).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_le_clock`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_le_clock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x_p>=1 on the fixed prime S, theta<=L(x), by positivity of each log p.

**Theorem 1.3 (Every admissible clock exceeds one).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.clock_gt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.clock_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the preceding inequalities pays the iterated-log domain condition for every admissible real vector.

**Theorem 1.4 (The vector's own price is positive).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_price_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_price_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The price is ActualRobinClockCovariance.g evaluated at L(x), definitionally 1/(L(x)*log L(x)), and is strictly positive.

**Theorem 1.5 (The price reference stays in the original real domain).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_boundary_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_boundary_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every b_p=max(1,c_p) is at least one on S. No unsupported prime is inserted, and its clock is the separate value T.

**Theorem 1.6 (A genuine real infimum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_values_nonempty_bdd_below`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_values_nonempty_bdd_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant vector one witnesses nonemptiness. The explicit lower bound EulerGamma+g(theta)+sum_S log(1-p^-1) follows from L>=theta, monotonicity of loglog, and log(1-p^(-x_p-1))<=0. Thus the image is bounded below without assuming the desired rounding theorem.

**Theorem 1.7 (Both conditional-infimum inequalities are paid).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_infimum_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_infimum_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

le_csInf gives the explicit baseline<=R_S; csInf_le gives R_S<=Phi(x) for every admissible x. Both use the actual nonempty bounded image, and the latter is applied to b.

**Theorem 1.8 (Nonlinear terminal correction and its equality case).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.tangent_remainder_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.tangent_remainder_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For L,T>1, H=g(L)+(T-L)/(L log L)-g(T)>=0, and H>0 iff L!=T. The proof directly reuses RestrictedDivisorStrictInventory.loglog_tangent; the L=T case is retained.

**Theorem 1.9 (The exact three-term own-clock identity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_clock_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_clock_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible real x, Phi(x)-R_S=(Phi(b)-R_S)+sum_S J_p(x_p)+[g(L)+lambda*(T-L)-g(T)]. All three terms are nonnegative: b belongs to the infimum domain, BoundaryPrimePrice supplies each real price comparison, and the existing nonlinear tangent gives the last sign. The sum identity retains lambda at x's L while Phi(b) uses T.

**Theorem 1.10 (Every integer vector pays the full finite rounding sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.all_integer_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.all_integer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a:S->Z with a_p>=1, 0<=sum_S d_p(lambda_L)<=Phi(a)-R_S. The scalar attained candidate compares each arbitrary a_p with the actual integer price maximum. No optimality of a, equality T=L, initial support, attained real minimizer or desired lower-bound hypothesis is used. This supplements the existing qualitative allocation theorem uniform_min_tail_robin_lower; it does not duplicate that theorem, fixed-budget KL, or the failure-side optimizer reduction. The explicit six-band prime-count stage remains separate and unpaid.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.all_integer_gap`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.clock_gt_one`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_boundary_admissible`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_clock_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.own_price_pos`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_infimum_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.real_values_nonempty_bdd_below`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.tangent_remainder_nonnegative`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_gt_one`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.theta_le_clock`
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice](BoundaryPrimePrice.md)
