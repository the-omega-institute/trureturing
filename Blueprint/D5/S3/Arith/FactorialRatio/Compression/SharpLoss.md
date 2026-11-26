# Primewise compact excess and shared budgets

## Abstract

Residue bands bound the large-prime compact excess, and a common parameter transfers bounded weights.

Write G(r,s) for the gcd of the compact factorial products and T(r,s)=tailLCM(rs+r-1,r-1). For r>=2 and s<r^2 the exact divisibility T(r,s)|G(r,s) makes their quotient an integer. At a modulus q, the paired floor sum subtracts r-1 from floor((rs+r-1)/q), truncated at zero. The difference is nonnegative at every legal compact parameter.

**Definition 1.1 (All legal compact parameters).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.legalParameters`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.legalParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite family is range(floor(s/r)+1), so b=0 is always included.

**Definition 1.2 (A minimum over the whole legal family).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any natural-valued function f, minimum(r,s,f) is the minimum of its values over all legal b. The legal family is nonempty.

**Theorem 1.3 (The minimum bounds each legal value).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any r,s,b and f, membership of b in legalParameters(r,s) implies minimum(r,s,f)<=f(b).

**Theorem 1.4 (One legal parameter attains the minimum).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all r,s and f, there is a legal b for which f(b)=minimum(r,s,f). The same b evaluates the entire weighted prime-power cost.

**Definition 1.5 (The ordinary excess).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural r and s, compactExcess(r,s) is G(r,s) divided by T(r,s). Under r>=2 and s<r^2 this division is exact.

**Theorem 1.6 (The exponent of the exact quotient).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural r,s,p with r>=2 and s<r^2, the factorization coefficient at p in compactExcess(r,s) equals its coefficient in G(r,s) minus its coefficient in T(r,s). The exact divisibility T(r,s)|G(r,s) makes this the actual nonnegative difference. This identity connects the local floor estimates to the integer quotient.

**Definition 1.7 (The defect at one modulus).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.floorDefect`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.floorDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural q,r,s,b, floorDefect(q,r,s,b) is the sum over 0<=i<r of floor((i+1)b/q)+floor((s-ib)/q)-floor(b/q), minus max(floor((rs+r-1)/q)-(r-1),0), with natural subtraction. For q>=2, r>=1 and rb<=s the lower floor bound makes this the actual nonnegative integer difference.

**Theorem 1.8 (The large-prime local bound).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.local_prime_excess_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.local_prime_excess_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural r,s,p,k with r>=2, s<r^2, p prime, r<p, 1<=k and kp<=s, the exponent of p in compactExcess(r,s) is at most 2k+2r^2/(kp), interpreted as a real bound. Thus every integer k in the interval 1<=k<=floor(s/p) supplies a valid upper bound.

Choose b=floor(kp/r). Then 0<b<p, rb<=s, and 0<kp-rb<r. The strict lower inequality follows from coprimality of p and r and 0<k<r. The points ib, for 1<=i<=r, occupy at most k quotient bands modulo p. Inside a fixed band, marks with residue at most u are separated by b, so there are at most floor(u/b)+1 marks.

Put v=s mod p. If v+b<p, the floor sum equals r(floor(s/p)-1) plus the number of marks with residue at most v+b. The band count bounds its defect by 2k+r/b. If v+b>=p, the new marked interval has length v+b-p<b, so it contains at most one mark per band; the defect is at most 2k. Finally kp<=2rb gives r/b<=2r^2/(kp). Since s<p^2, higher powers of p contribute zero.

**Definition 1.9 (A common parameter across prime powers).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedPrimeLoss`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedPrimeLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural r,s,p,K and nonnegative integer weights c(j), weightedPrimeLoss is the minimum, over 0<=b<=floor(s/r), of the sum of c(j)floorDefect(p^j,r,s,b) for 1<=j<K. The same b is used in every summand. With unit weights and K=log_p(s)+1, this minimum equals the exponent of p in the ordinary excess when r>=2, s<r^2 and p is prime.

**Definition 1.10 (A finite product of weighted prime losses).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedExcess`

*Formalization.* `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural r,s, a finite set P and nonnegative integer weights c(p,j), weightedExcess is the product over p in P of p raised to weightedPrimeLoss(r,s,p,log_p(s)+1,c(p,-)). For a weighted factorial model, identifying this product with its compact gcd divided by its full-composition gcd requires the corresponding primewise valuation formulas.

**Theorem 1.11 (A shared bound for two weight systems).**

Lean statement: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weighted_shared_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weighted_shared_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r>=2, s<r^2 and let P be any finite set of primes. For natural C and natural weights c(p,j),d(p,j), assume c(p,j)+d(p,j)<=C for p in P and 1<=j<=log_p(s). Then weightedExcess(r,s,P,c) times weightedExcess(r,s,P,d) divides compactExcess(r,s)^C. Taking d=0 yields the bounded-weight divisibility for a single system.

For each p, choose a parameter minimizing the unweighted sum of nonnegative defects. Evaluate both weighted sums at this same parameter. Their sum is at most C times the unweighted sum, while each separate minimum is at most its value there. This proves the inequality between exponents. Products over the finite prime set give the divisibility. The argument also covers C=0, empty P, and an empty interval of positive prime powers.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.compactExcess_factorization`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.floorDefect`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.legalParameters`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.local_prime_excess_bound`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_attained`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.minimum_le`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedExcess`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weightedPrimeLoss`
- Truth anchor: `D5/S3/Arith/FactorialRatio/Compression/SharpLoss.weighted_shared_budget`
- Dependency: [D5/S3/Arith/FactorialRatio/CompactFactorialGcd](../CompactFactorialGcd.md)
