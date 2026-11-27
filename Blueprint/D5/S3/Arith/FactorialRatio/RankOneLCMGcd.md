# Factorial gcd and multinomial lcm for rank-one windows

## Abstract

Exact factorial-product gcd and multinomial-coefficient lcm identities for LCM windows.

The problem is motivated by an Alpoge-inspired rank-one window calculation. The identities and primewise minimizing construction follow a GPT Pro derivation. Their priority in the external literature is unverified. Let L(n) denote the least common multiple of the integers from 1 through n, with L(0)=1. For natural H and M with M at most H, let S be the finite set of all ordered (M+1)-tuples of natural numbers with sum H-M.

**Definition 1.1 (Tail product).**

Lean statement: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM`

*Formalization.* `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of L(floor(H/k)) over the integers M<k<=H. An empty product equals one.

**Definition 1.2 (Prefix product).**

Lean statement: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM`

*Formalization.* `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of L(floor(H/k)) over the integers 1<=k<=M.

**Definition 1.3 (Factorial product).**

Lean statement: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.factorialProduct`

*Formalization.* `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.factorialProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple a of any finite length r, the product of a(i)! over its r entries.

**Theorem 1.4 (The exact gcd of factorial products).**

Lean statement: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM_eq_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM_eq_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural H and M with M<=H, tailLCM(H,M) equals the gcd of factorialProduct(a) over all a in S. For each prime p, every tuple has factorial valuation at least the valuation of the tail product, and a tuple attaining that minimum exists for each p. Write u=H-M. The smallest achievable sum of quotients floor(a(i)/p) is max(0, floor((u+M)/p)-M). Each tuple of this smaller sum lifts by remainders from 0 through p-1 to a tuple of the original sum. Strong induction on u therefore gives the same recurrence for minimum factorial valuation and the sum of the base-p logarithms of floor(H/k) over M<k<=H.

For H=8 and M=2, the unordered triples of sum six produce factorial products 720, 120, 48, 24, 36, 12 and 8. Their gcd is 4, which is attained by none of the triples. The minimum valuation of two is attained by (3,3,0) and that of three by (2,2,2). Thus the prime-specific witnesses need not constitute a single composition with the gcd as its factorial product.

**Theorem 1.5 (The exact lcm of multinomial coefficients).**

Lean statement: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM_eq_factorial_ratio_mul_multinomial_lcm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM_eq_factorial_ratio_mul_multinomial_lcm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural H and M with M<=H, prefixLCM(H,M) equals H!/(H-M)! multiplied by the lcm over a in S of the multinomial coefficient (H-M)!/factorialProduct(a). The factorial ratio is exact in natural arithmetic. Every factorial product times its multinomial coefficient equals (H-M)!. Finite gcd and lcm divisibility thus give tailLCM(H,M) times the multinomial lcm equal to (H-M)!. The prefix and tail products together equal H!, by applying the gcd identity at M=0 and splitting the interval. Cancellation of the positive tail product proves the formula.

For H=8 and M=2, the multinomial lcm is 180 and the factorial ratio is 56, giving the prefix product 10080. Both identities include M=0, M=H and H=M=0. At M=0 the tail is H! and the prefix is one. At M=H the tail is one and the prefix is H!.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.factorialProduct`
- Truth anchor: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM`
- Truth anchor: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.prefixLCM_eq_factorial_ratio_mul_multinomial_lcm`
- Truth anchor: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM`
- Truth anchor: `D5/S3/Arith/FactorialRatio/RankOneLCMGcd.tailLCM_eq_gcd`
