# Fixed Finite Prime-Block Negligibility

## Abstract

Every fixed finite prime block contributes o(1/P) uniformly over actual positive-price predecessor records.

**Theorem 1.1 (Uniform negligibility of a fixed finite block).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FiniteBlockNegligibility.price_record_finite_prime_block_negligible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FiniteBlockNegligibility.price_record_finite_prime_block_negligible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any finite set S of primes, including the empty set, and any real epsilon>0. A positive threshold T depends only on S and epsilon. For every natural m>=2 and every positive price lambda, if F_lambda(n)<F_lambda(m) for every positive natural n<m, then T<=P=largestPrime(m) implies P times the sum over p in S of layerTail(m,p) is less than epsilon. Here F_lambda(n)=log(sigma(n)/n)-lambda*log(n), and layerTail(m,p)=-log(1-p^(-(v_p(m)+1))). The quantifier order makes T uniform over all these records and prices.

Choose one fixed natural j>=2 with 4/j<epsilon before choosing any record. Put Q=product of the primes in S, with Q=1 for the empty block. Fixed-layer rigidity at tolerance j/2 supplies T_j. Increase the threshold to max(T_j,2 Q^j/j). For q=layerPrime(m,j), rigidity gives q^j/P>j/2 and hence q^j>Q^j, so q>Q>=1. The finite maximum defining the cutoff is therefore attained at an actual prime divisor q of the same m, with a=v_q(m)>=j.

Apply the single predecessor prime-block exchange to this donor q and the whole set S with k=1. It removes one copy of q and inserts one copy of each prime in S in a single predecessor, paying the donor only once. Since q>Q and lambda>0, the signed price contribution lambda(log q-log Q) is positive. Each tail is nonnegative and each weight 1-1/p is at least 1/2. The exchange therefore bounds half the unweighted tail sum strictly by gain(q,a). Marginal decay gives gain(q,a)<=q^(-a)<=q^(-j), so the sum is less than 2/q^j and its product with P is less than 4/j<epsilon. No equality a=j or adjacent-layer estimate is required. The same argument includes S empty.

Nonnegativity of the tails turns the one-sided bound into absolute smallness: every fixed finite block is uniformly o(1/P) as P tends to infinity within this record class. In particular, for S={2,3,5,7}, the 5040 support block D4 is o(1/P). This is an application of the finite-set theorem, with no separate named Lean specialization.

This general asymptotic statement has no computational instance. Its assumptions do not require colossal abundance, global optimality, price localization, or an additional occupied cutoff. It gives no uniform estimate for S growing with P, complete Euler tail estimate, exponent envelope, signed prime-error control, or Riemann-hypothesis conclusion. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FiniteBlockNegligibility.price_record_finite_prime_block_negligible`
- Dependency: [D5/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail](../../ExponentExchange/PriceRecordPrimeBlockTail.md)
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](../../GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](FixedLayerRigidity.md)
