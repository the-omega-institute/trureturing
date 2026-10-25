# Eventual Jordan-Cototient Records

## Abstract

Eventual strict Jordan-cototient records are exactly one and the even naturals.

**Definition 1.1 (The real-parameter Jordan totient).**

$$\forall k \in \mathbb{R}, n \in \mathbb{N},\; \operatorname{J}\left(k, n\right) = \operatorname{val}\left(n\right)^{k} \cdot \prod_{p \in \operatorname{primeFactors}\left(n\right)} (1 - \operatorname{val}\left(p\right)^{-k})$$

*Formalization.* `D5/S3/Factorization/JordanCototientRecordLimitInfinity.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real parameter k and a natural number n, J(k,n) is exactly n^k times the product over p in primeFactors(n) of 1-p^(-k). The function val shown in the formula is the coercion from natural numbers to real numbers. This is the definition stated in the OEIS A004277 comment.

**Definition 1.2 (The Jordan cototient).**

$$\forall k \in \mathbb{R}, n \in \mathbb{N},\; \operatorname{CoJ}\left(k, n\right) = \operatorname{val}\left(n\right)^{k} - \operatorname{J}\left(k, n\right)$$

*Formalization.* `D5/S3/Factorization/JordanCototientRecordLimitInfinity.CoJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real k and natural n, CoJ(k,n) is defined exactly as the real power n^k minus J(k,n), matching the OEIS source comment.

**Definition 1.3 (Strict records among positive predecessors).**

$$\forall k \in \mathbb{R}, n \in \mathbb{N},\; \operatorname{StrictRecord}\left(k, n\right) \Leftrightarrow \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(m < n \Rightarrow \operatorname{CoJ}\left(k, m\right) < \operatorname{CoJ}\left(k, n\right)\right)\right)$$

*Formalization.* `D5/S3/Factorization/JordanCototientRecordLimitInfinity.StrictRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

StrictRecord(k,n) means that every natural predecessor m with 1 <= m and m < n has strictly smaller Jordan cototient at the same parameter k.

**Lemma 1.4 (A finite-product union bound).**

$$\forall I \in Type,\; [\operatorname{LinearOrder}\left(I\right)] \forall s \in \operatorname{Finset}\left(I\right), x \in I \to \mathbb{R},\; \left(\forall i \in I,\; i \in s \Rightarrow \left(0 \le x\left(i\right) \land x\left(i\right) \le 1\right)\right) \Rightarrow 1 - \prod_{i \in s} (1 - x\left(i\right)) \le \sum_{i \in s} x\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.one_sub_prod_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite subset s of a linearly ordered type and real factors x(i) between zero and one, one minus the product of 1-x(i) is at most the sum of x(i). This bounds finite Euler products and geometric partial products.

**Lemma 1.5 (The minimum-prime-factor lower bound).**

$$\forall k \in \mathbb{R}, n \in \mathbb{N},\; 0 < k \Rightarrow \left(1 < n \Rightarrow \operatorname{val}\left(\operatorname{Nat.div}\left(n, \operatorname{minFac}\left(n\right)\right)\right)^{k} \le \operatorname{CoJ}\left(k, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k > 0 and n > 1, the k-th real power of the natural Euclidean quotient Nat.div(n,minFac(n)) is at most CoJ(k,n). Nat.div is the integer quotient before the displayed real coercion; it is not field division. The proof singles out the minFac(n) term in the finite Euler product.

**Lemma 1.6 (The minimum-prime-factor upper bound).**

$$\forall k \in \mathbb{R}, n \in \mathbb{N},\; 0 < k \Rightarrow \left(1 < n \Rightarrow \operatorname{CoJ}\left(k, n\right) \le \operatorname{val}\left(\operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right)\right) \cdot \operatorname{val}\left(\operatorname{Nat.div}\left(n, \operatorname{minFac}\left(n\right)\right)\right)^{k}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k > 0 and n > 1, CoJ(k,n) is at most the real coercion of the number of distinct prime factors times the k-th power of Nat.div(n,minFac(n)). Nat.div again denotes natural Euclidean division. A finite-product union bound compares every reciprocal prime scale with the minimum-prime-factor scale.

**Lemma 1.7 (Prime inputs have cototient one).**

$$\forall p \in \mathbb{N}, k \in \mathbb{R},\; \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{CoJ}\left(k, p\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural prime p has CoJ(k,p)=1 for every real k. This evaluation is consumed by the two-versus-three tie in not_strictRecord_three.

**Lemma 1.8 (The cototient of one vanishes).**

$$\forall k \in \mathbb{R},\; \operatorname{CoJ}\left(k, 1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real k, CoJ(k,1)=0 because primeFactors(1) is empty. This evaluation supplies the m=1 predecessor case in the even record theorem.

**Theorem 1.9 (Every positive even input is eventually a strict record).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \left(\exists K \in \mathbb{R},\; \forall k \in \mathbb{R},\; k > K \Rightarrow \operatorname{StrictRecord}\left(k, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.eventual_strictRecord_of_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If n is positive and even, there is a real threshold K after which n is a strict record. The proof combines the two cototient bounds with the strict base gap m/minFac(m) <= m/2 < n/2 and real exponential domination. Each slash in this prose is real division after coercion, whereas the Lean bounds themselves use the named Nat.div quotient.

**Theorem 1.10 (Odd inputs at least five eventually lose to their predecessor).**

$$\forall n \in \mathbb{N},\; 5 \le n \Rightarrow \left(\left(\neg \operatorname{Even}\left(n\right)\right) \Rightarrow \left(\exists K \in \mathbb{R},\; \forall k \in \mathbb{R},\; k > K \Rightarrow \operatorname{CoJ}\left(k, n\right) < \operatorname{CoJ}\left(k, \operatorname{Nat.sub}\left(n, 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.eventual_loses_to_predecessor_of_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If n is odd and at least five, a real threshold K makes CoJ(k,n) smaller than CoJ(k,Nat.sub(n,1)) for every k > K. Nat.sub is truncated natural subtraction. The proof uses n/minFac(n) <= n/3 < (n-1)/2 and the same real exponential-domination lemma.

**Lemma 1.11 (Three is never a strict record).**

$$\forall k \in \mathbb{R},\; \neg \operatorname{StrictRecord}\left(k, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.not_strictRecord_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real k, three is not a strict record: the preceding prime-value lemma gives CoJ(k,2)=CoJ(k,3)=1, so the required strict predecessor inequality is impossible.

**Theorem 1.12 (The eventual record set is one together with the even naturals).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left((\exists K \in \mathbb{R},\; \forall k \in \mathbb{R},\; k > K \Rightarrow \operatorname{StrictRecord}\left(k, n\right)) \Leftrightarrow (n = 1 \lor \operatorname{Even}\left(n\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/JordanCototientRecordLimitInfinity.a004277_eventual_record_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n >= 1, there exists a real threshold K after which n is always a strict Jordan-cototient record exactly when n=1 or n is even. The threshold is chosen separately for each n; no uniform threshold over all even inputs is asserted.

The forward direction excludes three by the prime tie and every odd n >= 5 by its eventual loss to Nat.sub(n,1). The reverse direction is vacuous at one and uses the even-input theorem otherwise. Thus the two-sided min-factor estimates remain in the derivation to the final characterization.

## References

- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.CoJ`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.J`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.StrictRecord`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.a004277_eventual_record_iff`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_lower_bound`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_one`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_prime`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.coJ_upper_bound`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.eventual_loses_to_predecessor_of_odd`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.eventual_strictRecord_of_even`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.not_strictRecord_three`
- Truth anchor: `D5/S3/Factorization/JordanCototientRecordLimitInfinity.one_sub_prod_le_sum`
