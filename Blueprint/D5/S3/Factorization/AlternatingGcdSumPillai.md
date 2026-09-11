# Bala's Alternating Gcd Sum

## Abstract

Bala's alternating gcd sum equals the floor-square totient sequence A344598.

The conjecture recorded in bala2024a344598 identifies OEIS A344598 with an alternating gcd sum at every positive index. The note also records the separate attribution of the divisor-sum formulas to Daniel Weber. The identity follows by relating both sums to Pillai's function.

All indices are natural numbers. The functions a and pillai take natural-number values; altGcdSum takes integer values. The symbol div denotes natural-number integer division. All subtraction in the definition of a is truncated natural subtraction. The function toInt is the canonical embedding of a natural number into the integers. Subtraction in the subsequent theorem formulas is integer subtraction.

**Definition 1.1 (The floor-square totient sequence).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{Icc}\left(1, n\right)} (\operatorname{totient}\left(k\right) \cdot (\operatorname{div}\left(n, k\right)^{2} - \operatorname{div}\left((n - 1), k\right)^{2}))$$

*Formalization.* `D5/S3/Factorization/AlternatingGcdSumPillai.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the defining sum of A344598. The function totient is Euler's totient function, and Icc(1,n) includes both endpoints.

**Definition 1.2 (Pillai's function).**

$$\forall n \in \mathbb{N}, \operatorname{pillai}\left(n\right) = \sum_{k \in \operatorname{Icc}\left(1, n\right)} (\operatorname{gcd}\left(k, n\right))$$

*Formalization.* `D5/S3/Factorization/AlternatingGcdSumPillai.pillai` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each positive integer k at most n contributes gcd(k,n).

**Definition 1.3 (The alternating half-sum).**

$$\forall n \in \mathbb{N}, \operatorname{altGcdSum}\left(n\right) = \sum_{k \in \operatorname{Icc}\left(1, 2 \cdot n\right)} ((-1)^{k} \cdot \operatorname{toInt}\left(\operatorname{gcd}\left(k, 4 \cdot n\right)\right))$$

*Formalization.* `D5/S3/Factorization/AlternatingGcdSumPillai.altGcdSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alternating signs and the gcd values are multiplied and summed in the integers over k from one through 2n.

**Theorem 1.4 (The totient sum in terms of Pillai's function).**

$$\forall n \in \mathbb{N}, 1 \le n \implies \operatorname{toInt}\left(\operatorname{a}\left(n\right)\right) = 2 \cdot \operatorname{toInt}\left(\operatorname{pillai}\left(n\right)\right) - \operatorname{toInt}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/AlternatingGcdSumPillai.a_eq_two_pillai_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient square changes only when k divides n; its increment is 2 div(n,k)-1. Grouping the gcd sum by its gcd fibres uses Mathlib's totient_div_of_dvd. Reindexing complementary divisors gives the totient-weighted quotient sum, and sum_totient supplies the subtracted n.

**Theorem 1.5 (The doubling identity).**

$$\forall n \in \mathbb{N}, \operatorname{pillai}\left(4 \cdot n\right) + 4 \cdot \operatorname{pillai}\left(n\right) = 4 \cdot \operatorname{pillai}\left(2 \cdot n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/AlternatingGcdSumPillai.pillai_four_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality is in the natural numbers and includes n=0. Even indices contribute twice the smaller gcd sum. For odd indices, coprimality with two removes the extra factor two from the modulus. Splitting the odd-index sum into two blocks of length n gives two equal sums, which yields the displayed identity.

**Theorem 1.6 (Reflection and endpoint terms).**

$$\forall n \in \mathbb{N}, 1 \le n \implies 2 \cdot \operatorname{altGcdSum}\left(n\right) + 2 \cdot \operatorname{toInt}\left(n\right) = 4 \cdot \operatorname{toInt}\left(\operatorname{pillai}\left(2 \cdot n\right)\right) - \operatorname{toInt}\left(\operatorname{pillai}\left(4 \cdot n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/AlternatingGcdSumPillai.altGcdSum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection k to 4n-k preserves the sign and gcd. In the half-open range from zero to 2n, replacing zero by 2n changes the sum by 2n, since the endpoint values are 4n and 2n. The reflected upper half equals altGcdSum(n). Splitting the full sum by parity gives 4 pillai(2n)-pillai(4n), including exactly the displayed endpoint term.

**Theorem 1.7 (Bala's conjectured formula).**

$$\forall n \in \mathbb{N}, 1 \le n \implies \operatorname{toInt}\left(\operatorname{a}\left(n\right)\right) = \operatorname{altGcdSum}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/AlternatingGcdSumPillai.bala_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a344598-alternating-gcd-sum-pillai` (proved) by `D5/S3/Factorization/AlternatingGcdSumPillai.bala_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a344598-alternating-gcd-sum-pillai","declaration_gid":"D5/S3/Factorization/AlternatingGcdSumPillai.bala_conjecture","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2024). *OEIS A344598, conjectured alternating gcd-sum formula*. URL: <https://oeis.org/A344598>.

*Commentary.*

The doubling identity and reflection identity imply altGcdSum(n)=2 pillai(n)-n. The totient identity gives the same integer for a(n), proving the conjectured formula for every positive n.

## References

- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.a`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.a_eq_two_pillai_sub`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.altGcdSum`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.altGcdSum_eq`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.bala_conjecture`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.pillai`
- Truth anchor: `D5/S3/Factorization/AlternatingGcdSumPillai.pillai_four_mul`
