# Arbitrarily high simultaneous sigma peaks

## Abstract

Primorial divisor sums dominate both adjacent divisor sums by any prescribed factor.

**Definition 1.1 (The exact OEIS conjecture).**

$$\forall n: \mathbb{N}, \exists k: \mathbb{N}, 2 \le k \land \left(n \cdot \operatorname{sigma}\left(1, k - 1\right) < \operatorname{sigma}\left(1, k\right) \land n \cdot \operatorname{sigma}\left(1, k + 1\right) < \operatorname{sigma}\left(1, k\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/SigmaNeighbourPeak.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ratushnyak's OEIS A397578 defines a(n) as the least k for which sigma(k) exceeds n times each of sigma(k-1) and sigma(k+1). Here sigma means the sum of positive divisors, sigma(1,k) in Lean. The claim includes all natural n, requires k >= 2, and uses strict inequalities on both sides. Natural subtraction is truncated, but the lower bound on k makes k-1 positive. Existence implies the least such k exists by well-ordering.

**Theorem 1.2 (Every factor is attained).**

$$\forall n: \mathbb{N}, \exists k: \mathbb{N}, 2 \le k \land \left(n \cdot \operatorname{sigma}\left(1, k - 1\right) < \operatorname{sigma}\left(1, k\right) \land n \cdot \operatorname{sigma}\left(1, k + 1\right) < \operatorname{sigma}\left(1, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/SigmaNeighbourPeak.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397578-sigma-neighbour-peaks` (proved) by `D5/S3/Arith/Robin/SigmaNeighbourPeak.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397578-sigma-neighbour-peaks","declaration_gid":"D5/S3/Arith/Robin/SigmaNeighbourPeak.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Set P = primorial(x), the product of primes at most x, with x >= 4. The existing reciprocal_divisor_sum identity identifies sigma(P)/P with the sum of reciprocal divisors. Each prime at most x is a divisor; divergence of the prime reciprocal series therefore gives an x with sigma(P) > 6nP. Neither P-1 nor P+1 has a prime factor at most x. For either neighbour m, the product of its distinct prime factors divides m, so 4^omega(m) <= m <= 4^x+1 < 4^(x+1), giving omega(m) <= x. The finite prime-power geometric sums give sigma(m)/m <= product over p dividing m of p/(p-1). Each factor is at most 1+1/x. Consequently sigma(m)/m <= (1+1/x)^x <= e < 3. Combining these estimates proves both inequalities, including n=0. This is an unbounded existence proof with a primorial witness; it does not bound the least witness's growth or characterize it as highly abundant.

## References

- Truth anchor: `D5/S3/Arith/Robin/SigmaNeighbourPeak.claim`
- Truth anchor: `D5/S3/Arith/Robin/SigmaNeighbourPeak.result`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../GoldenResourceOptimalInteger.md)
