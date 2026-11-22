# Norton thresholds and the reciprocal-square perturbation

## Abstract

The difference between Norton and KS strict threshold lengths tends to infinity.

Prime enumeration reuses D5/S3/Arith/OmegaGreedyPermutation.prime, the zero-based Nat.nth Nat.Prime enumeration with prime(0)=2. The source's p_n is prime(n-1). Euler factors reuse D5/S3/Arith/Robin/GoldenResidualFive.eulerFactor, whose value at a natural q is q/(q-1), with real subtraction. Weight bounds reuse ZelinskyZhangDoublePrimitive.log_bounds.

**Definition 1.1 (The perturbed Euler factor).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksFactor`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksFactor` (`✓ std3`).

*Citation.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every natural q, ksFactor(q) is eulerFactor(q)+1/q^2, with real arithmetic. For a prime q this is the factor in Beri and Zelinsky's definition of KS.

**Definition 1.2 (The logarithmic Euler weight).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.weight`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every natural q, weight(q) is log(eulerFactor(q)), using the real logarithm. For prime q, it lies between 1/q and 2/q. Positivity of prime Euler factors makes logarithms preserve their strict crossings.

**Definition 1.3 (The logarithmic perturbation).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.perturbation`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.perturbation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every natural q, perturbation(q) is log(1+(q-1)/q^3), with real arithmetic. For prime q, log(ksFactor(q)) equals weight(q)+perturbation(q), and the perturbation lies between 1/(4*q^2) and 1/q^2.

**Definition 1.4 (Consecutive Norton factors).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.nortonProduct`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.nortonProduct` (`✓ std3`).

*Citation.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For natural n and k, put s=n-1 using natural subtraction. nortonProduct(n,k) is the product of eulerFactor(prime(i)) over s<=i<s+k. When n>=1 this is the product over the source's primes p_n through p_(n+k-1). The product for k=0 is one. The value at n=0 uses the same starting prime as n=1.

**Definition 1.5 (Consecutive perturbed factors).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksProduct`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksProduct` (`✓ std3`).

*Citation.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For natural n and k, ksProduct(n,k) is the product of ksFactor(prime(i)) over n-1<=i<n-1+k, with natural subtraction in the starting index. It is the source's perturbed product for n>=1, and its empty product is one.

**Definition 1.6 (The strict threshold at alpha).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.aAlpha`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.aAlpha` (`✓ std3`).

*Citation.* J. Zelinsky (2023). *On the small prime factors of a non-deficient number*. URL: <https://math.colgate.edu/~integers/x13/x13.pdf>.

*Commentary.*

For every real alpha and natural n, aAlpha(alpha,n) is the infimum in the natural numbers of the positive lengths k such that nortonProduct(n,k)>alpha. Prime reciprocal divergence makes this set nonempty, so the infimum is its least member. The endpoint estimates and difference conclusions assume alpha>1.

**Definition 1.7 (Norton's threshold at two).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.a`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.a` (`✓ std3`).

*Citation.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every natural n, a(n) is aAlpha(2,n), the least positive number of consecutive prime Euler factors, starting at p_n for n>=1, whose product strictly exceeds two.

**Definition 1.8 (The KS threshold at two).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.KS`

*Formalization.* `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.KS` (`✓ std3`).

*Citation.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every natural n, KS(n) is the least positive natural k such that ksProduct(n,k)>2. The larger factors guarantee existence and KS(n)<=a(n). The strict inequality defining the crossing is part of the definition.

**Theorem 1.9 (The terminal prime has the alpha power scale).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_endpoint_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_endpoint_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every real alpha>1 there are positive real constants c and C such that, for all sufficiently large natural n, the final prime Q_n in the product of length aAlpha(alpha,n) satisfies c*p_n^alpha <= Q_n <= C*p_n^alpha. Precisely, p_n=prime(n-1) and Q_n=prime(n-1+aAlpha(alpha,n)-1).

The Mertens logarithmic Euler-product error is bounded by a constant divided by log(p_n). The first strict crossing exceeds log(alpha) by at most the final logarithmic weight. Subtracting prefix estimates gives log(Q_n)=alpha*log(p_n) plus a bounded error, which yields the two power bounds.

**Theorem 1.10 (Adjacent starting indices force large differences).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_adjacent_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_adjacent_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

For every real alpha>1 there is a positive real constant c such that, for all sufficiently large natural n, c*p_n^(alpha-1) is at most aAlpha(alpha,n+1)-aAlpha(alpha,n)+1, where the threshold lengths on the right are cast separately to the reals.

Subtracting the two crossing sums cancels their common prime interval. The remaining sum is the initial weight w(p_n) plus the difference of the two crossing excesses. Endpoint localization makes the excesses negligible compared with 1/p_n, while each new upper-end weight is at most a constant times p_n^(-alpha). Their number is one plus the difference of the threshold lengths.

**Theorem 1.11 (Question 6 has an affirmative answer).**

Lean statement: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result` (`✓ std3`). ∎

*Resolves.* `Problems/norton-threshold-differences` (proved) by `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"norton-threshold-differences","declaration_gid":"D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Beri and Zelinsky (2025). *arXiv:2505.08160v2, Question 6 on Norton and KS thresholds*. DOI: [10.48550/arXiv.2505.08160](https://doi.org/10.48550/arXiv.2505.08160). URL: <https://arxiv.org/abs/2505.08160v2>.

*Commentary.*

As the natural starting index n tends to infinity, the integer a(n)-KS(n) tends to positive infinity. Both natural threshold lengths are cast to the integers before subtraction.

Write A and B for the terminal primes of the Norton and KS crossings, and P for p_n. Both terminal primes are bounded above and below by positive constant multiples of P^2. The accumulated perturbation through B has a positive lower bound of order 1/(P*log(P)), using the finite prime reciprocal-square tail estimate. Subtracting the crossing identities leaves the ordinary weights between B and A, with crossing errors of order P^(-2). Each intervening weight is at most a constant times P^(-2), forcing the number of omitted primes to grow without bound.

This is the limit in Beri and Zelinsky's Question 6. It does not assert an exact asymptotic equivalence for a(n)-KS(n), or strict a(n)>KS(n) at every positive starting index.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.KS`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.a`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.aAlpha`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksFactor`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.ksProduct`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.nortonProduct`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_adjacent_cancellation`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.norton_endpoint_bounds`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.perturbation`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result`
- Truth anchor: `D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.weight`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive](ZelinskyZhangDoublePrimitive.md)
- Dependency: [D5/S3/Arith/OmegaGreedyPermutation](../OmegaGreedyPermutation.md)
- Dependency: [D5/S3/Arith/Robin/GoldenResidualFive](../Robin/GoldenResidualFive.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail](../Robin/PriceRecord/PrimeSquareTail.md)
