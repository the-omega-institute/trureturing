# Zelinsky and Zhang's Conjecture 15

## Abstract

There are infinitely many positive deficient KL-primitive integers.

**Definition 1.1 (The logarithmic divisor sum).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KL`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KL` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

Equation (6) defines KL(n) as the sum over positive divisors d of n of d log(d/(2 phi(d))). Quotients and logarithms are real. The value at one is minus log 2.

**Definition 1.2 (KL primitivity).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KLPrimitive`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KLPrimitive` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

Definition 1 on page twelve requires KL(n) to be nonnegative and KL(d) to be strictly negative for every positive proper divisor d of n.

**Definition 1.3 (Deficiency).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.Deficient`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.Deficient` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

An integer n is deficient when its sum of positive divisors is strictly smaller than 2n.

**Theorem 1.4 (Bounds for the logarithmic prime increment).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.f_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.f_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every natural p at least two, f(p)=p/(p+1)*log(p/(p-1)) satisfies 2/(3p)<=f(p)<=2/p and 0<f(p)<log(2). These estimates compare finite prime-tail sums with reciprocal-prime sums.

**Theorem 1.5 (Arbitrarily large finite prime-tail mass).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.tail_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.tail_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every pair of natural numbers Q and k, there is a finite set of primes exceeding Q whose f sum is at least k/3. In particular the increment upper bound converts the choice k=6 into reciprocal mass at least one.

**Theorem 1.6 (Positive divisors preserve deficiency).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.deficient_of_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.deficient_of_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

If d and n are positive natural numbers, d divides n, and n is deficient, then d is deficient. This follows from monotonicity of sigma(n)/n under divisibility and transfers the bounds on products with one prime removed to all proper divisors.

**Theorem 1.7 (Exponential threshold control at quadratic logarithmic cost).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.rough_deficient_core`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.rough_deficient_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

Fix any natural cutoff B. There are constants K>0 and T such that for every real t at least T there is a finite set S of primes exceeding B. Put h=product over p in S of (1+1/p) and a=h/(2-h). Then h<2, exp(t)<=a<=3*exp(t), every p in S is less than 2a, and the sum of log(p) over S is at most K*t^2. Distinctness of the prime factors makes their product squarefree, and its abundancy ratio is h.

Divergence of the reciprocal-prime sum supplies a finite prime product with h at least 2. A minimal crossing set, with its largest prime removed, gives a deficient starting core whose threshold parameter exceeds its prime factors.

For a large current parameter a, choose a prime p in (2a,3a]. Adjoining p keeps the core deficient and replaces a by a*(p+1)/(p-a), which lies between 3a/2 and 3a. All old and new prime factors remain below twice the new parameter. The first iteration to reach exp(t) therefore has parameter at most 3*exp(t). The number of iterations is linear in t, and each added prime has logarithm bounded linearly in that iteration's index, giving the quadratic total cost.

These deficient cores supply the initial factors for the lower bound on primitive non-deficient integers.

**Theorem 1.8 (Infinitely many deficient KL-primitive integers).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-zhang-2025-conjecture-15` (proved) by `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-zhang-2025-conjecture-15","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every natural bound B there is a positive integer n greater than B that is deficient and KL-primitive. This is the infinitude assertion of Conjecture 15.

On a product of distinct primes, KL(n)/sigma(n) plus log 2 is the sum of f(p) = p/(p+1) log(p/(p-1)). The logarithm of sigma(n)/n is the sum of g(p) = log(1+1/p). StrictGibbs.kl_divergence_pos_of_ne applied to the distinct two-point distributions P = (1/(p+1), p/(p+1)) and Q = (1/p, (p-1)/p) gives g(p) < f(p), since their KL divergence is f(p)-g(p). The Euler logarithm upper bound is FibonacciRankEulerTail.euler_log_bounds. The bounds 2/(3p) <= f(p) <= 2/p give arbitrarily small positive increments with unbounded finite tail sums.

Choose one prime beyond B and two, retaining half its positive difference f(p)-g(p). Add distant primes until the f sum first reaches log 2, with each increment smaller than this reserve. The resulting product has nonnegative KL and is deficient. Its smallest positive divisor with nonnegative KL is KL-primitive. Deficiency passes to divisors by GA2ForcedPrimeSource.abundancy_mono. All prime factors still exceed B, and the chosen divisor cannot be one, so it exceeds B.

The odd squarefree strengthening follows from the same construction on paper. The present conclusion does not require that strengthening and does not settle the question about primitive non-deficient integers.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.Deficient`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KL`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.KLPrimitive`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.deficient_of_dvd`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.f_bounds`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.rough_deficient_core`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.tail_mass`
- Dependency: [D5/S3/Arith/Robin/FibonacciRankEulerTail](../Robin/FibonacciRankEulerTail.md)
- Dependency: [D5/S3/Arith/Robin/GA2ForcedPrimeSource](../Robin/GA2ForcedPrimeSource.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](../Robin/PriceRecord/FixedLayerRigidity.md)
- Dependency: [D5/S3/Divergence/StrictGibbs](../../Divergence/StrictGibbs.md)
- Dependency: [D5/S3/Factorization/ReciprocalSigmaThreshold](../../Factorization/ReciprocalSigmaThreshold.md)
