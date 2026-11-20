# Zelinsky and Zhang's Question 1

## Abstract

Infinitely many positive integers are primitive non-deficient and KL-primitive.

**Definition 1.1 (Primitive non-deficiency).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient` (`✓ std3`).

*Citation.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

On page two, a primitive non-deficient integer is non-deficient and has no non-deficient positive proper divisor. Thus sigma(n) is at least 2n, while sigma(d) is strictly less than 2d for each positive divisor d less than n. The predicate uses the existing definition of deficiency.

**Theorem 1.2 (A uniform eventual exponent of 79/80).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

For every finite set M of primes there is a natural threshold X0 such that, for every natural X at least X0, at least X^(79/80) positive integers n at most X are odd, squarefree, primitive non-deficient, and divisible by no prime in M. The finite set may be empty. Primitive non-deficiency means that sigma(n) is at least 2n and sigma(d) is strictly less than 2d for every positive proper divisor d of n.

Write h(m)=sigma(m)/m and alpha=h(m)/(2-h(m)) for a deficient squarefree core. A finite prime product first crossing h=2 gives an initial deficient core. Adjoining primes between 2alpha and 3alpha increases alpha by a fixed multiplicative factor while retaining deficiency. Thus alpha can reach a prescribed exponential scale with log(m) bounded by a constant times the square of that scale's logarithm.

Choose k distinct primes in the interval ((k-1)(alpha+1),k*alpha]. Their product times the core is abundant by the strict Bernoulli inequality. Removing any selected prime leaves a deficient integer, by the exponential bound for a product of 1+1/p. Removing a core prime gives an even smaller abundancy ratio. Divisibility monotonicity then proves primitivity.

The quantitative prime number theorem supplies at least alpha/(4*log(k*alpha)) primes in this interval at the selected scales. Unique factorization makes distinct k-element prime subsets produce distinct integers. A binomial lower bound and a square-root logarithmic parameter choice give the stated exponent.

For a core cost C, put D=1000*(abs(C)+1), a=99*D/100 and t=sqrt(log(X)/D). The inequalities C+a<D and 79*D/80<a leave positive margins for both the size budget and the binomial count. Thus the constructed integers lie below X and their number is at least X^(79/80).

**Theorem 1.3 (Infinitely many integers with both primitivities).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-zhang-2025-question-1` (proved) by `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-zhang-2025-question-1","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky; Kyle Zhang (2025). *Kullback-Leibler divergence and primitive non-deficient numbers*. DOI: [10.48550/arXiv.2501.04209](https://doi.org/10.48550/arXiv.2501.04209). URL: <https://arxiv.org/abs/2501.04209v2>.

*Commentary.*

Question 1 on page twelve asks: Are there infinitely many n which are both primitive non-deficient and KL-primitive? For every natural bound B, the conclusion supplies a positive integer n greater than B with both properties. KL and KL-primitivity are the existing definitions of Equation (6) and Definition 1, including the divisor one.

Let k be at least three, put A = 2^k, and choose a prime p between 3A/2 and 7A/4. Set n = Ap. For every nonnegative exponent a, the exact formulas are sigma(2^a p) = (2^(a+1)-1)(p+1), KL(2^a) = -log 2, and KL(2^a p) = -(p+1) log 2 + p(2^(a+1)-1) log(p/(p-1)). Positive divisors have the forms 2^a and 2^a p; a proper divisor of the second form has a less than k. The mixed-prime formulas apply ZelinskyZhangKLPrimitive.sig_prime_mul and kl_prime_mul at the coprime factors p and 2^a, followed by the pure-power formulas and algebraic normalization.

The sigma formula gives non-deficiency at n and strict deficiency at every positive proper divisor. The logarithm bounds 1/p <= log(p/(p-1)) <= 1/(p-1) and 2/3 < log 2 < 1 give positive KL at n. For the second divisor form, 2^(a+1) is at most A and 2p is at least 3A, giving KL < (p+1)(2/3-log 2) < 0. Pure powers of two have KL equal to -log 2. Consequently every positive proper divisor has strictly negative KL.

FixedLayerRigidity.fixed_cardinality_prime_window with A = 3/2, B = 7/4 and N = 1 supplies a set of cardinality one in (3x/2,7x/4] for every sufficiently large x. Its member is prime. Both modules have generality I. Taking x = 2^k gives arbitrarily large constructed integers. The fixed interval fits between the asymptotic KL threshold 1/log 2 and the ordinary threshold 2.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive](ZelinskyZhangKLPrimitive.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Lower](../Robin/Analytic/OmegaTail/Lower.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](../Robin/PriceRecord/FixedLayerRigidity.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../Robin/PriceRecord/QuantitativePrimeAbel.md)
