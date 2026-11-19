# Zelinsky's Conjectures 10, 12 and 14

## Abstract

Primitive non-deficient integers have relative density zero in B.

**Definition 1.1 (The primitive non-deficient counting function).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitiveCount`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitiveCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

The count uses the existing predicate PrimitiveNonDeficient and the inclusive interval [1,X]. A positive integer is primitive non-deficient when its divisor sum is at least twice itself and every positive proper divisor has divisor sum strictly less than twice itself.

**Theorem 1.2 (Primitive non-deficient integers have density zero).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitive_density_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitive_density_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

Write h(n)=sigma(n)/n. For n primitive non-deficient and a prime power p^a exactly dividing n, the prime-step formula and h(n/p)<2 give 2<=h(n)<2+2/p^a. If all full prime powers of n are at most T, their prime valuations show that n divides T!. Consequently every primitive non-deficient n>T! satisfies 2<=h(n)<2+2/T.

Fix 2<=K<=L and take T=2L^2. If a primitive non-deficient n>T! has a prime divisor p in [K,L] which occurs exactly once, write n=mp. Then h(n)=h(m)(1+1/p). The cofactor m determines p uniquely among such integers. Indeed, distinct primes p<q<=L give a difference h(m)(1/p-1/q)>=1/L^2, since h(m)>=1. Two values in [2,2+1/L^2) cannot have that separation. There are at most X/K possible cofactors for n<=X.

The remaining integers either have no prime divisor in [K,L] or are divisible by p^2 for some p>=K. Put Q equal to the product of the primes in [K,L]. Quotient and remainder modulo Q bound the first count by X*phi(Q)/Q+phi(Q). Euler's totient formula identifies phi(Q)/Q with the product of 1-1/p on that interval. The square-divisor count is at most 2X/K. Altogether C(X) is at most (2L^2)!+phi(Q)+X*product(1-1/p)+3X/K.

For fixed K, Mertens' product theorem makes the interval product tend to zero as L tends to infinity. Choose L so that it is less than 1/K. After division by X, the two constant terms vanish, and the remaining upper bound is 4/K. Letting K increase proves C(X)/X tends to zero.

**Theorem 1.3 (The three relative counting limits).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-2026-radical-component-density` (proved) by `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result` and `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-radical-component-density","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-radical-component-density","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For B defined by the threshold lam=2, the limits (B intersect C)(X)/B(X), (B intersect C_O)(X)/B(X), and (B intersect C_M)(X)/B(X) are all zero. Here C_O is the set of odd primitive non-deficient integers, and M ranges over all nonempty finite sets of primes; C_M consists of primitive non-deficient integers divisible by no element of M. Each numerator is bounded by C(X), whereas B(X)/X tends to the positive constant 1-log(2). The quotient limit therefore follows. The argument applies to every subset of C and every positive radical threshold. It does not settle the different ratios whose denominator is C(X).

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitiveCount`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.primitive_density_zero`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result`
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity](StrongPseudoperfectEulerDensity.md)
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity](ZelinskyRadicalComponentDensity.md)
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive](ZelinskyZhangDoublePrimitive.md)
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](../Robin/PrimeFiberPropagation.md)
