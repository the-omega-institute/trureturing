# A lower bound after excluding finitely many primes

## Abstract

Odd squarefree primitive non-deficient integers have a power lower bound.

**Theorem 1.1 (A uniform eventual exponent of 39/40).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For every finite set M of primes there is a natural threshold X0 such that, for every natural X at least X0, at least X^(39/40) positive integers n at most X are odd, squarefree, primitive non-deficient, and divisible by no prime in M. The finite set may be empty. Primitive non-deficiency means that sigma(n) is at least 2n and sigma(d) is strictly less than 2d for every positive proper divisor d of n.

Write h(m)=sigma(m)/m and alpha=h(m)/(2-h(m)) for a deficient squarefree core. A finite prime product first crossing h=2 gives an initial deficient core. Adjoining primes between 2alpha and 3alpha increases alpha by a fixed multiplicative factor while retaining deficiency. Thus alpha can reach a prescribed exponential scale with log(m) bounded by a constant times the square of that scale's logarithm.

Choose k distinct primes in the interval ((k-1)(alpha+1),k*alpha]. Their product times the core is abundant by the strict Bernoulli inequality. Removing any selected prime leaves a deficient integer, by the exponential bound for a product of 1+1/p. Removing a core prime gives an even smaller abundancy ratio. Divisibility monotonicity then proves primitivity.

The quantitative prime number theorem supplies at least alpha/(4*log(k*alpha)) primes in this interval at the selected scales. Unique factorization makes distinct k-element prime subsets produce distinct integers. A binomial lower bound and a square-root logarithmic parameter choice give the stated exponent.

The related source questions are Zelinsky's Conjectures 11, 13 and 15 in section 3 of arXiv:2005.12115v5, also referenced by https://github.com/the-omega-institute/trureturing/issues/31919. This theorem supplies a counting lower bound for their primitive non-deficient families.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound.result`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyDeficientCore](ZelinskyDeficientCore.md)
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive](ZelinskyZhangDoublePrimitive.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Lower](../Robin/Analytic/OmegaTail/Lower.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../Robin/PriceRecord/QuantitativePrimeAbel.md)
