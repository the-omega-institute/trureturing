# Finite Prime Even Defect

## Abstract

A nonempty finite prime layer detects every nonzero mirror offset.

**Theorem 1.1 (The mirror-prime mean is a hyperbolic cosine).**

$$\forall p: \operatorname{NatPrimes}, delta: \mathbb{R},\\{}\frac{p^{delta} + p^{-delta}}{2} = \operatorname{cosh}(delta \cdot \operatorname{log}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.prime_mirror_mean_eq_cosh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and real offset delta, the arithmetic mean of the positive and negative real prime powers is cosh(delta log p).

**Definition 1.2 (Finite prime even defect).**

$$\forall P: \operatorname{Finset}(\operatorname{NatPrimes}), delta: \mathbb{R},\\{}\operatorname{finitePrimeEvenDefect}(P, delta) = 2 \cdot \sum_{p \in P} \frac{\operatorname{cosh}(delta \cdot \operatorname{log}(p)) - 1}{p}.$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finitePrimeEvenDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect doubles the finite sum of reciprocal-prime-weighted excesses of cosh(delta log p) above one.

**Theorem 1.3 (Each prime defect term is nonnegative).**

$$\forall p: \operatorname{NatPrimes}, delta: \mathbb{R},\\{}0 \leq \frac{\operatorname{cosh}(delta \cdot \operatorname{log}(p)) - 1}{p}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.prime_even_defect_term_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib gives cosh x at least one, and every prime is positive, so division by p preserves nonnegativity.

**Theorem 1.4 (A nonzero offset has positive finite-prime defect).**

$$\forall P: \operatorname{Finset}(\operatorname{NatPrimes}), delta: \mathbb{R},\\{}\operatorname{Nonempty}(P) \land delta \neq 0 \Rightarrow 0 < \operatorname{finitePrimeEvenDefect}(P, delta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finite_prime_even_defect_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a prime from the nonempty layer. Its logarithm is nonzero, so a nonzero delta makes delta log p nonzero and the strict cosh criterion makes that summand positive.

All remaining summands are nonnegative; hence the complete finite sum and its positive factor two are strictly positive.

**Theorem 1.5 (The finite-prime defect vanishes exactly at zero offset).**

$$\forall P: \operatorname{Finset}(\operatorname{NatPrimes}), delta: \mathbb{R},\\{}\operatorname{Nonempty}(P) \Rightarrow \operatorname{finitePrimeEvenDefect}(P, delta) = 0 \Leftrightarrow delta = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finite_prime_even_defect_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite set of primes, a nonzero offset has positive defect by the preceding theorem, while substitution of delta zero makes every hyperbolic-cosine excess vanish.

This closes the exact finite-layer detection claim. The source's later informal small-offset and prime-number-scale asymptotic discussion is not asserted by this declaration.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finitePrimeEvenDefect`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finite_prime_even_defect_eq_zero_iff`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.finite_prime_even_defect_pos`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.prime_even_defect_term_nonneg`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeEvenDefect.prime_mirror_mean_eq_cosh`
