# Factorial Square-Exponent Sum Parity

## Abstract

The coefficients of OEIS A222014 are odd exactly one below a power of two.

The entry cited in hanna2024a222014 defines A by a factorial product sum whose numerator exponent is r squared and whose denominator exponent is r. It asks whether a(n) is odd exactly when n+1 is a power of two.

All indices are natural numbers. R is a commutative ring, Z is the integer ring, and X is the power-series indeterminate. The operation coeff extracts coefficients, mk constructs a series from its coefficient function, and C embeds a scalar as a constant series. Each displayed unit inverse has constant coefficient one.

The parameter functions e and d control the numerator and denominator powers independently. The factor X to the r makes the degree window independent of their growth. P denotes the private finite-step approximations used to define a, pi is the integer cast into ZMod(2), and K is the Catalan series from CatalanCompositionSquareParity.

**Definition 1.1 (The exponent-parametric summand).**

$$\forall e: \mathbb{N} \Rightarrow \mathbb{N}, \forall d: \mathbb{N} \Rightarrow \mathbb{N} \Rightarrow \mathbb{N}, \forall r: \mathbb{N}, \forall F: \operatorname{PowerSeries}\left(R\right), \operatorname{parameterizedTerm}\left(e, d, r, F\right) = \operatorname{C}\left(\operatorname{factorial}\left(r\right)\right) \cdot X^{r} \cdot F^{\operatorname{e}\left(r\right)} \cdot \operatorname{invOfUnit}\left(\prod_{k \in \operatorname{range}\left(r\right)} (1 + \operatorname{C}\left(k + 1\right) \cdot X \cdot F^{\operatorname{d}\left(r, k\right)}), 1\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.parameterizedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two exponent functions are arbitrary. The product ranges over k below r, so its scalar k+1 represents the factors numbered one through r.

**Theorem 1.2 (Uniform degree contraction).**

$$\forall e: \mathbb{N} \Rightarrow \mathbb{N}, \forall d: \mathbb{N} \Rightarrow \mathbb{N} \Rightarrow \mathbb{N}, \forall r: \mathbb{N}, \forall N: \mathbb{N}, (N < r) \implies \forall F: \operatorname{PowerSeries}\left(R\right), \operatorname{coeff}\left(N, \operatorname{parameterizedTerm}\left(e, d, r, F\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.parameterized_term_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factor X to the r divides every parameterized summand. The coefficient criterion for this divisibility makes every degree below r zero.

**Definition 1.3 (The A222014 summand).**

$$\forall r: \mathbb{N}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{term}\left(r, F\right) = \operatorname{C}\left(\operatorname{factorial}\left(r\right)\right) \cdot X^{r} \cdot F^{r^{2}} \cdot \operatorname{invOfUnit}\left(\prod_{k \in \operatorname{range}\left(r\right)} (1 + \operatorname{C}\left(k + 1\right) \cdot X \cdot F^{r}), 1\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.term` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set e(r) to r squared and set d(r,k) to r in the parameterized summand.

**Theorem 1.4 (The A222014 coefficient window).**

$$\forall r: \mathbb{N}, \forall N: \mathbb{N}, (N < r) \implies \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{coeff}\left(N, \operatorname{term}\left(r, F\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.term_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-exponent specialization inherits the uniform coefficient window.

**Definition 1.5 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from the zero series, each finite step extends agreement by one degree. The diagonal coefficient at stage n+1 defines a(n).

**Definition 1.6 (The integer generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series is constructed from the diagonal coefficient function.

**Theorem 1.7 (The coefficientwise OEIS equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, A\right) = \sum_{r \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{term}\left(r, A\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stability identifies each diagonal coefficient with one further finite step. Only indices at most N contribute to degree N.

**Theorem 1.8 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, B\right) = \sum_{r \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{term}\left(r, B\right)\right))) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed point agrees with A below degree zero. The degree contraction extends agreement one coefficient at a time, yielding equality.

**Theorem 1.9 (The reduced quadratic equation).**

$$\operatorname{map}\left(pi, A\right) = 1 + X \cdot \operatorname{map}\left(pi, A\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.mod_two_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r at least two, the scalar r factorial is zero in ZMod(2). The terms r=0 and r=1 remain, and cancellation of their unit denominator gives the quadratic equation.

**Theorem 1.10 (Catalan series identity).**

$$X \cdot \operatorname{map}\left(pi, A\right) = \operatorname{map}\left(pi, K\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reduced A222014 and A222013 series have constant coefficient one and obey the same quadratic equation. Unit cancellation identifies them, after which the established A222013 identity supplies X map(pi,A)=map(pi,K).

**Theorem 1.11 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n + 1 = 2^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.hanna_conjecture` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2024). *OEIS A222014, factorial square-exponent product-sum generating function and parity conjecture*. URL: <https://oeis.org/A222014>.

*Commentary.*

Coefficient equality transfers the established A222013 parity theorem to a. An integer maps to one in ZMod(2) exactly when it is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.mod_two_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.parameterizedTerm`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.parameterized_term_coeff_eq_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.term`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.term_coeff_eq_zero`
- Dependency: [D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity](FactorialProductSumCatalanParity.md)
