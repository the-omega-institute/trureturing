# The unit-exponent bilateral product

## Abstract

Hanna's A380066 bilateral product congruence.

Paul D. Hanna's OEIS A380066 gives the bilateral product equation and conjectures that every positive coefficient is two modulo four. The formalization uses integer power series and coefficientwise symmetric windows for the bilateral sum.

**Definition 1.1 (The normalized bilateral generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{IsGF}\left(A\right) \Leftrightarrow ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(\operatorname{Int}.\operatorname{ofNat}\left(K\right)), \operatorname{Int}.\operatorname{ofNat}\left(K\right)\right)} (\operatorname{coeff}\left(\operatorname{Int}.\operatorname{ofNat}\left(N\right), \operatorname{laurentTerm}\left(1, A, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0))))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380066, bilateral product generating function*. URL: <https://oeis.org/A380066>.

*Commentary.*

The OEIS A380066 name states: "G.f. A(x) satisfies 1/2 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + x)^(n-1) * (A(x) + x^n)^(n-1)." A normalized integer power series satisfies this literal summand equation at every coefficient and every symmetric window whose radius is at least the coefficient index.

**Definition 1.2 (Hanna's A380066 coefficient conjecture).**

$$(\exists A \in (\operatorname{PowerSeries}\left(\mathbb{Z}\right)),\; \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, A\right) \bmod 4 = 2)))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380066, bilateral product generating function*. URL: <https://oeis.org/A380066>.

*Commentary.*

The OEIS A380066 comment states: "Conjecture: for n > 0, a(n) == 2 (mod 4)." There is a normalized integer solution, and every normalized integer solution has positive coefficients congruent to two modulo four.

**Theorem 1.3 (The proved A380066 congruence).**

$$(\exists A \in (\operatorname{PowerSeries}\left(\mathbb{Z}\right)),\; (\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(\operatorname{Int}.\operatorname{ofNat}\left(K\right)), \operatorname{Int}.\operatorname{ofNat}\left(K\right)\right)} (\operatorname{coeff}\left(\operatorname{Int}.\operatorname{ofNat}\left(N\right), \operatorname{laurentTerm}\left(1, A, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0)))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(\operatorname{Int}.\operatorname{ofNat}\left(K\right)), \operatorname{Int}.\operatorname{ofNat}\left(K\right)\right)} (\operatorname{coeff}\left(\operatorname{Int}.\operatorname{ofNat}\left(N\right), \operatorname{laurentTerm}\left(1, A, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0)))) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, A\right) \bmod 4 = 2)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A380066, bilateral product generating function*. URL: <https://oeis.org/A380066>.

*Commentary.*

The contraction of the coefficientwise bilateral remainder gives a normalized integral fixed series and identifies every normalized integral solution with it. The fixed point identity makes the difference from twice the geometric series minus one divisible by four, yielding the stated congruence. The same argument works for every exponent parameter at least one.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.IsGF`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.claim`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.result`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralProductModFour](BilateralProductModFour.md)
