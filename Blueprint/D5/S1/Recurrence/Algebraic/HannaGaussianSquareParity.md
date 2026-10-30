# Hanna's Gaussian square parity

## Abstract

Symmetric coefficient pairs leave exactly the odd diagonal contribution.

**Definition 1.1 (Rational summands).**

$$\forall m: \mathbb{N}, (\operatorname{summand}\left(m\right) = ((X)^{m} + C\left(\operatorname{Complex}.\operatorname{I}\right))^{m} \cdot ((1 + C\left(\operatorname{Complex}.\operatorname{I}\right) \cdot (X)^{m})^{m + 1})^{-1})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.summand` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

OEIS A323689, NAME (unpaginated): "G.f.: Sum_{n>=0} (x^n + i)^n / (1 + i*x^n)^(n+1), in which the constant term is taken to be 1." Complex.I is the imaginary unit and X is the formal series variable. The inverse has unit constant denominator.

**Definition 1.2 (The coefficient series).**

$$A = \operatorname{PowerSeries}.\operatorname{mk}\left((N: \mathbb{N} \mapsto \operatorname{if} (N = 0) \operatorname{then} 1 \operatorname{else} \sum_{m \in \operatorname{Finset}.\operatorname{Icc}\left(1, N\right)} (\operatorname{coeff}\left(N, \operatorname{summand}\left(m\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

OEIS A323689, NAME (unpaginated): "G.f.: Sum_{n>=0} (x^n + i)^n / (1 + i*x^n)^(n+1), in which the constant term is taken to be 1." Degree zero is 1. At positive degree N, only indices 1 through N contribute.

**Definition 1.3 (The parity assertion).**

$$claim = (\forall N: \mathbb{N}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(N, A\right) = (z: \mathbb{C})) \land (\operatorname{Odd}\left(z\right) \iff (\exists r: \mathbb{N}, (N = (r)^{2}))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

OEIS A323689, COMMENTS and FORMULA (unpaginated): "Odd terms occur only at n = k^2 for k >= 0 (conjecture); a(n^2) = 1 (mod 2) for n >= 0." The index N is natural, z is an ordinary integer embedded in the complex numbers, and degree zero is included.

**Theorem 1.4 (Integral coefficients and exact odd support).**

$$\forall N: \mathbb{N}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(N, A\right) = (z: \mathbb{C})) \land (\operatorname{Odd}\left(z\right) \iff (\exists r: \mathbb{N}, (N = (r)^{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna323-gaussparity` (proved) by `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna323-gaussparity","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

At positive degree, the exponent equation is symmetric in the two indices and off-diagonal pairs are even integers. A diagonal term is present exactly when N = r^2, and its weight is odd. The constant coefficient is 1.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.summand`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity](HannaGaussianKernelParity.md)
