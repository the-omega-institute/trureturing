# Hanna's Gaussian shifted-square parity

## Abstract

Symmetric coefficient pairs leave exactly the odd diagonal contribution.

**Definition 1.1 (Rational summands).**

$$\forall m: \mathbb{N}, (\operatorname{summand}\left(m\right) = (X)^{m} \cdot ((X)^{m + 1} + C\left(\operatorname{Complex}.\operatorname{I}\right))^{m} \cdot ((1 + C\left(\operatorname{Complex}.\operatorname{I}\right) \cdot (X)^{m + 1})^{m + 1})^{-1})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.summand` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A324300: Gaussian generating function and square parity*. URL: <https://oeis.org/A324300>.

*Commentary.*

OEIS A324300, NAME (unpaginated): "G.f.: Sum_{n>=0} x^n * (x^(n+1) + i)^n / (1 + i*x^(n+1))^(n+1)." Complex.I is the imaginary unit and X is the formal series variable. The inverse has unit constant denominator.

**Definition 1.2 (The coefficient series).**

$$A = \operatorname{PowerSeries}.\operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{summand}\left(m\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A324300: Gaussian generating function and square parity*. URL: <https://oeis.org/A324300>.

*Commentary.*

OEIS A324300, NAME (unpaginated): "G.f.: Sum_{n>=0} x^n * (x^(n+1) + i)^n / (1 + i*x^(n+1))^(n+1)." The leading X power makes each coefficient sum finite.

**Definition 1.3 (The parity assertion).**

$$claim = (\forall N: \mathbb{N}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(N, A\right) = (z: \mathbb{C})) \land (\operatorname{Odd}\left(z\right) \iff (\exists k: \mathbb{N}, (N = k \cdot \left(k + 2\right)))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2019). *OEIS A324300: Gaussian generating function and square parity*. URL: <https://oeis.org/A324300>.

*Commentary.*

OEIS A324300, COMMENTS and FORMULA (unpaginated): "Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture); a(n*(n+2)) = 1 (mod 2) for n >= 0." The index N is natural, z is an ordinary integer embedded in the complex numbers, and degree zero is included.

**Theorem 1.4 (Integral coefficients and exact odd support).**

$$\forall N: \mathbb{N}, (\exists z: \mathbb{Z}, ((\operatorname{coeff}\left(N, A\right) = (z: \mathbb{C})) \land (\operatorname{Odd}\left(z\right) \iff (\exists k: \mathbb{N}, (N = k \cdot \left(k + 2\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna324-gaussparity` (proved) by `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna324-gaussparity","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A324300: Gaussian generating function and square parity*. URL: <https://oeis.org/A324300>.

*Commentary.*

The exponent equation is symmetric in the two indices and off-diagonal pairs are even integers. A diagonal term is present exactly when N = k*(k+2), and its weight is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianShiftedSquareParity.summand`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity](HannaGaussianKernelParity.md)
