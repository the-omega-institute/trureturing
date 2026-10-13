# Integral Analytic Discriminant

## Abstract

An integral divisor-sum series for the actual analytic modular discriminant, with finite coefficient computation.

For r a natural number let U_r have coefficient sigma_r(n), the sum of the r-th powers of the positive divisors of n. The divisor set at zero is empty. Put U=U_3 and V=U_5. The normalized weight-four and weight-six Eisenstein series have q-expansions 1+240U and 1-504V.

**Theorem 1.1 (Weight-four integral series).**

$$\operatorname{map}\left(E_{4}\right) = \operatorname{qExpansion}\left(1, E_{4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinFour_map` (`✓ std3`). ∎

*Citation.* The Mathlib Community (2026). *Mathlib4: Modular Forms*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ModularForms>.

*Commentary.*

Mapping integralEisensteinFour coefficientwise through the integer embedding into the complex numbers gives qExpansion 1 E4, for Mathlib's actual analytic normalized Eisenstein form. EisensteinSeries.E_qExpansion_coeff supplies its divisor-sum formula; bernoulli(4)=-1/30 supplies the factor 240. This identity is used in the discriminant comparison.

**Theorem 1.2 (Weight-six integral series).**

$$\operatorname{map}\left(E_{6}\right) = \operatorname{qExpansion}\left(1, E_{6}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinSix_map` (`✓ std3`). ∎

*Citation.* The Mathlib Community (2026). *Mathlib4: Modular Forms*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ModularForms>.

*Commentary.*

Mapping integralEisensteinSix coefficientwise gives qExpansion 1 E6 for the actual analytic form. The same normalized Eisenstein formula, with bernoulli(6)=1/42, supplies the factor -504. Both series have constant coefficient one.

**Theorem 1.3 (The integer series is the actual discriminant).**

$$\operatorname{map}\left(D\right) = \operatorname{qExpansion}\left(1, \Delta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralDiscriminant_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer d, 5d^3+7d^5 is zero modulo 3 and modulo 4. These coprime divisibilities imply divisibility by 12. Summing over divisors proves that C_n=(5 sigma_3(n)+7 sigma_5(n))/12 is an exact integer quotient, including n=0.

Set D=C+100U^2-147V^2+8000U^3. The exact quotient identity gives 1728D=(1+240U)^3-(1-504V)^2. Mathlib's discriminant_eq_E4_cube_sub_E6_sq identifies the corresponding actual analytic functions. Compatibility of qExpansion with scalar multiplication, subtraction and powers then proves map(D)=qExpansion 1 Delta. Thus every analytic discriminant coefficient is an integer; division by 1728 alone is not the integrality argument.

The accompanying Mathlib source note records the pinned Eisenstein and analytic discriminant suppliers and links the existing Ribet-Stein Hecke context. The integer denominator-clearing realization and the finite coefficient bridge are repository proofs of classical modular-form infrastructure; no unique result, new verified Maeda case or mathematical originality is claimed. The full Miller basis and actual Hecke matrix construction remain unresolved.

**Theorem 1.4 (Executable integer coefficients).**

$$\forall n : N, \operatorname{a}\left(\Delta, n\right) = \operatorname{cast}\left(\operatorname{discriminantCoefficient}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/IntegralDiscriminant.discriminantCoefficient_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

discriminantCoefficient(n) computes the exact quotient C_n and finite convolution coefficients for 100U^2-147V^2+8000U^3. Each convolution sums i from 0 through n. Nested convolution computes the cube. The function uses integer arithmetic and finite divisor sets, with no analytic coefficient evaluation or selected inverse. For every n its integer output, embedded in the complex numbers, equals coefficient n of the actual analytic discriminant.

At every natural precision N, PowerSeries.trunc_apply and Fin.sum_univ_eq_sum_range turn this coefficient theorem into equality between the analytic truncation and the polynomial of integer outputs at indices n<N. This application is checked transiently rather than retained as a separate theorem. Precision pm+1 includes coefficient pm. IntegralMillerBasis constructs the normalized integral basis and full coefficient lattice for m>=1 and s in 0,4,6,8,10,14 at weight 12m+s. The actual Hecke matrix and finite-array precision correctness remain to be proved.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/IntegralDiscriminant.discriminantCoefficient_correct`
- Truth anchor: `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralDiscriminant_map`
- Truth anchor: `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinFour_map`
- Truth anchor: `D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinSix_map`
