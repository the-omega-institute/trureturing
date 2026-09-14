# Perturbed Diagonal Square Divisibility

## Abstract

Hanna's vanishing diagonal defines a unique integer series and implies square divisibility for every integer perturbation.

The note hanna2023a365095 records the defining equation and conjecture of OEIS A365095. Write A for generatingSeries and P(d) for the integer-series approximation at depth d. The indices n and d are natural numbers, while k is an arbitrary integer and B is an integer power series. Subtraction in the index n-1 is natural subtraction; subtraction in parameters is integer subtraction, with intCast marking the conversion from natural numbers.

The operator coeff extracts a coefficient, mk forms a series from its coefficient function, and C embeds an integer as a constant series. The symbols 1 and X denote the unit series and formal variable. The expression invOfUnit(f,1) is the formal inverse when coeff(0,f)=1. The operator ediv is integer division; each division in the update below is proved exact. Divisibility in the conclusion is over the integers.

**Definition 1.1 (The integral triangular construction).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{P}\left(d + 1\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} \operatorname{coeff}\left(n, \operatorname{P}\left(d\right)\right) + \operatorname{ediv}\left(\operatorname{coeff}\left(n, (\operatorname{invOfUnit}\left(\operatorname{P}\left(d\right), 1\right) + ((\operatorname{C}\left(\operatorname{intCast}\left(n\right)\right)) \cdot (X)) \cdot (\operatorname{P}\left(d\right)))^{n + 1}\right), \operatorname{intCast}\left(n\right) + 1\right))\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-n residual is the coefficient of the (n+1)-st power of invOfUnit(P(d),1)+C(intCast(n))*X*P(d). Differentiation proves that n+1 divides this coefficient. If two normalized series agree below n, their residuals differ by -(n+1) times their degree-n coefficient difference. Thus the update extends agreement by one degree and the approximations stabilize.

**Definition 1.2 (The normalized integer series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stabilized integer coefficient function a defines A.

**Theorem 1.3 (The defining vanishing diagonal).**

$$(\operatorname{coeff}\left(0, A\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n - 1, ((1 + ((\operatorname{C}\left(\operatorname{intCast}\left(n\right) - 1\right)) \cdot (X)) \cdot ((A)^{2}))^{n}) \cdot ((\operatorname{invOfUnit}\left(A, 1\right))^{n})\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives a fixed point of the triangular update. Exact division then forces every positive-degree residual to vanish. Multiplying 1+C(t)*X*A^2 by invOfUnit(A,1) gives invOfUnit(A,1)+C(t)*X*A. Taking the n-th power bridges the residual to precisely the defining diagonal with t=n-1.

**Theorem 1.4 (Uniqueness among normalized integer series).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n - 1, ((1 + ((\operatorname{C}\left(\operatorname{intCast}\left(n\right) - 1\right)) \cdot (X)) \cdot ((B)^{2}))^{n}) \cdot ((\operatorname{invOfUnit}\left(B, 1\right))^{n})\right) = 0)) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any B satisfying the normalized vanishing diagonal is a fixed point of the same exact integer update. The inverse-difference identity and leading-power coefficient calculation show that the update improves agreement by one degree. Induction identifies B with A.

**Definition 1.5 (The integer-parameter diagonal).**

$$\forall k: \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{perturbedDiagonal}\left(k, n\right) = \operatorname{coeff}\left(n - 1, ((1 + ((\operatorname{C}\left((k) \cdot (\operatorname{intCast}\left(n\right)) - 1\right)) \cdot (X)) \cdot ((A)^{2}))^{n}) \cdot ((\operatorname{invOfUnit}\left(A, 1\right))^{n})\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.perturbedDiagonal` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A365095, expansion of a generating function defined by a vanishing diagonal*. URL: <https://oeis.org/A365095>.

*Commentary.*

This is the coefficient extraction in formula (2), using the n-th power of the formal unit inverse for division by A(x)^n.

**Theorem 1.6 (Square divisibility for every integer k).**

$$\forall k: \mathbb{Z}, \forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{intCast}\left(n\right))^{2} \mid \operatorname{perturbedDiagonal}\left(k, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a365095-perturbed-diagonal-square-divisibility` (proved) by `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a365095-perturbed-diagonal-square-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2023). *OEIS A365095, expansion of a generating function defined by a vanishing diagonal*. URL: <https://oeis.org/A365095>.

*Commentary.*

Replacing n-1 by k*n-1 adds n*C(k-1)*X*A^2 to the base of the n-th power. Mathlib's dvd_sub_pow_of_dvd_sub gives divisibility of the power difference by n^2. Multiplication by invOfUnit(A,1)^n and coefficient extraction preserve it. For n>1 the defining diagonal is zero; for n=1 the divisor is one. No sign restriction is imposed on k.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.a`
- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.perturbedDiagonal`
