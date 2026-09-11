# Dyadic Denominators of OEIS A381670

## Abstract

Every reduced denominator of the normalized compositional-square series is a power of two.

Thomas Scheuerle's entry of March 3, 2025, cited in scheuerle2025a381670, defines A by x(A(x)+1)=A(A(x)), with constant coefficient zero and linear coefficient one. A381669 records the reduced numerators; A381670 records the positive reduced denominators.

A denotes generatingSeries, f(n) its rational coefficient, and X the formal variable. The notation coeff(n,P) means the coefficient of X^n in P, C embeds a scalar as a constant series, subst(P,Q) means P(Q(X)), and rescale(c,P) means P(cX). The integral series I is built from compatible approximations P_n. The map iota sends integers to rationals. All indices are natural numbers; subtraction in an exponent is natural subtraction. The operation div below is integer division.

**Definition 1.1 (Construction by compatible integral approximations).**

$$\begin{aligned}A = \operatorname{C}\left(4\right) \cdot \operatorname{rescale}\left(\frac{1}{4}, \operatorname{map}\left(\operatorname{iota}, I\right)\right)\\I = \operatorname{mk}\left(n \mapsto \operatorname{coeff}\left(n, \operatorname{P}\left(n\right)\right)\right)\\\operatorname{P}\left(0\right) = X\\\forall n \in \mathbb{N}, \operatorname{P}\left(n + 1\right) = \operatorname{P}\left(n\right) + \operatorname{C}\left(-\operatorname{div}\left(\operatorname{coeff}\left(n + 2, \operatorname{E}\left(\operatorname{P}\left(n\right)\right)\right), 2\right)\right) \cdot X^{n + 2}\\\forall P \in \mathbb{Z}[[X]], \operatorname{E}\left(P\right) = \operatorname{subst}\left(P, P\right) - X - 4 \cdot X \cdot P\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set E(P)=P(P(X))-X-4XP. Starting with P_0=X, correct degree n+2 by subtracting half its residual. The triangular composition identity gives multiplier two in that degree and preserves every lower degree. If P-X=2Q, then Q(P)-Q(X) is divisible by two, because P^j-X^j is divisible by P-X. Therefore E(P) is divisible by four and each correction is even. The stable coefficients define I. Scaling back gives A=4I(X/4), with the integer coefficients embedded in the rationals.

**Definition 1.2 (The rational coefficient sequence).**

$$\forall n \in \mathbb{N}, \operatorname{f}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence f is extracted from the constructed formal series. Its reduced denominators are the terms of A381670, with denominator one for any zero coefficient.

**Theorem 1.3 (The defining functional equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (X \cdot (A + 1) = \operatorname{subst}\left(A, A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.functional_equation` (`✓ std3`). ∎

*Citation.* Thomas Scheuerle (2025). *OEIS A381670, denominators of the compositional-square series*. URL: <https://oeis.org/A381670>.

*Commentary.*

The limit of the corrected approximations satisfies I(I(X))=X+4XI(X). Mapping to rational coefficients and conjugating by the linear scaling gives exactly X(A+1)=A(A(X)), with the stated constant and linear terms.

**Theorem 1.4 (Uniqueness with the specified normalization).**

$$\forall B \in \mathbb{Q}[[X]], (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((X \cdot (B + 1) = \operatorname{subst}\left(B, B\right)) \implies (B = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two normalized series agree below degree n, their compositional squares differ there by twice their coefficient difference. The right side X+XB depends only on the preceding coefficient. Induction therefore forces equality at every degree over the rationals.

**Theorem 1.5 (The rescaled coefficients are even integers).**

$$\forall n \in \mathbb{N}, (2 \le n) \implies (\exists z \in \mathbb{Z}, 4^{n - 1} \cdot \operatorname{f}\left(n\right) = \operatorname{iota}\left(2 \cdot z\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.rescaled_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integral approximation differs from X by twice an integer series. This persists in the compatible limit I. Undoing the scaling identifies its degree-n coefficient with 4^(n-1)f(n) for n at least two.

**Theorem 1.6 (Every denominator is a power of two).**

$$\forall k \in \mathbb{N}, \exists e \in \mathbb{N}, \operatorname{den}\left(\operatorname{f}\left(k\right)\right) = 2^{e}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.scheuerle_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381670-compositional-square-dyadic-denominators` (proved) by `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.scheuerle_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381670-compositional-square-dyadic-denominators","declaration_gid":"D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.scheuerle_conjecture","resolution_kind":"proved"} -->

*Citation.* Thomas Scheuerle (2025). *OEIS A381670, denominators of the compositional-square series*. URL: <https://oeis.org/A381670>.

*Commentary.*

For n at least two the even-integer invariant writes f(n) as an integer divided by 4^(n-1). Its reduced denominator divides that power of two, so it is itself a power of two. At indices zero and one the coefficients are zero and one, both with denominator one. No nonzero-coefficient restriction is imposed.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.f`
- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.functional_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.rescaled_even`
- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.scheuerle_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.uniqueness`
