# Quadratic Square Reversion Modulo Four

## Abstract

The coefficients of OEIS A389542 satisfy Hanna's mod-four classification.

The entry cited in hanna2025a389542 defines A by A(A(x)^2-x^2)=4A(x)^3. For n greater than one, its conjecture asserts that a(n) is congruent to two modulo four at indices one more than a power of two, and divisible by four elsewhere.

All indices are natural numbers and all coefficients are integers. R denotes inverseSeries, A denotes generatingSeries, and X is the indeterminate. The local series P(n) are the approximations and H is their coefficientwise limit. The operator mk constructs a series from its coefficient function; coeff(n,B) extracts its nth coefficient; subst(B,C) substitutes C into B; inv(R) denotes Mathlib's substInvOfIsUnit with the proved unit linear coefficient. K denotes catalanSeries from CatalanCompositionSquareParity, the integer series with zero constant coefficient satisfying K=X+K^2. The map pi sends integers to ZMod(4), and map(pi,B) applies pi coefficientwise. The operator mod denotes integer remainder.

**Definition 1.1 (The integral inverse).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{P}\left(n + 1\right) = -X - \operatorname{P}\left(n\right)^{2} - 2 \cdot X \cdot \operatorname{subst}\left(\operatorname{P}\left(n\right), 4 \cdot X^{3}\right)\\H = \operatorname{mk}\left((n \mapsto \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right))\right)\\R = X \cdot (1 + 2 \cdot H)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.inverseSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map defining P preserves zero constant coefficient and increases coefficient agreement by one degree. Thus the displayed diagonal limit H satisfies H=-X-H^2-2XH(4X^3). The series R=X(1+2H) has zero constant coefficient and linear coefficient one.

**Definition 1.2 (The generating series).**

$$A = \operatorname{inv}\left(R\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compositional inverse is defined over the integers and satisfies R(A)=X and A(R)=X.

**Definition 1.3 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the coefficient of degree n in A.

**Theorem 1.4 (The quadratic inverse equation).**

$$R^{2} = X^{2} - \operatorname{subst}\left(R, 4 \cdot X^{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.inverse_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding R=X(1+2H), its defining correction equation gives R^2=X^2-R(4X^3) exactly over the integers.

**Theorem 1.5 (The OEIS equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left(A, (A^{2} - X^{2})\right) = 4 \cdot A^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting A into the inverse equation gives R(4A^3)=A^2-X^2. Composing with A gives the stated functional equation. Integral compositional inversion gives the two normalization conditions.

**Theorem 1.6 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (\operatorname{coeff}\left(1, B\right) = 1) \implies (\operatorname{subst}\left(B, (B^{2} - X^{2})\right) = 4 \cdot B^{3}) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized solution B has an integral compositional inverse S. Transporting its equation gives S^2=X^2-S(4X^3). To compare S with R, pass injectively to rational coefficients and write S=Xu and R=Xv. Both units satisfy u^2=1-4Xu(4X^3), and their sum has constant coefficient two. Multiplying the difference by this unit and using substitution increases coefficient agreement by one degree. Induction gives S=R and hence B=A.

**Theorem 1.7 (The Catalan correction modulo four).**

$$\operatorname{map}\left(pi, A\right) = X + 2 \cdot X \cdot \operatorname{map}\left(pi, K\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing the correction equation modulo two gives H=X+H^2. The factor 1-H-K is a unit, so comparison with K=X+K^2 yields H=K modulo two. Also R=X modulo two, whence A=X modulo two. Therefore AH(A)=XK modulo two. Doubling lifts this equality modulo four; R(A)=A+2AH(A)=X then gives A=X+2XK modulo four.

**Theorem 1.8 (Hanna's coefficient conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies ((\operatorname{a}\left(n\right) \bmod 4 = 2 \iff (\exists k: \mathbb{N}, n = 2^{k} + 1)) \land (\operatorname{a}\left(n\right) \bmod 4 = 0 \iff \neg (\exists k: \mathbb{N}, n = 2^{k} + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389542-quadratic-square-reversion-mod-four` (proved) by `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389542-quadratic-square-reversion-mod-four","declaration_gid":"D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389542, g.f. satisfying A(A(x)^2 - x^2) = 4*A(x)^3*. URL: <https://oeis.org/A389542>.

*Commentary.*

The frozen binary_catalan theorem states that the coefficient of degree m in K is odd exactly when m is a power of two. For n greater than one, the mod-four identity gives a(n)=2 coeff(n-1,K) modulo four. An odd coefficient gives remainder two and an even coefficient gives remainder zero, proving both biconditionals.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.a`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.inverseSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.inverse_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.mod_four_identity`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
