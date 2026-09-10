# Reflected Quadratic Quarter Parity

## Abstract

The integer coefficients of OEIS A369083 have the conjectured binomial parity.

The entry cited in hanna2024a369083 defines A by A(x)=1+x*(5*A(x)^2-A(-x)^2)/4 and conjectures the parity of binomial(4*n+3,n) for every natural index n, including zero. The equation below clears the denominator four over the integers.

All indices are natural numbers and all coefficients are integers. A denotes generatingSeries; P(n) denotes its private approximations. The operator coeff extracts a coefficient, mk constructs a series, Even is the even-index predicate, and ite selects its second argument when its first argument holds and its third otherwise. The operator ediv is integer Euclidean division; mod is integer remainder. The series rescale(-1,B) is B(-X). The map pi sends integers to ZMod(2), and map(pi,B) applies it coefficientwise. G denotes the integer generatingSeries of AbsoluteReciprocalCubeParity: it has constant coefficient one and satisfies G=1+X*absSeries(invOfUnit(G,1))^3, as recorded in hanna2024a369083.

**Definition 1.1 (The integer coefficient sequence).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{coeff}\left(0, \operatorname{P}\left(n + 1\right)\right) = 1\\\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{coeff}\left(k + 1, \operatorname{P}\left(n + 1\right)\right) = \operatorname{ite}\left(\operatorname{Even}\left(k\right), \operatorname{coeff}\left(k, \operatorname{P}\left(n\right)^{2}\right), 3 \cdot \operatorname{ediv}\left(\operatorname{coeff}\left(k, \operatorname{P}\left(n\right)^{2}\right), 2\right)\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update uses the coefficient of P(n)^2 at the preceding index. At odd indices of that square, reduction modulo two and Frobenius show divisibility by two. Each update increases coefficient agreement by one degree, so the diagonal coefficients define an integer solution.

**Definition 1.2 (The generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.3 (The normalized OEIS equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (4 \cdot (A - 1) = X \cdot (5 \cdot A^{2} - \operatorname{rescale}\left(-1, A\right)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient stabilization gives the fixed point. Even degrees of the square contribute directly; odd degrees contribute three times their exact half. These are precisely the coefficients of the equation with its denominator cleared.

**Theorem 1.4 (Uniqueness over the integers).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((4 \cdot (B - 1) = X \cdot (5 \cdot B^{2} - \operatorname{rescale}\left(-1, B\right)^{2})) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancelling four shows that any solution is fixed by the coefficient update. Induction on the degree of agreement identifies it with A.

**Theorem 1.5 (Eliminating the reflected series).**

$$\operatorname{rescale}\left(-1, A\right) = 5 \cdot A - 4 - 6 \cdot X \cdot A^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.reflection_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rescaling the equation by minus one gives its reflected counterpart. Subtracting five times the original equation cancels the reflected square; cancelling four gives this linear expression.

**Theorem 1.6 (The quartic equation).**

$$1 - 4 \cdot X + (10 \cdot X - 1) \cdot A - (5 \cdot X + 12 \cdot X^{2}) \cdot A^{2} + 15 \cdot X^{2} \cdot A^{3} - 9 \cdot X^{3} \cdot A^{4} = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.quartic_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the reflected expression into the original equation and cancelling four gives the displayed quartic.

**Theorem 1.7 (Adjacent binomial coefficients).**

$$\forall n: \mathbb{N}, \operatorname{choose}\left(4 \cdot n + 3, n + 1\right) = 3 \cdot \operatorname{choose}\left(4 \cdot n + 3, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.choose_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's adjacent-binomial identity gives equality after multiplication by n+1. Since 4*n+3-n=3*(n+1), cancellation gives the factor three.

**Theorem 1.8 (Identification with the reciprocal-cube series).**

$$1 + X \cdot \operatorname{map}\left(pi, A\right) = \operatorname{map}\left(pi, G\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing F=map(pi,A), the quartic reduces to F*(1+X*F)^3=1. Consequently H=1+X*F satisfies H^4-H^3=X. Absolute values are invisible modulo two, so map(pi,G) satisfies the same equation. The difference factors through a series of constant coefficient one, whose invertibility proves equality.

**Theorem 1.9 (Hanna's binomial parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) \bmod 2 = \operatorname{choose}\left(4 \cdot n + 3, n\right) \bmod 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a369083-reflected-quadratic-quarter-parity` (proved) by `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a369083-reflected-quadratic-quarter-parity","declaration_gid":"D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A369083, g.f. satisfying A(x) = 1 + x*(5*A(x)^2 - A(-x)^2)/4*. URL: <https://oeis.org/A369083>.

*Commentary.*

The coefficient of degree n+1 in G modulo two is binomial(4*n+3,n+1). The series identity identifies it with a(n). The adjacent-binomial identity changes it to three times binomial(4*n+3,n), which has the same parity.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.choose_shift`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.quartic_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.reflection_linear`
- Dependency: [D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity](AbsoluteReciprocalCubeParity.md)
