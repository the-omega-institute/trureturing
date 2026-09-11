# Absolute Reciprocal Squares and Binary Parity

## Abstract

The positive-index coefficients of OEIS A380710 are odd exactly at powers of two.

The generating equation and conjecture are recorded in hanna2025a380710. Write A for generatingSeries and C for CatalanCompositionSquareParity.catalanSeries. The series A, C, F, B, and P(r) have integer coefficients, X is the indeterminate, and all coefficient indices and exponents are natural numbers.

The operator mk forms a series from its coefficient function; coeff(n,F) extracts its degree-n coefficient. The scalar operator abs is integer absolute value. The operator invOfUnit(F,1) is Mathlib's power-series inverse with the unit 1 as constant-coefficient parameter. When the constant coefficient of F is one, its product with this inverse is one. The operator map applies a ring homomorphism coefficientwise, and intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)).

**Definition 1.1 (Coefficientwise absolute value).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{absSeries}\left(F\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{abs}\left(\operatorname{coeff}\left(n, F\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.absSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of absSeries(F) at each natural index n is the integer absolute value of the corresponding coefficient of F.

**Definition 1.2 (The stabilized coefficient sequence).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall r: \mathbb{N}, \operatorname{P}\left(r + 1\right) = 1 + X \cdot \operatorname{P}\left(r\right) \cdot \operatorname{absSeries}\left(\operatorname{invOfUnit}\left(\operatorname{P}\left(r\right)^{2}, 1\right)\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed recursion defines the auxiliary approximations P(r). The map gains one degree of coefficient agreement: powers, inverses with constant coefficient one, and coefficientwise absolute values preserve agreement, while multiplication by X shifts it. Thus the degree-n coefficient stabilizes by approximation n+1.

**Definition 1.3 (The generating series).**

$$A = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series A is formed from the stabilized integer coefficients a(n).

**Theorem 1.4 (The exact functional equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A = 1 + X \cdot A \cdot \operatorname{absSeries}\left(\operatorname{invOfUnit}\left(A^{2}, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient stabilization makes A a fixed point of the approximation map. Its constant coefficient is one, so the inverse in the equation is the reciprocal of A squared.

**Theorem 1.5 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies (B = 1 + X \cdot B \cdot \operatorname{absSeries}\left(\operatorname{invOfUnit}\left(B^{2}, 1\right)\right)) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any integer solution B with constant coefficient one agrees with A below degree zero. The fixed-point equations and degree contraction extend agreement by one degree at every step, proving B=A.

**Theorem 1.6 (Reduction to the shifted Catalan series).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = 1 + \operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), C\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In ZMod(2), the images of an integer and its absolute value coincide. Mapping the reciprocal-square identity and multiplying the defining equation by the reduced series gives its square equal to itself plus X. The frozen Catalan equation gives the same quadratic equation for 1+map(intCast(ZMod(2)),C). The difference of the two solutions is annihilated by one minus their sum. This factor has unit constant coefficient, so cancellation identifies the two solutions.

**Theorem 1.7 (Hanna's A380710 parity conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380710-absolute-reciprocal-square-parity` (proved) by `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380710-absolute-reciprocal-square-parity","declaration_gid":"D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A380710, g.f. satisfying A(x) = 1 + x*A(x)*abs(1/A(x)^2)*. URL: <https://oeis.org/A380710>.

*Commentary.*

At a positive index, adding the constant series one changes no coefficient. The reduction identity and the frozen binary_catalan theorem therefore give odd a(n) exactly when n is a power of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.absSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
