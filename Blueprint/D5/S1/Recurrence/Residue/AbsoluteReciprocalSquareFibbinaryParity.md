# Absolute Reciprocal Squares and Fibbinary Parity

## Abstract

The positive-index coefficients of OEIS A380708 are odd exactly at twice a fibbinary number plus one.

The equation and conjecture are recorded in hanna2025a380708. Write A for generatingSeries. The imported symbol absSeries is D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries: it takes the integer absolute value of each coefficient before squaring. The imported predicate Fibbinary is D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity.Fibbinary. It asserts n bitwise-and (n shifted right by one) equals zero, equivalently that no two adjacent binary digits are both one.

Write T for the imported integer series D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries. The series A, B, T, and the auxiliary approximations P(r) have integer coefficients; P(r) denotes the private approximation(r). All indices are natural numbers and X is the indeterminate. The operator coeff extracts a coefficient, constantCoeff extracts the constant coefficient, and mk forms a series from its coefficient function. The operator invOfUnit(F,1) is Mathlib's inverse with unit parameter one. The operator map acts coefficientwise; intCastRingHom(ZMod(2)) is Int.castRingHom(ZMod(2)), and cast2 embeds a natural number into ZMod(2). The operator expand(2,F) substitutes X^2 for X, with its nonzero parameter proof implicit. The operator choose denotes Nat.choose.

**Definition 1.1 (The stabilized coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{P}\left(0\right) = 1\\\forall r: \mathbb{N}, \operatorname{P}\left(r + 1\right) = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(\operatorname{P}\left(r\right), 1\right)\right))^{2}\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inversion with constant coefficient one, coefficientwise absolute value, and squaring preserve agreement below a given degree. Multiplication by X increases that degree by one. Thus the coefficient at n stabilizes by approximation n+1.

**Definition 1.2 (The integer generating series).**

$$A = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series A has coefficient function a.

**Theorem 1.3 (The exact functional equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(A, 1\right)\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization establishes the equation in every degree. Its constant coefficient is one, so invOfUnit(A,1) is the reciprocal of A.

**Theorem 1.4 (Uniqueness of the solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(B, 1\right)\right))^{2}) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two fixed-point equations increase coefficient agreement by one degree. Induction proves agreement in every degree, hence B=A.

**Theorem 1.5 (Reduction to the ternary series).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = 1 + X \cdot \operatorname{expand}\left(2, \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute values disappear modulo two. If F is the reduction of A and U is its reciprocal, then F=1+X*U^2. Multiplication by U gives 1=U+X*U^3, hence U=1+X*U^3 in characteristic two. The imported generating_equation and strip3_mod_two give the same cubic equation for the reduction V of T. Factoring the difference gives (U-V)*(1-X*(U^2+U*V+V^2))=0. The second factor has constant coefficient one and is a unit, so U=V. Frobenius replaces V^2 by expand(2,V), proving the displayed identity.

**Theorem 1.6 (Binomial parity and adjacent binary digits).**

$$\forall f: \mathbb{N}, (\operatorname{cast2}\left(\operatorname{choose}\left(3 \cdot f, f\right)\right) = 1) \iff \operatorname{Fibbinary}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.choose_three_odd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported choose_three_lucas theorem reduces the binomial coefficient at 2r or 4r+1 to that at r, and makes it zero at 4r+3. The bitwise definition gives the same three rules for Fibbinary. Strong induction, starting with zero, proves the equivalence.

**Theorem 1.7 (Hanna's A380708 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists f: \mathbb{N}, (\operatorname{Fibbinary}\left(f\right)) \land (n = 2 \cdot f + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380708-absolute-reciprocal-square-fibbinary-parity` (proved) by `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380708-absolute-reciprocal-square-fibbinary-parity","declaration_gid":"D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A380708, g.f. satisfying A(x) = 1 + x*abs(1/A(x))^2*. URL: <https://oeis.org/A380708>.

*Commentary.*

At a positive even index the shifted expansion has coefficient zero. At index 2f+1 it has the degree-f coefficient of the reduction of T. The imported mod_two_identity identifies this coefficient with choose(3f,f) in ZMod(2). The binomial equivalence therefore proves exactly the asserted fibbinary support of the odd coefficients.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.a`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.choose_three_odd_iff`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity](../Invariants/AbsoluteReciprocalSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity](../Parity/FibbinarySquareSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity](../Parity/StripThreeTernaryCatalanParity.md)
