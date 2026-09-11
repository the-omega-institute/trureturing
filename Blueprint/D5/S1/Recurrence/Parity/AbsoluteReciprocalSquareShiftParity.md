# Absolute Reciprocal-Square Shift Parity

## Abstract

The absolute reciprocal-square series satisfies conjecture C.1 of OEIS A384267.

The entry cited in hanna2025a384267 defines a(n) as the absolute value of the coefficient of x^n in 1+x/A(x)^2, where A is its generating series. Conjecture C.1 states the binomial-quotient congruence at every positive index.

Indices and binomial coefficients are natural numbers; index subtraction is natural subtraction. The function div is natural integer division, int is the natural-to-integer cast, and mod is integer remainder. The coefficients a(n) are integers. A denotes generatingSeries, P(n) denotes its local approximations, and mk constructs a series from a coefficient function. The imported absSeries from AbsoluteReciprocalSquareParity takes absolute values coefficientwise. The expression invOfUnit(B,1) is the formal unit inverse with prescribed constant coefficient one. T denotes the integer generatingSeries from StripThreeTernaryCatalanParity. The map pi is Int.castRingHom(ZMod(2)); map(pi,B) applies it to each coefficient. The operator expand(2,B) substitutes X^2 for X.

**Definition 1.1 (The stabilized coefficient sequence).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{P}\left(n + 1\right) = \operatorname{absSeries}\left(1 + X \cdot \operatorname{invOfUnit}\left(\operatorname{P}\left(n\right)^{2}, 1\right)\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by X makes the reciprocal-square step increase coefficient agreement by one degree. The diagonal coefficients therefore stabilize under the displayed iteration.

**Definition 1.2 (The integer generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series has coefficient a(n) at degree n.

**Theorem 1.3 (The defining equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A = \operatorname{absSeries}\left(1 + X \cdot \operatorname{invOfUnit}\left(A^{2}, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement with every finite approximation gives the fixed-point equation. Every approximation has constant coefficient one.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B = \operatorname{absSeries}\left(1 + X \cdot \operatorname{invOfUnit}\left(B^{2}, 1\right)\right)) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of two unit inverses is controlled by the difference of their original series. Induction on the degree of coefficient agreement then identifies any normalized solution with A.

**Theorem 1.5 (The shifted ternary Catalan series).**

$$\operatorname{map}\left(pi, A\right) = 1 + X \cdot \operatorname{expand}\left(2, \operatorname{map}\left(pi, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute values disappear modulo two. Multiplying the reduced equation by A^2 gives F^3=F^2+X for F=map(pi,A). Thus U=F+1 satisfies U=X+U^3 with zero constant coefficient. The imported strip3_mod_two and generating_equation show that map(pi,T) satisfies the ternary Catalan equation, so V=X expand(2,map(pi,T)) also satisfies V=X+V^3. The factor 1-U^2-UV-V^2 has constant coefficient one; cancellation in the difference of the two cubic equations proves U=V.

**Theorem 1.6 (The constant coefficient).**

$$\operatorname{a}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.a_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalization of A gives a(0)=1.

**Theorem 1.7 (Exact binomial division).**

$$\forall n: \mathbb{N}, (0 < n) \implies (3 \cdot n - 1 \mid \operatorname{choose}\left(3 \cdot n - 1, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integers n and 3n-1 are coprime. The standard identity (3n-1) choose(3n-2,n-1)=n choose(3n-1,n) therefore proves the asserted divisibility.

**Theorem 1.8 (The quotient at odd indices).**

$$\forall r: \mathbb{N}, \operatorname{div}\left(\operatorname{choose}\left(6 \cdot r + 2, 2 \cdot r + 1\right), 6 \cdot r + 2\right) = \operatorname{div}\left(\operatorname{choose}\left(6 \cdot r + 1, 2 \cdot r\right), 2 \cdot r + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_div_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact division and cancellation give n times the quotient equal to choose(3n-2,n-1). Substituting n=2r+1 gives the displayed equality.

**Theorem 1.9 (The quotient at positive even indices).**

$$\forall r: \mathbb{N}, (0 < r) \implies (2 \mid \operatorname{div}\left(\operatorname{choose}\left(6 \cdot r - 1, 2 \cdot r\right), 6 \cdot r - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_div_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since 6r-1 is odd, exact division preserves parity. Lucas reduction sends choose(6r-1,2r) to choose(3r-1,r) modulo two. The identity 3 choose(3r-1,r)=2 choose(3r,r), valid for r positive, makes this last coefficient even.

**Theorem 1.10 (Hanna's conjecture C.1).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{a}\left(n\right) \bmod 2 = \operatorname{int}\left(\operatorname{div}\left(\operatorname{choose}\left(3 \cdot n - 1, n\right), 3 \cdot n - 1\right)\right) \bmod 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a384267-absolute-reciprocal-square-shift-parity` (proved) by `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a384267-absolute-reciprocal-square-shift-parity","declaration_gid":"D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A384267, a(n) = abs([x^n] 1 + x/A(x)^2), conjecture C.1*. URL: <https://oeis.org/A384267>.

*Commentary.*

The series identity gives zero at positive even indices and choose(3r,r) modulo two at index 2r+1, using the imported mod_two_identity for T. The even quotient is even. At odd indices, multiplication by 2r+1 preserves parity, and Lucas reduction sends choose(6r+1,2r) to choose(3r,r). These two cases establish the stated congruence for every positive n.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.a_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_div_even`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_div_odd`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.ternary_dvd`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity](../Invariants/AbsoluteReciprocalSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity](StripThreeTernaryCatalanParity.md)
