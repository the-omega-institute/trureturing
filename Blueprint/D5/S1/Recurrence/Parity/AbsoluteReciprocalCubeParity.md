# Absolute Reciprocal Cubes and Binomial Parity

## Abstract

The coefficients of OEIS A380709 have Hanna's conjectured binomial parity.

The generating equation and conjecture are recorded in hanna2025a380709. Write A for generatingSeries. The series A, B, F, and P(r) have integer coefficients, X is the indeterminate, and n and r are natural numbers. The auxiliary series Q and H used in the proof have coefficients in ZMod(2).

The operator mk forms a power series from its coefficient function, coeff(n,F) extracts its degree-n coefficient, and abs is integer absolute value. The operator invOfUnit(F,1) is Mathlib's power-series inverse with unit parameter 1. The operator map applies a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)). The operator choose is Nat.choose, with natural subtraction in its upper index. The operator ofNat denotes Int.ofNat and embeds a natural number into the integers, while zmodCast embeds it into ZMod(2). Remainders in lucas_recursion_q are natural remainders; those in hanna_conjecture are integer remainders.

**Definition 1.1 (Coefficientwise absolute value).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{absSeries}\left(F\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{abs}\left(\operatorname{coeff}\left(n, F\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.absSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Absolute value is applied to each reciprocal coefficient before cubing.

**Definition 1.2 (The stabilized coefficient sequence).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall r: \mathbb{N}, \operatorname{P}\left(r + 1\right) = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(\operatorname{P}\left(r\right), 1\right)\right))^{3}\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximations P start at one. Inversion of series with constant coefficient one, coefficientwise absolute value, and cubing preserve coefficient agreement. Multiplication by X increases the degree of agreement, so coefficient n stabilizes by step n+1.

**Definition 1.3 (The generating series).**

$$A = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series A has the stabilized integer coefficients a(n).

**Theorem 1.4 (The exact functional equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (A = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(A, 1\right)\right))^{3})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization proves the functional equation with constant coefficient one. The inverse is therefore the reciprocal of A.

**Theorem 1.5 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B = 1 + X \cdot (\operatorname{absSeries}\left(\operatorname{invOfUnit}\left(B, 1\right)\right))^{3}) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two fixed-point equations extend agreement by one degree. Induction gives agreement in every degree and hence equality.

**Theorem 1.6 (Three Lucas recursions).**

$$\forall r: \mathbb{N}, (\operatorname{choose}\left(4 \cdot \left(4 \cdot r + 1\right) + 1, 4 \cdot r + 1\right) \bmod 2 = \operatorname{choose}\left(4 \cdot r + 1, r\right) \bmod 2) \land ((\operatorname{choose}\left(4 \cdot \left(4 \cdot r + 3\right) + 1, 4 \cdot r + 3\right) \bmod 2 = 0) \land (\operatorname{choose}\left(4 \cdot 2 \cdot r + 1, 2 \cdot r\right) \bmod 2 = (\operatorname{if} (r = 0) \operatorname{then} 1 \operatorname{else} 0)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.lucas_recursion_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's binary Lucas congruence gives the two odd-index formulas. For a positive even index, repeated halving reduces choose(4r,r) to a binomial coefficient with even upper and odd lower index, which vanishes modulo two.

**Theorem 1.7 (Identification with the binomial parity series).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto (\operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} \operatorname{zmodCast}\left(\operatorname{choose}\left(4 \cdot n - 1, n\right), \operatorname{ZMod}\left(2\right)\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute values disappear modulo two. If f is the reduction of A and U its reciprocal, the equation gives U=1+X*U^4 and f=f^2+X*U^2. The Lucas recursions and Frobenius give Q=1+X*Q^4 when coefficient n of Q is choose(4n+1,n) modulo two. Factoring the difference of the quartic equations gives Q=U by cancellation of a series with unit constant coefficient. The two Lucas recursions for the displayed binomial series H give H=H^2+X*Q^2. Thus (1-f-H)*(f-H)=0. The first factor has constant coefficient -1 and is a unit, proving f=H.

**Theorem 1.8 (The constant coefficient).**

$$\operatorname{a}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.a_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact equation gives a(0)=1. This represents the convention binomial(-1,0)=1 without using natural subtraction at index zero.

**Theorem 1.9 (Hanna's A380709 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(n\right) \bmod 2 = \operatorname{ofNat}\left(\operatorname{choose}\left(4 \cdot n - 1, n\right)\right) \bmod 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380709-absolute-reciprocal-cube-parity` (proved) by `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380709-absolute-reciprocal-cube-parity","declaration_gid":"D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A380709, g.f. satisfying A(x) = 1 + x*abs(1/A(x))^3*. URL: <https://oeis.org/A380709>.

*Commentary.*

At each positive index, coefficient extraction from the reduction identity gives equality in ZMod(2). Mathlib identifies this equality with equality of the two integer remainders modulo two.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.a_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.absSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.lucas_recursion_q`
- Truth anchor: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.mod_two_identity`
