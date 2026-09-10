# Hanna's Half-Scaled Reflection Parity

## Abstract

The odd coefficients of OEIS A389540 occur exactly at powers of two.

The entry cited in hanna2025a389540 defines A(x) by A(x)^2=A(2x-2A(x))/2 and conjectures that a(n) is odd exactly when n is a power of two. The integer series below has constant coefficient zero, linear coefficient one, and satisfies the equation after multiplication by two.

All indices are natural numbers, and r and a take integer values. R denotes inverseSeries and A denotes generatingSeries in the integer formal power-series ring PowerSeries(Z), with indeterminate X. The operator mk constructs a series from its coefficient function, coeff(n,B) extracts a coefficient, and subst(B,C) substitutes C into B. The notation inv(R) denotes Mathlib's substInvOfIsUnit applied to the proved unit linear coefficient of R; it is a compositional inverse. The operator div is integer Euclidean division, and subNat is natural subtraction truncated at zero. Multiplication by two is repeated addition.

**Definition 1.1 (The inverse coefficients).**

$$\forall n: \mathbb{N}, \operatorname{r}\left(n\right) = \operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} \operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} \operatorname{if} (2 \mid n) \operatorname{then} 2^{\operatorname{subNat}\left(\operatorname{div}\left(n, 2\right), 1\right)} \cdot \operatorname{r}\left(\operatorname{div}\left(n, 2\right)\right) \operatorname{else} 0$$

*Formalization.* `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.r` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion fixes r(0)=0 and r(1)=1. Every other even index is reduced to half its value with the displayed integral power-of-two multiplier; every other odd index has coefficient zero.

**Definition 1.2 (The inverse series).**

$$R = \operatorname{mk}\left(r\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.inverseSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series R has coefficient function r. Its constant coefficient is zero and its linear coefficient is one, so Mathlib's integral compositional inverse applies.

**Definition 1.3 (The OEIS coefficients).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{inv}\left(R\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient a(n) is the nth integer coefficient of the compositional inverse of R.

**Definition 1.4 (The generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series A has coefficient function a and is the compositional inverse of R in both orders.

**Theorem 1.5 (The defining equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (2 \cdot A^{2} = \operatorname{subst}\left(A, (2 \cdot X - 2 \cdot A)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursion for r gives R(2X^2)=2R-2X coefficient by coefficient. Substituting A and using R(A)=X gives R(2A^2)=2X-2A. Composing with A gives the displayed equation, together with the two normalization conditions.

**Theorem 1.6 (Uniqueness among normalized integer series).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (\operatorname{coeff}\left(1, B\right) = 1) \implies (2 \cdot B^{2} = \operatorname{subst}\left(B, (2 \cdot X - 2 \cdot B)\right)) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized integer solution B has an integral compositional inverse S. Its equation implies S(2X^2)=2S-2X. Coefficient comparison and strong induction force S to have coefficient function r. Thus S=R and B=A.

**Theorem 1.7 (The A389540 parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389540-half-scaled-reflection-parity` (proved) by `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389540-half-scaled-reflection-parity","declaration_gid":"D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389540, g.f. satisfying A(x)^2 = A(2*x - 2*A(x))/2*. URL: <https://oeis.org/A389540>.

*Commentary.*

The inverse-coefficient recursion reduces R to X+X^2 modulo two. Reducing R(A)=X therefore gives A+A^2=X over ZMod(2). Mathlib's Frobenius identity identifies squaring with substitution of X^2. At index one the coefficient is odd; at every larger positive even index its parity equals the parity at half the index, and at every larger odd index it is even. Strong induction gives precisely the powers of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.inverseSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.r`
