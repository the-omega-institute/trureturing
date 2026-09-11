# Quadratic Reversion and Dyadic Support

## Abstract

Hanna's A389476 series has odd coefficients exactly at the indices of A027383.

Paul D. Hanna's OEIS entry hanna2025a389476 defines A(x-A(x)^2/(1-A(x))^2)=x and conjectures that a(n) is odd precisely at indices 3*2^m-2 or 4*2^m-2 for natural m. The formulas below use n+2=3*2^m or n+2=4*2^m. The products are at least three and four, so this is equivalent to the natural-subtraction formulation.

A denotes generatingSeries, U denotes innerSeries, and P denotes lacunarySeries. The first two series and the approximation T have integer coefficients; P has coefficients in ZMod(2). X is the indeterminate in the indicated coefficient ring. PowerSeries(R) denotes formal power series over R, coeff(n,f) extracts a coefficient, and mk constructs a series from its coefficient function. The notation subst(f,g) means f composed with g. The operation invOfUnit(f,1) is Mathlib's power-series inverse with prescribed constant unit one. Every denominator here has constant coefficient one. All indices and exponents are natural numbers.

**Definition 1.1 (The integer series).**

$$\begin{aligned}\operatorname{T}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{T}\left(n + 1\right) = \operatorname{T}\left(n\right) + X - (\operatorname{subst}\left(\operatorname{T}\left(n\right), X - (((\operatorname{T}\left(n\right)) \cdot (\operatorname{invOfUnit}\left(1 - (\operatorname{T}\left(n\right)), 1\right)))^{2})\right))\\A = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{T}\left(n + 1\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from zero, the transformation f+X-subst(f,u(f)), where u(f)=X-(f*invOfUnit(1-f,1))^2, preserves zero constant coefficient. If two zero-constant inputs agree below degree d, their inner arguments agree below degree d+1. Substitution by an argument with linear coefficient one preserves the first coefficient of a difference. The transformation therefore gains one degree of agreement, making the displayed coefficientwise construction stable.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer sequence consists of the coefficients of A.

**Definition 1.3 (The inner argument).**

$$U = X - (((A) \cdot (\operatorname{invOfUnit}\left(1 - (A), 1\right)))^{2})$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.innerSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The square of the product of A and the prescribed inverse gives A^2/(1-A)^2 in the ring of formal power series.

**Theorem 1.4 (The generating equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((\operatorname{subst}\left(A, U\right) = X) \land (((1 - (A))^{2}) \cdot (X - (U)) = (A)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives the reversion equation and constant coefficient zero. The linear coefficient is one. Multiplication by the square of the unit denominator gives the last conjunct, identifying U with the rational expression in Hanna's equation.

**Theorem 1.5 (Uniqueness of integer reversion).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{subst}\left(f, X - (((f) \cdot (\operatorname{invOfUnit}\left(1 - (f), 1\right)))^{2})\right) = X) \implies (f = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every zero-constant solution is fixed by the same transformation. Induction on the degree of agreement proves equality with A. A separate linear-coefficient hypothesis is unnecessary.

**Definition 1.6 (The dyadic support series).**

$$P = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (\exists m: \mathbb{N}, (n + 2 = (3) \cdot ((2)^{m}) \lor n + 2 = (4) \cdot ((2)^{m}))) \operatorname{then} 1 \operatorname{else} 0)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the indicator of the union of the two dyadic families, with values zero and one in ZMod(2).

**Theorem 1.7 (The quadratic identity).**

$$P = X + (X)^{2} + ((X)^{2}) \cdot ((P)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunary_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support contains 1 and 2 and excludes 0. Beyond these indices, n+2 lies in the support exactly when n is even and n/2 lies in the support. Factoring a power of two from the defining equalities proves this equivalence. Frobenius identifies P^2 with subst(P,X^2), and coefficient extraction gives the quadratic identity.

**Theorem 1.8 (Reversion in characteristic two).**

$$\operatorname{subst}\left(P, X - (((P) \cdot (\operatorname{invOfUnit}\left(1 - (P), 1\right)))^{2})\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunary_reversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put z=P, v=invOfUnit(1-P,1), and r=X+(z*v)^2. Clearing the unit denominator in the quadratic identity gives (1+X)*r=z*v. Squaring gives r+X=(1+X^2)*r^2 and hence X=r+r^2+r^2*X^2. Composing the quadratic identity with r gives the same equation for subst(P,r). The factor r^2 increases the degree of agreement, so induction proves uniqueness and subst(P,r)=X. In characteristic two, r is Inner(P).

**Theorem 1.9 (Reduction equals the support series).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = P$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map the proved integer generating equation through the canonical homomorphism to ZMod(2). A unit-denominator cancellation shows that mapping commutes with the inner argument, and Mathlib's map_subst transports composition. The generic reversion uniqueness proof then identifies the reduced series with P.

**Theorem 1.10 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists m: \mathbb{N}, (n + 2 = (3) \cdot ((2)^{m}) \lor n + 2 = (4) \cdot ((2)^{m})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389476-quadratic-reversion-dyadic-support-parity` (proved) by `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389476-quadratic-reversion-dyadic-support-parity","declaration_gid":"D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389476, g.f. satisfying A(x - A(x)^2/(1 - A(x))^2) = x*. URL: <https://oeis.org/A389476>.

*Commentary.*

Extract coefficient n from the reduction identity. The coefficient of P is one exactly on its defining dyadic support, and an integer maps to one in ZMod(2) exactly when it is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.innerSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunarySeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunary_quadratic`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lacunary_reversion`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.mod_two_identity`
