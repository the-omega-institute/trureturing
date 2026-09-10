# Square-Denominator Reversion and Dyadic Support

## Abstract

Hanna's A380678 series has odd coefficients exactly at the indices of A027383.

Paul D. Hanna's entry hanna2025a380678 specifies A(x-A(x)^2/(1-A(x)^2))=x. Its conjecture says that, for n at least one, a(n) is odd exactly when n=3*2^m-2 or n=4*2^m-2 for a natural m. The equivalent formulas below use n+2, since the two products are at least three and four respectively.

A denotes generatingSeries and T denotes its private approximations, all over the integers. X is the indeterminate. The operator coeff(n,f) extracts a coefficient, mk constructs a series from its coefficient function, and subst(f,g) composes f with g. The operation invOfUnit(f,1) is the formal power-series inverse with prescribed constant unit one; every denominator used here has constant coefficient one. All indices and exponents are natural numbers.

P denotes the imported lacunarySeries from D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity. It has coefficients in ZMod(2), with coefficient one exactly when n+2=3*2^m or n+2=4*2^m for some natural m, and zero otherwise. The operator map applies its ring homomorphism coefficientwise; intCastRingHom(ZMod(2)) is the canonical map from the integers.

**Definition 1.1 (The integral generating series).**

$$\begin{aligned}\operatorname{T}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{T}\left(n + 1\right) = \operatorname{T}\left(n\right) + X - (\operatorname{subst}\left(\operatorname{T}\left(n\right), X - (((\operatorname{T}\left(n\right))^{2}) \cdot (\operatorname{invOfUnit}\left(1 - ((\operatorname{T}\left(n\right))^{2}), 1\right)))\right))\\A = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{T}\left(n + 1\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For zero-constant f and g, clearing the unit denominators factors the difference of f^2/(1-f^2) and g^2/(1-g^2) as (f-g)(f+g) times the two inverses. The factor f+g has zero constant coefficient, so the inner arguments gain one degree of agreement. Substitution by an argument with linear coefficient one preserves the first coefficient of a difference. Thus the displayed transformation gains one degree of agreement, and its diagonal coefficient limit is well defined.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the coefficient of degree n in A.

**Theorem 1.3 (The OEIS equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left(A, X - (((A)^{2}) \cdot (\operatorname{invOfUnit}\left(1 - ((A)^{2}), 1\right)))\right) = X))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient limit is fixed by f+X-subst(f,X-f^2/(1-f^2)). Rearranging gives exactly the functional equation in hanna2025a380678. The approximations have zero constant coefficient, and their stable linear coefficient is one.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\operatorname{subst}\left(B, X - (((B)^{2}) \cdot (\operatorname{invOfUnit}\left(1 - ((B)^{2}), 1\right)))\right) = X) \implies (B = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every zero-constant solution is fixed by the same transformation. Induction on the degree of agreement proves equality with A. In particular, this applies under both displayed normalization hypotheses.

**Theorem 1.5 (Reduction to the imported support series).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = P$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the integral equation commutes with substitution and the inverse of its unit denominator. In characteristic two, 1-f^2=(1-f)^2. Cancellation of this unit shows that its inverse is invOfUnit(1-f,1)^2. Therefore the imported lacunary_reversion identity for P is also the square-denominator equation. The imported lacunary_quadratic identity gives constant coefficient zero. Applying the same degree-contraction uniqueness argument over ZMod(2) identifies the reduction of A with P.

**Theorem 1.6 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists m: \mathbb{N}, (n + 2 = (3) \cdot ((2)^{m}) \lor n + 2 = (4) \cdot ((2)^{m})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380678-quadratic-square-reversion-dyadic-support-parity` (proved) by `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380678-quadratic-square-reversion-dyadic-support-parity","declaration_gid":"D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A380678, g.f. satisfying A(x - A(x)^2/(1 - A(x)^2)) = x*. URL: <https://oeis.org/A380678>.

*Commentary.*

Extracting coefficient n from the reduction identity gives the indicator of the two dyadic families. Mathlib's intCast_eq_one_iff_odd identifies an integer's image being one in ZMod(2) with its being odd.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity](../Invariants/QuadraticReversionDyadicSupportParity.md)
