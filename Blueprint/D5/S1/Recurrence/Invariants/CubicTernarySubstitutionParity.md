# Hanna's Cubic Ternary Substitution Parity

## Abstract

The odd coefficients of OEIS A375439 occur exactly at powers of three and twice powers of three.

The entry cited in hanna2024a375439 defines A(x) by A(x)=x+x^2+(2A(x)^3+A(x^3))/3 and conjectures its parity support. The integer series below has constant coefficient zero and satisfies that equation after multiplication by three.

All indices are natural numbers. PowerSeries(Z) denotes the integer formal power-series ring, X its indeterminate, and powers are ordinary ring powers. The notation subst(B,C) means substitution of C into B. The operator coeff(n,B) extracts a coefficient, mk constructs a series from its coefficient function, and div is integer Euclidean division. Multiplication by a natural number denotes repeated addition. The map rho reduces every integer coefficient to ZMod(3).

**Theorem 1.1 (Cubic Frobenius congruence).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{rho}\left(B^{3}\right) = \operatorname{rho}\left(\operatorname{subst}\left(B, X^{3}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.cube_congr_subst_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's multivariate power-series Frobenius identity identifies expansion by three with cubing after reduction modulo three. Frobenius is the identity on ZMod(3). Thus every coefficient of 2B^3+B(X^3) is divisible by three, for every integer series B.

**Definition 1.2 (The stabilized integer coefficients).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(n + 1\right)\right)\\\operatorname{approximation}\left(0\right) = 0\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = X + X^{2} + \operatorname{mk}\left((j: \mathbb{N} \mapsto \operatorname{div}\left(\operatorname{coeff}\left(j, (2 \cdot \operatorname{approximation}\left(d\right)^{3} + \operatorname{subst}\left(\operatorname{approximation}\left(d\right), X^{3}\right))\right), 3\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximation starts at zero and repeatedly applies the displayed transformation. Each division by three is exact by the Frobenius congruence. For series with zero constant coefficient, agreement below degree d improves to agreement below degree d+1. Coefficient n has therefore stabilized at approximation n+1.

**Definition 1.3 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series is the integer power series with coefficient function a.

**Theorem 1.4 (The defining OEIS equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (3 \cdot \operatorname{generatingSeries} = 3 \cdot (X + X^{2}) + 2 \cdot \operatorname{generatingSeries}^{3} + \operatorname{subst}\left(\operatorname{generatingSeries}, X^{3}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized series agrees to every finite degree with later approximations. Degree contraction makes it a fixed point. Exact division then gives the displayed integer identity and the zero constant coefficient.

**Theorem 1.5 (Uniqueness with zero constant coefficient).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (3 \cdot B = 3 \cdot (X + X^{2}) + 2 \cdot B^{3} + \operatorname{subst}\left(B, X^{3}\right)) \implies B = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer equation first implies that B is a fixed point of the same transformation. Induction on the degree of coefficient agreement then identifies B with generatingSeries.

**Theorem 1.6 (The A375439 parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, (n = 3^{k} \lor n = 2 \cdot 3^{k})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a375439-cubic-ternary-substitution-parity` (proved) by `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a375439-cubic-ternary-substitution-parity","declaration_gid":"D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A375439, expansion of A(x) = x + x^2 + (2*A(x)^3 + A(x^3))/3*. URL: <https://oeis.org/A375439>.

*Commentary.*

Reducing the coefficient equation modulo two removes the cubic term. The coefficients at indices one and two are odd. At every larger positive index, oddness is equivalent to divisibility of the index by three and oddness at one third of that index. Strong induction gives exactly the two displayed families.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.cube_congr_subst_three`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.hanna_conjecture`
