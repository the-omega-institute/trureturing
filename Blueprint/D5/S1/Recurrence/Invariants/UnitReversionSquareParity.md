# Unit Reversion and Square Parity

## Abstract

The normalized integer solution of Hanna's A373312 equation has odd coefficients exactly at positive Mersenne indices.

Paul D. Hanna's OEIS entry hanna2024a373312 specifies A(x)^2=A(x*A(x)/(1-A(x))^2) and conjectures that a(n) is odd exactly when n=2^k-1 for k at least one. The normalization is A(0)=0 and a(1)=1.

Here A denotes generatingSeries and U denotes innerSeries. PowerSeries(R) denotes formal power series over R, X is the indeterminate, coeff(n,f) extracts coefficient n, and mk builds a series from a coefficient function. The notation subst(f,g) means f composed with g. The operation invOfUnit(f,1) is the power-series inverse with prescribed constant unit 1; every denominator used below has constant coefficient 1. The auxiliary P(n), r(f), and q(f) in the construction are integer power series. Indices and exponents are natural numbers, including subtraction in 2^k-1; a(n) is an integer. In the mod-two identity X and the arithmetic lie over ZMod(2).

**Definition 1.1 (Construction of the integer series).**

$$\begin{aligned}\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{r}\left(f\right) = \operatorname{invOfUnit}\left(1 - X \cdot f, 1\right)\\\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{q}\left(f\right) = (X)^{2} \cdot f \cdot (\operatorname{r}\left(f\right))^{2}\\\operatorname{P}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{P}\left(n + 1\right) = (\operatorname{r}\left(\operatorname{P}\left(n\right)\right))^{2} \cdot \operatorname{subst}\left(\operatorname{P}\left(n\right), \operatorname{q}\left(\operatorname{P}\left(n\right)\right)\right)\\A = X \cdot \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{P}\left(n\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write A=X*B. The equation B=r(B)^2*subst(B,q(B)) contracts agreement by one degree for series of constant coefficient 1. The inverse r(B) gains a degree of agreement, while q(B) has order at least two, so outer substitution doubles the degree of agreement. Consequently coefficient n of P(n) has stabilized, and these coefficients define B.

**Definition 1.2 (The integer coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence is defined by coefficient extraction from A.

**Definition 1.3 (The unit-denominator argument).**

$$U = X \cdot A \cdot (\operatorname{invOfUnit}\left(1 - A, 1\right))^{2}$$

*Formalization.* `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.innerSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Since A has zero constant coefficient, 1-A is a unit. Mathlib's invOfUnit_mul identifies the prescribed inverse with the denominator in Hanna's functional equation.

**Theorem 1.4 (The normalized generating equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((A)^{2} = \operatorname{subst}\left(A, U\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives B=r(B)^2*subst(B,q(B)). Multiplication by X^2*B and the substitution multiplication law give A^2=subst(A,U). The initial constant coefficient of B is 1, giving both normalization identities.

**Theorem 1.5 (Uniqueness over the integers).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies ((f)^{2} = \operatorname{subst}\left(f, X \cdot f \cdot (\operatorname{invOfUnit}\left(1 - f, 1\right))^{2}\right)) \implies f = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero constant coefficient gives f=X*B, and the linear coefficient gives B(0)=1. Cancellation of the nonzero factor X^2*B turns the functional equation into the same contracting fixed-point equation. Induction on the degree of agreement identifies B with the constructed series.

**Theorem 1.6 (The lacunary fixed-point equation).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = X + X \cdot \operatorname{subst}\left(\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(2\right)\right), A\right), (X)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.mod_two_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map the proved generating equation to ZMod(2). Frobenius identifies A^2 with subst(A,X^2). Mathlib's compositional inverse cancels the outer series A, whose linear coefficient is 1, and gives U=X^2. Clearing the unit denominator and cancelling X yields A=X*(1-A)^2. Characteristic two and Frobenius give the displayed equation.

**Theorem 1.7 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff \exists k: \mathbb{N}, (1 \le k) \land (n = (2)^{k} - 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a373312-unit-reversion-square-parity` (proved) by `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a373312-unit-reversion-square-parity","declaration_gid":"D5/S1/Recurrence/Invariants/UnitReversionSquareParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A373312, g.f. satisfying A(x)^2 = A(x*A(x)/(1-A(x))^2)*. URL: <https://oeis.org/A373312>.

*Commentary.*

The fixed-point equation gives coefficient 1 equal to 1. For n positive, coefficient n+1 is zero when n is odd, and is coefficient n/2 when n is even. The index n+1 is a positive Mersenne index exactly when n is even and n/2 is a positive Mersenne index. Strong induction, with constant coefficient zero, proves the support classification. An integer maps to 1 in ZMod(2) exactly when it is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.innerSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.mod_two_fixed`
