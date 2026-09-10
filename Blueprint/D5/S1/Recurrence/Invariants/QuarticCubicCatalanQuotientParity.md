# Hanna's Quartic-Cubic Quotient Parity

## Abstract

The coefficients of OEIS A384270 are odd exactly at powers of two.

The entry cited in hanna2025a384270 specifies A(x)=A(x^4+4xA(x)^4)/A(x^3+3xA(x)^3) and conjectures the parity support. The denominator has zero constant coefficient and is not a unit in the integer power-series ring. The defining equation below is therefore cross-multiplied, with A(0)=0 and a(1)=1.

Indices are natural numbers. PowerSeries(Z) is the integer formal power-series ring, X is its indeterminate, and all series powers are ring powers. The notation subst(B,U) substitutes U into B; coeff(n,B) extracts a coefficient, and mk constructs a series from its coefficient function. The auxiliary symbols b, approximation, T, and u describe the private construction used in the definition of a.

**Definition 1.1 (The integral coefficient construction).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, X \cdot b\right)\\b = \operatorname{mk}\left((j: \mathbb{N} \mapsto \operatorname{coeff}\left(j, \operatorname{approximation}\left(j + 1\right)\right))\right)\\\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = \operatorname{T}\left(\operatorname{approximation}\left(d\right)\right)\\\forall t: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{T}\left(t\right) = t + (1 + 4 \cdot X \cdot t^{4}) \cdot \operatorname{subst}\left(t, \operatorname{u}\left(4, t\right)\right) - t \cdot (1 + 3 \cdot X \cdot t^{3}) \cdot \operatorname{subst}\left(t, \operatorname{u}\left(3, t\right)\right)\\\forall p: \mathbb{N}, \forall t: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{u}\left(p, t\right) = X^{p} \cdot (1 + p \cdot X \cdot t^{p})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The approximations start at one and apply T. Their constant coefficient remains one. Agreement below degree d improves to agreement below degree d+1, since each inner series is divisible by X squared and the uncancelled differences carry an additional X. The diagonal coefficients define b, and a is the coefficient function of Xb. Every operation in this construction is integral; no division occurs.

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer generating series has coefficient function a.

**Theorem 1.3 (The normalized functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries} \cdot \operatorname{subst}\left(\operatorname{generatingSeries}, X^{3} + 3 \cdot X \cdot \operatorname{generatingSeries}^{3}\right) = \operatorname{subst}\left(\operatorname{generatingSeries}, X^{4} + 4 \cdot X \cdot \operatorname{generatingSeries}^{4}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal limit is a fixed point of T. Writing A=Xb and cancelling X^4 identifies this fixed-point equation with the displayed cross-multiplied equation. The constant and linear coefficients follow from the constant coefficient of b being one.

**Theorem 1.4 (Uniqueness of the integer series).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies (f \cdot \operatorname{subst}\left(f, X^{3} + 3 \cdot X \cdot f^{3}\right) = \operatorname{subst}\left(f, X^{4} + 4 \cdot X \cdot f^{4}\right)) \implies f = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor any series with zero constant coefficient as Xb. The linear coefficient hypothesis gives b(0)=1. Cancelling X^4 turns its equation into the fixed-point identity for T. Induction on coefficient agreement proves uniqueness. This argument also holds over ZMod(2).

**Theorem 1.5 (The parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a384270-quartic-cubic-catalan-quotient-parity` (proved) by `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a384270-quartic-cubic-catalan-quotient-parity","declaration_gid":"D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A384270, g.f. satisfying A(x) = A(x^4 + 4*x*A(x)^4)/A(x^3 + 3*x*A(x)^3)*. URL: <https://oeis.org/A384270>.

*Commentary.*

Over ZMod(2), let C be the compositional inverse of X+X^2. Then C+C^2=X, so X^3+XC^3=C^3+C^6. Substituting C^3 into the left inverse identity gives C(C^3+C^6)=C^3. Frobenius gives C(X^4)=C^4, hence C satisfies the reduced functional equation. Uniqueness identifies the reduction of generatingSeries with C. Its quadratic identity makes the coefficient at an even index equal to that at half the index and makes every odd index above one vanish. Strong induction gives exactly the powers of two.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.hanna_conjecture`
