# Hanna's Absolute Reciprocal Geometric Parity

## Abstract

Every coefficient of OEIS A383377 above index one is even.

The entry cited in hanna2025a383377 defines A(x) as the sum of x^n times the coefficientwise absolute value of its nth reciprocal power, and conjectures evenness for n greater than one. The integer series below is constructed and proved to satisfy that equation uniquely among series with constant coefficient one.

All indices are natural numbers. PowerSeries(Z) denotes integer formal power series, X is its indeterminate, coeff(N,F) is coefficient N, and mk constructs a series from a coefficient function. The operation invOfUnit(F,1) is the unit inverse when the constant coefficient is one; powers are ordinary products of series. The symbol abs denotes integer absolute value. Each coefficient sum is finite: terms indexed above N contain X to a power greater than N and contribute zero at degree N. The map intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)); map(h,F) applies h to every coefficient of F.

**Theorem 1.1 (Multiplication preserves coefficient agreement).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall d: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), \forall u: \operatorname{PowerSeries}\left(R\right), \forall v: \operatorname{PowerSeries}\left(R\right), (\forall k: \mathbb{N}, (k < d) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, g\right))) \implies ((\forall k: \mathbb{N}, (k < d) \implies (\operatorname{coeff}\left(k, u\right) = \operatorname{coeff}\left(k, v\right))) \implies (\forall k: \mathbb{N}, (k < d) \implies (\operatorname{coeff}\left(k, f \cdot u\right) = \operatorname{coeff}\left(k, g \cdot v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.agree_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Products of two pairs of series agreeing below d also agree below d.

**Theorem 1.2 (Agree inv).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall d: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies ((\operatorname{constantCoeff}\left(g\right) = 1) \implies ((\forall j: \mathbb{N}, (j < d) \implies (\operatorname{coeff}\left(j, f\right) = \operatorname{coeff}\left(j, g\right))) \implies (\forall j: \mathbb{N}, (j < d) \implies (\operatorname{coeff}\left(j, \operatorname{invOfUnit}\left(f, 1\right)\right) = \operatorname{coeff}\left(j, \operatorname{invOfUnit}\left(g, 1\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.agree_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit inverses of normalized agreeing series agree through the same degree.

**Definition 1.3 (Coefficientwise absolute value).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{absSeries}\left(F\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{abs}\left(\operatorname{coeff}\left(n, F\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.absSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function is replaced by its integer absolute value.

**Definition 1.4 (Stabilized integer coefficients).**

$$\begin{aligned}\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = \operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{n \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, (X)^{n} \cdot \operatorname{absSeries}\left((\operatorname{invOfUnit}\left(\operatorname{approximation}\left(d\right), 1\right))^{n}\right)\right)))\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximation starts at one. Each successor is formed by the displayed finite coefficient sums. The transformation preserves constant coefficient one and improves agreement below d to agreement below d+1. Consequently coefficient n has stabilized by approximation n+1.

**Definition 1.5 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has the integer coefficient function a.

**Theorem 1.6 (The exact defining equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, \operatorname{generatingSeries}\right) = \sum_{n \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, (X)^{n} \cdot \operatorname{absSeries}\left((\operatorname{invOfUnit}\left(\operatorname{generatingSeries}, 1\right))^{n}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement with sufficiently late approximations, followed by one more degree contraction, proves both the constant coefficient and every coefficient equation. The finite-sum form is the defining formal generating-function equation from hanna2025a383377.

**Theorem 1.7 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall N: \mathbb{N}, \operatorname{coeff}\left(N, B\right) = \sum_{n \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, (X)^{n} \cdot \operatorname{absSeries}\left((\operatorname{invOfUnit}\left(B, 1\right))^{n}\right)\right))) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two series with constant coefficient one, taking unit inverses preserves coefficient agreement below any degree. Powers and absolute values preserve it as well. Every nonconstant summand then gains a factor X. Induction gives agreement at every degree, proving equality.

**Theorem 1.8 (The entire series modulo two).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{generatingSeries}\right) = 1 + X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer absolute value disappears modulo two. Write F for the mapped series and U for its mapped unit inverse, so UF=1. The coefficient equation makes F agree below d with the sum of (XU)^n for n below d. Multiplication by 1-XU and finite geometric cancellation yield F(1-XU)=1 at every degree. Since FXU=X, this gives F=1+X.

**Theorem 1.9 (The A383377 parity conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{Even}\left(\operatorname{a}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a383377-absolute-reciprocal-geometric-parity` (proved) by `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a383377-absolute-reciprocal-geometric-parity","declaration_gid":"D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A383377, g.f. satisfying A(x) = Sum_{n>=0} x^n * abs(1/A(x)^n)*. URL: <https://oeis.org/A383377>.

*Commentary.*

Taking coefficient n in the modulo-two identity gives zero whenever n is greater than one. The integer cast criterion for ZMod(2) converts this vanishing to Even(a(n)).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.absSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.agree_inv`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.agree_mul`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.mod_two_identity`
