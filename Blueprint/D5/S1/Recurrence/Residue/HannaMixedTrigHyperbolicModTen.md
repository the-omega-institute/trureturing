# Hanna's Mixed Trigonometric and Hyperbolic Reciprocal

## Abstract

Every positive-index factorial-normalized coefficient of Hanna's reciprocal is an integer congruent to three modulo ten.

OEIS A227051, revision 10, NAME (no numbered page): E.g.f.: 1/(cos(x) - sin(x)*sinh(x)), omitting the zero-valued coefficients of odd powers of x. All series below lie in PowerSeries over the rationals. Mathlib's PowerSeries.cos and PowerSeries.sin are rational Taylor series. The natural index n selects degree 2*n. The existing eCoeff(f,k) is k! times coeff(k,f), so a(n) retains the source's factorial normalization. The notation val(z) in the formula is the coercion from integers to rationals.

**Definition 1.1 (The hyperbolic sine Taylor series).**

$$\operatorname{sinhSeries} = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (m:\mathbb{N}) \mapsto \operatorname{ite}\left(\operatorname{Even}\left(m\right), 0, (\operatorname{Nat}.\operatorname{factorial}\left(m\right):\mathbb{Q})^{-1}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.sinhSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

The odd Taylor coefficient is the inverse of the factorial; every even coefficient is zero.

**Definition 1.2 (The mixed denominator).**

$$\operatorname{denominator} = \operatorname{PowerSeries}.\operatorname{cos}\left(\mathbb{Q}\right) - \operatorname{PowerSeries}.\operatorname{sin}\left(\mathbb{Q}\right) \cdot \operatorname{sinhSeries}$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.denominator` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

OEIS A227051, revision 10, NAME (no numbered page): E.g.f.: 1/(cos(x) - sin(x)*sinh(x)), omitting the zero-valued coefficients of odd powers of x.

**Definition 1.3 (The reciprocal series).**

$$\operatorname{A} = \operatorname{denominator}^{-1}$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

The formal inverse is taken over the rationals. The denominator has constant coefficient one.

**Definition 1.4 (The even factorial-normalized coefficients).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{IntegralEGFComposition}.\operatorname{eCoeff}\left(\operatorname{A}, 2 \cdot n\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

OEIS A227051, revision 10, PARI program (no numbered page): (PARI) {a(n)=local(X=x+x*O(x^(2*n))); (2*n)!*polcoeff(1/(cos(X) - sin(X)*sinh(X)), 2*n)} Thus n=0 selects the constant coefficient, and no odd-degree coefficient is included.

**Definition 1.5 (Hanna's congruence assertion).**

$$\operatorname{claim} \Leftrightarrow (\forall n: \mathbb{N}, 1 \le n \Rightarrow \exists z:\mathbb{Z}, \operatorname{a}\left(n\right) = \operatorname{val}\left(z\right) \land \operatorname{Int}.\operatorname{ModEq}\left(10, z, 3\right))$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

OEIS A227051, revision 10, first FORMULA (no numbered page), verbatim: a(n) == 3 (mod 10) for n>0 (conjecture). The natural index satisfies 1<=n. An integer z equals a(n) in the rationals and satisfies the integer congruence, so integrality is part of the assertion.

**Theorem 1.6 (The congruence at every positive index).**

$$\forall n: \mathbb{N}, 1 \le n \Rightarrow \exists z:\mathbb{Z}, \operatorname{a}\left(n\right) = \operatorname{val}\left(z\right) \land \operatorname{Int}.\operatorname{ModEq}\left(10, z, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result` (`✓ std3`). ∎

*Resolves.* `Problems/h227051-cossinhmod10` (proved) by `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"h227051-cossinhmod10","declaration_gid":"D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A227051: mixed trigonometric and hyperbolic reciprocal*. URL: <https://oeis.org/A227051>.

*Commentary.*

The denominator coefficients are d(2r)=1 and d(2r+1)=-1-2*(-4)^r. The binomial product equation identifies the rational coefficients with an integer recurrence. Triangular uniqueness identifies its inverse modulo two with 1,1,1,... and its inverse modulo five with 1,3,3,... . Coprimality of two and five gives the stated congruence. The calculation uses finite coefficient identities and does not invert factorials in a residue field.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.A`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.a`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.denominator`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.result`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.sinhSeries`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](ExponentialSquareWeightCatalanParity.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
