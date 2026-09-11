# Self-Referential Inverse Series Parity

## Abstract

The positive-index coefficients of OEIS A393170 are odd exactly at powers of two.

Paul D. Hanna's OEIS A393170 entry defines an integer series A by requiring coefficient n of the reciprocal of A-nX to vanish at every positive n, fixes a(0)=1, and states the parity conjecture.

PowerSeries(R) is the formal power-series ring over R, X is its indeterminate, coeff(n,F) is the degree-n coefficient, and constantCoeff(F) is the constant coefficient. The expression invOfUnit(F,1) is Mathlib's inverse for a series whose constant coefficient is one. The operation map(intCast,ZMod(2)) reduces integer coefficients modulo two. All indices and exponents are natural numbers.

**Theorem 1.1 (Existence of a normalized source series).**

$$\exists A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(A - \operatorname{C}\left(\operatorname{castZ}\left(n\right)\right) \cdot X, 1\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.exists_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a(0)=1. At each positive n, form the prefix containing the already chosen coefficients below n and choose a(n) to be coefficient n of the inverse of that prefix minus nX. The inverse recurrence depends only on coefficients through degree n, and adding a(n)X^n changes its degree-n coefficient by minus a(n). Strong recursion therefore builds an integer series satisfying all the required equations.

**Theorem 1.2 (Parity separation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(A - \operatorname{C}\left(\operatorname{castZ}\left(n\right)\right) \cdot X, 1\right)\right) = 0))) \implies (\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right)^{2} + \operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put F=map(intCast,A), B=1/F, and C=1/(F+X). The even-index source conditions make the positive even coefficients of B vanish, while the odd-index conditions make the odd coefficients of C vanish. Thus B=1+X*U(X^2) and C=V(X^2). From C*(1+X*B)=B, comparison of odd coefficients gives V=U and hence B=1+X*C. Multiplication by F*(F+X), followed by characteristic-two cancellation, gives F^2+F=X.

**Theorem 1.3 (The normalized quadratic root is unique).**

$$\forall F: \operatorname{PowerSeries}\left(\operatorname{ZMod}\left(2\right)\right), (\operatorname{constantCoeff}\left(F\right) = 1) \implies ((F^{2} + F = X) \implies (F = \operatorname{artinSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If F and the constant-one Artin series S satisfy the same quadratic equation, then (1+F+S)*(F-S)=0. The first factor has unit constant coefficient, so cancellation gives F=S.

**Theorem 1.4 (Identification with the Artin series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(A - \operatorname{C}\left(\operatorname{castZ}\left(n\right)\right) \cdot X, 1\right)\right) = 0))) \implies (\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = \operatorname{artinSeries})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parity-separation equation and uniqueness identify the reduction of every normalized source solution with the Artin series.

**Theorem 1.5 (Support of the constant-one root).**

$$\forall F: \operatorname{PowerSeries}\left(\operatorname{ZMod}\left(2\right)\right), (\operatorname{constantCoeff}\left(F\right) = 1) \implies ((F^{2} + F = X) \implies (\forall n: \mathbb{N}, (\operatorname{coeff}\left(n, F\right) = 1 \iff (n = 0 \lor \exists k: \mathbb{N}, n = 2^{k}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.unit_constant_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniqueness theorem identifies any constant-one root with the Artin series. Its coefficient at zero and at each power of two is one, and every other coefficient is zero.

**Theorem 1.6 (The A393170 parity conjecture).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(A - \operatorname{C}\left(\operatorname{castZ}\left(n\right)\right) \cdot X, 1\right)\right) = 0))) \implies (\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{Odd}\left(\operatorname{coeff}\left(n, A\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SelfReferentialInverseSeriesParity.a393170_conjecture` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A393170, self-referential inverse series*. URL: <https://oeis.org/A393170>.

*Commentary.*

At a positive index, reduction modulo two sends the integer coefficient to one exactly when it is odd. The reduction identity and the support of the constant-one root therefore leave precisely the powers of two.

## References

- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.a393170_conjecture`
- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.exists_solution`
- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.generating_equation`
- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.generating_unique`
- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.mod_two_identity`
- Truth anchor: `D5/S3/Arith/SelfReferentialInverseSeriesParity.unit_constant_support`
- Dependency: [D5/S3/Arith/ArtinSchreierTracePowersOfTwo](ArtinSchreierTracePowersOfTwo.md)
