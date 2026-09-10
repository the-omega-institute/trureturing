# Hanna's Fibbinary Parity Conjecture

## Abstract

The odd coefficients of OEIS A374571 occur exactly at Fibbinary indices.

The entry cited in hanna2024a374571 specifies A(x)=A(x^2)-x A(x^2)^2 and conjectures that, for n>0, a(n) is odd exactly when n is a Fibbinary number, as listed by A003714. The normalization is A(0)=1. The functional equation alone leaves the constant coefficient free, so uniqueness retains that hypothesis.

Indices and exponents are natural numbers. The functions div and mod denote natural integer division and remainder; subtraction inside an index is natural subtraction. Fin(r) consists of j with 0<=j<r, read as natural numbers in the summand. Values of a are integers. PowerSeries(Z) is the formal power-series ring with indeterminate X; subst(B,Q) means composition of B with Q, and mk(a) has coefficients a. The operations land and shiftRight are natural-number bitwise intersection and right shift, respectively.

**Definition 1.1 (The integer coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{a}\left(n + 1\right) = \operatorname{if} (\operatorname{mod}\left(n + 1, 2\right) = 0) \operatorname{then} \operatorname{a}\left(\operatorname{div}\left(n + 1, 2\right)\right) \operatorname{else} -(\sum_{j: \operatorname{Fin}\left(\operatorname{div}\left(n, 2\right) + 1\right)} (\operatorname{a}\left(j\right) \cdot \operatorname{a}\left(\operatorname{div}\left(n, 2\right) - j\right)))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seed and the displayed recurrence define a by well-founded recursion. Every recursive index in the successor clause is strictly smaller than n+1.

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries}: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of degree n is a(n).

**Definition 1.3 (No adjacent one bits).**

$$\forall n: \mathbb{N}, \operatorname{Fibbinary}\left(n\right) \iff (\operatorname{land}\left(n, \operatorname{shiftRight}\left(n, 1\right)\right) = 0)$$

*Formalization.* `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.Fibbinary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bit i of land(n,shiftRight(n,1)) is the conjunction of bits i and i+1 of n. Thus the intersection vanishes exactly when the binary representation contains no adjacent ones, including the case n=0.

**Theorem 1.4 (The normalized functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries} = \operatorname{subst}\left(\operatorname{generatingSeries}, X^{2}\right) - X \cdot (\operatorname{subst}\left(\operatorname{generatingSeries}, X^{2}\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution by X^2 retains coefficient n/2 at even degrees and is zero at odd degrees. The shifted square contributes the negative convolution at odd degrees. Coefficient comparison gives the defining recurrence and proves the identity together with the constant coefficient.

**Theorem 1.5 (Uniqueness with constant coefficient one).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((B = \operatorname{subst}\left(B, X^{2}\right) - X \cdot (\operatorname{subst}\left(B, X^{2}\right))^{2}) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive degree, the equation expresses the coefficient using only smaller indices. Strong induction, with the prescribed constant coefficient as base case, identifies B with generatingSeries.

**Theorem 1.6 (The A374571 parity conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff \operatorname{Fibbinary}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a374571-fibbinary-square-substitution-parity` (proved) by `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a374571-fibbinary-square-substitution-parity","declaration_gid":"D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A374571, g.f. satisfying A(x) = A(x^2) - x*A(x^2)^2*. URL: <https://oeis.org/A374571>.

*Commentary.*

Reduce the proved generating equation to ZMod(2). Frobenius identifies the square of a series with its substitution by X^2. Consequently the coefficient residues satisfy a(2m)=a(m), a(4m+1)=a(m), and a(4m+3)=0. The Fibbinary predicate satisfies the same three descent rules: an ending zero may be removed, an ending 01 may be removed, and an ending 11 is forbidden. Strong induction from a(0)=1 proves the equivalence; the displayed theorem restricts it to the positive indices in the entry.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.Fibbinary`
- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.hanna_conjecture`
