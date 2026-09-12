# Reciprocal Square-Exponent Diagonals and Catalan Parity

## Abstract

The coefficients of OEIS A397356 are odd exactly when their index plus one is a power of two.

OEIS A397356 has two conjectures. Only the parity conjecture is proved here; the second conjecture, on divisibility by three, remains open. The defining equation and both conjectures are quoted in hanna2026a397356.

Write R for reciprocalSeries and G for generatingSeries, both power series over the integers, and a(n)=coeff(n,G). The coefficient function r defines R=PowerSeries.mk(r), and G=PowerSeries.invOfUnit(R,1). Write v for one plus the reduction modulo two of D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries. This series over ZMod(2) satisfies v^2=v+X, where X is the indeterminate. Write S for R.map(Int.castRingHom(ZMod(2))). The notation coeff(n,F) extracts the coefficient of X^n in F. All indices and exponents are natural numbers, and subtraction in an exponent is truncated natural subtraction.

**Theorem 1.1 (The binary Catalan diagonal).**

$$\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, (v)^{(n)^{2}}\right) = \operatorname{coeff}\left(n, (v)^{(n)^{2} - 1}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.v_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powers v^(n^2) and v^(n^2-1) have equal coefficients at n for n>1. The residual diagonal vanishes after splitting on the parity of n. A coefficient at an odd degree of a square vanishes in the even case; square extraction in the odd case reduces the residual to a Frobenius diagonal.

**Theorem 1.2 (The defining inverse pair).**

$$(R * G = 1) \land ((\operatorname{a}\left(0\right) = 1) \land ((\operatorname{a}\left(1\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, (R)^{(n)^{2}}\right) = \operatorname{coeff}\left(n, (R)^{(n)^{2} - 1}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

R and G are inverse, and a(0)=a(1)=1. The strict-prefix recurrence for r cancels the difference of the square-exponent diagonals of R for n>1. Since R is the reciprocal of G, this is the entry's defining relation and makes a its coefficient sequence.

**Theorem 1.3 (Uniqueness of the inverse pair).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\operatorname{coeff}\left(1, B\right) = -1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, (B)^{(n)^{2}}\right) = \operatorname{coeff}\left(n, (B)^{(n)^{2} - 1}\right))) \implies ((B * A = 1) \implies ((B = R) \land (A = G)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any integer series B with constant coefficient 1, linear coefficient -1, and the same square-exponent diagonal relation equals R. Strong induction compares coefficients using the diagonal multiplier. If B*A=1 as well, uniqueness of the inverse gives A=G.

**Theorem 1.4 (The reciprocal modulo two).**

$$S = v$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction of R modulo two equals v. The initial coefficients and the diagonal relations agree, so uniqueness over ZMod(2) identifies them.

**Theorem 1.5 (Hanna's A397356 parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.hanna_conjecture_a397356` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397356-reciprocal-square-exponent-diagonal-parity` (proved) by `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.hanna_conjecture_a397356`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397356-reciprocal-square-exponent-diagonal-parity","declaration_gid":"D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.hanna_conjecture_a397356","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397356, reciprocal square-exponent diagonal generating series*. URL: <https://oeis.org/A397356>.

*Commentary.*

The identity S=v identifies the reduction of G with the unit inverse of v. Multiplication of that inverse by X gives the binary Catalan series. Its coefficient description therefore yields Odd(a(n)) exactly when n+1 is a power of two, including n=0.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.hanna_conjecture_a397356`
- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.v_diagonal`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity](../Parity/StripThreeTernaryCatalanParity.md)
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd](DiagonalPowerRatioAllOdd.md)
- Dependency: [D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity](QuadraticPowerDiagonalFibbinaryParity.md)
