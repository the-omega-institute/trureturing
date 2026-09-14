# Quadratic Power Diagonals and Fibbinary Parity

## Abstract

The positive-index coefficients of OEIS A397244 are odd exactly at twice a Fibbinary number plus one.

The NAME and conjecture are quoted in hanna2026a397244. Write A for generatingSeries, the integer series with coefficient function a. The strict-prefix recurrence starts with a(0)=a(1)=1 and uses only coefficients below n to define a(n). The formalization uses the NAME and that recurrence; the source note records the formula erratum.

Write S for A.map(Int.castRingHom(ZMod(2))) and T for D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries.map(Int.castRingHom(ZMod(2))). Thus S and T are series over ZMod(2), while A and the universally quantified B are series over the integers. All indices have type natural number. The notation intCast(n) is the cast (n : integers), coeff(n,F) extracts the coefficient at n, and expand(2,T) substitutes X^2 for X; its proof that 2 is nonzero is implicit. X is the indeterminate. Fibbinary is the imported predicate D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity.Fibbinary: f bitwise-and (f shifted right by one) equals zero.

**Theorem 1.1 (The second coefficient).**

$$\operatorname{a}\left(2\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.a_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix is 1+X. The recurrence gives 3*choose(5,2)-4*choose(4,2)=6.

**Theorem 1.2 (The exact diagonal equations).**

$$(\operatorname{coeff}\left(0, A\right) = 1) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies ((2 * \operatorname{intCast}\left(n\right)) * \operatorname{coeff}\left(n, (A)^{2 * n}\right) = (2 * \operatorname{intCast}\left(n\right) - 1) * \operatorname{coeff}\left(n, (A)^{2 * n + 1}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen diagonal multiplier compares each power with its strict prefix. The recurrence cancels the resulting coefficient difference and gives the displayed relation for every n greater than one.

**Theorem 1.3 (Uniqueness over the integers).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies ((2 * \operatorname{intCast}\left(n\right)) * \operatorname{coeff}\left(n, (B)^{2 * n}\right) = (2 * \operatorname{intCast}\left(n\right) - 1) * \operatorname{coeff}\left(n, (B)^{2 * n + 1}\right))) \implies (B = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The private equation_unique proves uniqueness over any commutative ring by strong induction and the frozen diagonal multiplier. Specializing to the integers gives B=A with both initial coefficients and all diagonal equations present as hypotheses.

**Theorem 1.4 (The cubic equation modulo two).**

$$(S)^{3} = (S)^{2} + X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.mod_two_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The private even_power_diagonal proves coeff(n,F^(2*n))=0 for every series over ZMod(2) and every positive n by Frobenius descent. The private cubic_diagonal uses it to turn the frozen candidate's cubic equation into A397244's diagonal relations. The general equation_unique then identifies S with the candidate.

**Theorem 1.5 (The ternary-series reduction).**

$$S = 1 + X * \operatorname{expand}\left(2, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved equality of reductions transports the frozen candidate's identity S=1+X*expand(2,T). This is equality modulo two, not equality of the two integer sequences.

**Theorem 1.6 (Hanna's A397244 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists f: \mathbb{N}, (\operatorname{Fibbinary}\left(f\right)) \land (n = 2 * f + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.hanna_conjecture_a397244` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397244-quadratic-power-diagonal-fibbinary-parity` (proved) by `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.hanna_conjecture_a397244`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397244-quadratic-power-diagonal-fibbinary-parity","declaration_gid":"D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.hanna_conjecture_a397244","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397244, quadratic power-diagonal generating series*. URL: <https://oeis.org/A397244>.

*Commentary.*

Coefficient equality of the reductions transports Odd(a(n)) to the frozen AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture. The new Frobenius diagonal lemma remains on the live path through reduction_eq_candidate; the integer sequences are not identified.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.a_two`
- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.hanna_conjecture_a397244`
- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.mod_two_cubic`
- Truth anchor: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.mod_two_identity`
- Dependency: [D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity](../Parity/FibbinarySquareSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity](../Parity/StripThreeTernaryCatalanParity.md)
- Dependency: [D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity](AbsoluteReciprocalSquareFibbinaryParity.md)
- Dependency: [D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd](DiagonalPowerRatioAllOdd.md)
