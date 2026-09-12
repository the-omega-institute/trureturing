# Eventual Periods of Scaled Logarithm Columns

## Abstract

Every scaled logarithm column is eventually periodic modulo every positive integer.

Seiichi Manyama's entries A383165 and A383166, dated April 18, 2025, give the square and cube columns. Peter Bala's conjectures, dated February 17, 2026, ask for eventual periodicity modulo every positive integer. The notes bala2026a383165 and bala2026a383166 record the two statements. The theorem below applies to every natural column r.

All indices, columns, moduli, onsets and periods are natural numbers. The sequence a is integer-valued. Power series have rational coefficients: exp is PowerSeries.exp over the rationals, rescale(c,F) replaces X by cX, C embeds a rational constant, and logOf(H) is the formal logarithm of H, namely PowerSeries.log substituted at H-1. The function coeff(n,F) extracts a coefficient, mk forms a series from its coefficient function, factorial is Nat.factorial, and rat denotes a cast to the rationals. Every fraction displayed here is rational division. The function num returns the reduced rational numerator; residue(m,z) denotes the integer cast to ZMod m.

**Definition 1.1 (The e.g.f. coefficient sequence).**

$$\forall r, n: \mathbb{N}, \operatorname{a}\left(r, n\right) = \operatorname{num}\left(\operatorname{rat}\left(\operatorname{factorial}\left(n\right)\right) \cdot \operatorname{coeff}\left(n, \operatorname{C}\left(\frac{1}{\operatorname{rat}\left(\operatorname{factorial}\left(r\right)\right)}\right) \cdot (\operatorname{logOf}\left((1 + \operatorname{C}\left(\frac{1}{2}\right) \cdot (\operatorname{rescale}\left(2, exp\right) - 1))\right))^{r}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition extracts the factorial-scaled coefficient of log(1+(exp(2X)-1)/2)^r/r!. The integral differential bridge proves that this rational number has denominator one, so numerator extraction loses no information.

**Theorem 1.2 (The defining scaled logarithm e.g.f.).**

$$\forall r: \mathbb{N}, \operatorname{mk}\left((n: \mathbb{N} \mapsto \frac{\operatorname{rat}\left(\operatorname{a}\left(r, n\right)\right)}{\operatorname{rat}\left(\operatorname{factorial}\left(n\right)\right)})\right) = \operatorname{C}\left(\frac{1}{\operatorname{rat}\left(\operatorname{factorial}\left(r\right)\right)}\right) \cdot (\operatorname{logOf}\left((1 + \operatorname{C}\left(\frac{1}{2}\right) \cdot (\operatorname{rescale}\left(2, exp\right) - 1))\right))^{r}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put H=(1+exp(2X))/2 and U=H inverse. Then H'=2H-1, U'=U squared minus 2U, and (log H)'=2-U. Differentiating B(r,j)=U^j (log H)^r/r! gives j B(r,j+1)-2j B(r,j), together with 2 B(r-1,j)-B(r-1,j+1) when r is positive. Its initial constant coefficient is one for r=0 and zero otherwise. Induction identifies the resulting integer recurrence with n! times coeff(n,B(r,j)). At j=0 this proves integrality and the displayed generating identity.

**Theorem 1.3 (Eventual periodicity of every column).**

$$\forall r, m: \mathbb{N}, (0 < m) \implies (\exists N, p: \mathbb{N}, ((0 < p) \land (\forall n: \mathbb{N}, (N \le n) \implies (\operatorname{residue}\left(m, \operatorname{a}\left(r, n + p\right)\right) = \operatorname{residue}\left(m, \operatorname{a}\left(r, n\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.coefficient_periodicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo m the differential recurrence depends on j only through its residue. For fixed r, the values indexed by columns at most r and auxiliary indices below m form a finite state. Equal states have equal successors. The pigeonhole principle gives a repeated state, and induction propagates that equality to all later indices. The scaled coefficient bridge transfers the resulting positive period to a. Neither a specific onset nor a minimal period is asserted.

**Theorem 1.4 (Bala's conjecture on A383165).**

$$\forall m: \mathbb{N}, (0 < m) \implies (\exists N, p: \mathbb{N}, ((0 < p) \land (\forall n: \mathbb{N}, (N \le n) \implies (\operatorname{residue}\left(m, \operatorname{a}\left(2, n + p\right)\right) = \operatorname{residue}\left(m, \operatorname{a}\left(2, n\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383165` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a383165-scaled-log-column-periodicity` (proved) by `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383165`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a383165-scaled-log-column-periodicity","declaration_gid":"D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383165","resolution_kind":"proved"} -->

*Citation.* Seiichi Manyama; Peter Bala (2026). *OEIS A383165, Expansion of e.g.f. log(1 + (exp(2*x) - 1)/2)^2 / 2.*. URL: <https://oeis.org/A383165>.

*Commentary.*

Specialize the general theorem to r=2. The proved generating equation identifies this column with the square divided by two in bala2026a383165, proving the conjecture for every positive modulus.

**Theorem 1.5 (Bala's conjecture on A383166).**

$$\forall m: \mathbb{N}, (0 < m) \implies (\exists N, p: \mathbb{N}, ((0 < p) \land (\forall n: \mathbb{N}, (N \le n) \implies (\operatorname{residue}\left(m, \operatorname{a}\left(3, n + p\right)\right) = \operatorname{residue}\left(m, \operatorname{a}\left(3, n\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383166` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a383166-scaled-log-column-periodicity` (proved) by `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383166`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a383166-scaled-log-column-periodicity","declaration_gid":"D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383166","resolution_kind":"proved"} -->

*Citation.* Seiichi Manyama; Peter Bala (2026). *OEIS A383166, Expansion of e.g.f. log(1 + (exp(2*x) - 1)/2)^3 / 6.*. URL: <https://oeis.org/A383166>.

*Commentary.*

Specialize the general theorem to r=3. The proved generating equation identifies this column with the cube divided by six in bala2026a383166, proving the conjecture for every positive modulus.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383165`
- Truth anchor: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.bala_conjecture_a383166`
- Truth anchor: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.coefficient_periodicity`
- Truth anchor: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.generating_equation`
