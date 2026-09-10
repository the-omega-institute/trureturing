# Hanna's Odd-Square Continued Fraction

## Abstract

The coefficients of the odd-square continued fraction in OEIS A338636 are divisible by eight above degree one.

The equation and mod-eight conjecture are recorded in hanna2020a338636. All indices are natural numbers. PowerSeries(R) denotes formal series over a commutative ring R, X is the formal variable, C embeds a scalar, and coeff(n,A) is the degree-n coefficient. The ring argument of finiteTail is displayed explicitly. The function cast(R,m) is the natural number m viewed in R. The expression invOfUnit(A,1) is the formal inverse with constant coefficient one; the denominator identities below justify its use as division. Types may lie in any universe.

**Definition 1.1 (Finite tails with a specified terminal denominator).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall A: \operatorname{PowerSeries}\left(R\right), \forall j: \mathbb{N}, (\operatorname{finiteTail}\left(R, A, j, 0\right) = A) \land (\forall d: \mathbb{N}, \operatorname{finiteTail}\left(R, A, j, d + 1\right) = A - \operatorname{C}\left(\operatorname{cast}\left(R, 2 \cdot j + 1\right)^{2}\right) \cdot X \cdot \operatorname{invOfUnit}\left(\operatorname{finiteTail}\left(R, A, j + 1, d\right), 1\right)))$$

*Formalization.* `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.finiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are d levels beginning at numerator (2j+1)^2*X. The terminal denominator is A at index j+d. The outermost numerator in the defining equation is X, and its denominator begins at j=1.

**Theorem 1.2 (Increasing depth preserves the old coefficients).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall A: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(A\right) = 1) \implies (\forall j: \mathbb{N}, \forall d: \mathbb{N}, \forall e: \mathbb{N}, \forall n: \mathbb{N}, (d \le e) \implies ((n \le d) \implies (\operatorname{coeff}\left(n, \operatorname{finiteTail}\left(R, A, j, d\right)\right) = \operatorname{coeff}\left(n, \operatorname{finiteTail}\left(R, A, j, e\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.stabilization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the old depth compares the two terminal chains. Inversion of series with constant coefficient one preserves agreement, and each multiplication by X gains one degree. The initial comparison is their common constant coefficient. Thus a coefficient of index n is independent of all depths at least n.

**Definition 1.3 (The stabilized integer coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n\right)\right)\\\operatorname{P}\left(0\right) = 1\\\forall m: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{coeff}\left(k, \operatorname{P}\left(m + 1\right)\right) = \operatorname{coeff}\left(k, (1 + X \cdot \operatorname{invOfUnit}\left(\operatorname{finiteTail}\left(\mathbb{Z}, \operatorname{P}\left(m\right), 1, k\right), 1\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary integer series P(m) is the private approximation at stage m. It begins at one. The displayed coefficient rule gives the next series, using tail depth k for its coefficient of index k. The transformation gains one degree of agreement, so P(m) and every later approximation agree through degree m. The diagonal coefficients therefore stabilize.

**Definition 1.4 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PowerSeries.mk assembles the coefficient function a into a formal integer series. Its coefficients agree with each approximation through that approximation's stage.

**Theorem 1.5 (The continued-fraction equation at every finite depth).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land ((\forall j: \mathbb{N}, \forall d: \mathbb{N}, (\operatorname{constantCoeff}\left(\operatorname{finiteTail}\left(\mathbb{Z}, \operatorname{generatingSeries}, j, d\right)\right) = 1) \land (\operatorname{finiteTail}\left(\mathbb{Z}, \operatorname{generatingSeries}, j, d\right) \cdot \operatorname{invOfUnit}\left(\operatorname{finiteTail}\left(\mathbb{Z}, \operatorname{generatingSeries}, j, d\right), 1\right) = 1)) \land (\forall d: \mathbb{N}, \forall n: \mathbb{N}, (n \le d + 1) \implies (\operatorname{coeff}\left(n, 1\right) = \operatorname{coeff}\left(n, (\operatorname{generatingSeries} - X \cdot \operatorname{invOfUnit}\left(\operatorname{finiteTail}\left(\mathbb{Z}, \operatorname{generatingSeries}, 1, d\right), 1\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite tail has constant coefficient one and its displayed inverse multiplies it to one. Stabilization identifies the coefficientwise construction with the depth-d fraction through degree d+1. This is the finite-depth interpretation of the continued fraction in hanna2020a338636.

**Theorem 1.6 (Uniqueness of the normalized integer solution).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 1) \implies ((\forall d: \mathbb{N}, \forall n: \mathbb{N}, (n \le d + 1) \implies (\operatorname{coeff}\left(n, 1\right) = \operatorname{coeff}\left(n, (A - X \cdot \operatorname{invOfUnit}\left(\operatorname{finiteTail}\left(\mathbb{Z}, A, 1, d\right), 1\right))\right))) \implies (A = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-depth equations make any normalized solution a fixed point of the coefficient transformation defining P. If two input series agree below degree n, their outputs agree below degree n+1. Induction gives agreement at every degree and hence equality of the two series.

**Theorem 1.7 (Divisibility by eight above degree one).**

$$\forall n: \mathbb{N}, (1 < n) \implies (8 \mid \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a338636-continued-fraction-odd-square-mod-eight` (proved) by `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a338636-continued-fraction-odd-square-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2020). *OEIS A338636, continued-fraction g.f. with odd-square numerators*. URL: <https://oeis.org/A338636>.

*Commentary.*

Map the proved finite-depth equations to ZMod(8). Every odd square equals one because two divides j*(j+1). For A=1+X, induction shows that a tail of depth d agrees with one through degree d. Thus 1+X is the reduced fixed point, and contraction uniqueness identifies it with the reduction of generatingSeries. Its coefficients above degree one vanish.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.a`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.finiteTail`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.stabilization`
