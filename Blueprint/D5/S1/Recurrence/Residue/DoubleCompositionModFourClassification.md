# Hanna's Double-Composition Modulo-Four Classification

## Abstract

The normalized series of OEIS A372577 has a complete modulo-four classification.

The entry cited in hanna2024a372577 defines A(x) by A(x)^2=A(A(x*A(x)+x*A(x)^2)), with constant coefficient zero and linear coefficient one. It conjectures remainder three at indices 6m-3 and remainder one at indices 6m-k for k in {0,1,2,4,5}, where m is positive. These indices cover all positive integers.

PowerSeries(Z) denotes formal power series over the integers, X is the indeterminate, coeff extracts a coefficient, and mk constructs a series from its coefficient function. The notation subst(f,u) means f(u), with the outer series first. All indices are natural numbers. The remainder of n is natural remainder, and the remainder of a(n) is integer remainder. The displayed approximation, argument, nested, and step operations are local notation for the private construction.

**Definition 1.1 (Construction by stabilized coefficients).**

$$\begin{aligned}\operatorname{generatingSeries} = (X) \cdot (\operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n, \operatorname{approximation}\left(n\right)\right))\right))\\\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = \operatorname{step}\left(\operatorname{approximation}\left(d\right)\right)\\\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{step}\left(f\right) = ((1 + (X) \cdot (f)) \cdot (\operatorname{subst}\left(f, \operatorname{argument}\left(f\right)\right))) \cdot (\operatorname{subst}\left(f, \operatorname{nested}\left(f\right)\right))\\\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{argument}\left(f\right) = (((X)^{2}) \cdot (f)) \cdot (1 + (X) \cdot (f))\\\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{nested}\left(f\right) = (\operatorname{argument}\left(f\right)) \cdot (\operatorname{subst}\left(f, \operatorname{argument}\left(f\right)\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing A=X*U and cancelling X^2*U gives U=step(U). Each substitution argument is divisible by X^2. If two unit series agree below degree d, where d is positive, their transformed series agree below degree d+1. The approximations start at one, keep constant coefficient one, and stabilize through degree d by approximation d. Their diagonal coefficients define U and hence generatingSeries.

**Definition 1.2 (The integer coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient sequence is extracted from the constructed generating series.

**Theorem 1.3 (The double composition and normalization).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land ((\operatorname{generatingSeries})^{2} = \operatorname{subst}\left(\operatorname{generatingSeries}, \operatorname{subst}\left(\operatorname{generatingSeries}, (X) \cdot (\operatorname{generatingSeries}) + (X) \cdot ((\operatorname{generatingSeries})^{2})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient stabilization proves that U is fixed by step. Multiplying this fixed-point identity by X^2*U restores the two nested substitutions in the defining equation. The constant and linear coefficients follow from the factor X and the constant coefficient one of U.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies (((f)^{2} = \operatorname{subst}\left(f, \operatorname{subst}\left(f, (X) \cdot (f) + (X) \cdot ((f)^{2})\right)\right)) \implies (f = \operatorname{generatingSeries})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor any competing solution as X*U. The linear normalization makes U a unit, so cancelling X^2 and U in the equation gives the same fixed-point identity. Degree contraction proves equality of all coefficients.

**Theorem 1.5 (Every positive coefficient modulo four).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(n\right) \bmod 4 = (\operatorname{if} (n \bmod 6 = 3) \operatorname{then} 3 \operatorname{else} 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a372577-double-composition-mod-four` (proved) by `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a372577-double-composition-mod-four","declaration_gid":"D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A372577, expansion of g.f. A(x) satisfying A(x)^2 = A(A(x*A(x) + x*A(x)^2))*. URL: <https://oeis.org/A372577>.

*Commentary.*

Over ZMod(4), put P=X+X^2+3X^3+X^4+X^5+X^6 and D=1-X^6. The rational series P/D satisfies the full double-composition equation: homogenizing P and D clears each substitution denominator, and two polynomial identities establish the result by unit cancellation. Uniqueness identifies it with the reduction of generatingSeries. The identity P/D=X/(1-X)+2X^3/(1-X^6), with formal unit inverses, then gives remainder three precisely at n mod 6 equal to three, and remainder one otherwise. This is both conjectured clauses together.

**Theorem 1.6 (Oddness as a corollary).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.odd_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete classification gives only the residues one and three modulo four. Both imply integer remainder one modulo two, so every positive-index coefficient is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.a`
- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.odd_coefficients`
