# Hanna's Compositional-Iterate Congruence

## Abstract

Every positive-index coefficient of OEIS A396807 is congruent to one modulo ten.

Paul D. Hanna's OEIS entry of June 16, 2026 uses superscripts for compositional iteration, not ordinary powers. The sequence below is constructed over the integers. Its generating series has zero constant term and satisfies exactly the defining equation; the uniqueness theorem identifies it without assuming that a fixed point exists.

Ring parameters are displayed explicitly, including those implicit in Lean. PowerSeries(R) is the formal power-series ring, X its indeterminate, and subst(f,g) denotes f composed with g. The operator mk constructs a series from its coefficient function; mk(1) uses the constant function one. Rescaling multiplies coefficient n by the nth power of its parameter. The final remainder is integer remainder, and all indices are natural numbers.

**Definition 1.1 (Compositional iteration).**

$$\begin{aligned}\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall series: \operatorname{PowerSeries}\left(R\right), \forall count: \mathbb{N}, \\\operatorname{iterate}\left(R, series, 0\right) = X\\\operatorname{iterate}\left(R, series, count + 1\right) = \operatorname{subst}\left(\operatorname{iterate}\left(R, series, count\right), series\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.iterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zeroth iterate is the identity series X. Each successor substitutes the original series into the previous iterate. On zero-constant series this is the usual compositional iteration.

**Definition 1.2 (The defining transformation).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall series: \operatorname{PowerSeries}\left(R\right), \operatorname{step}\left(R, series\right) = X + \operatorname{iterate}\left(R, series, 5\right) \cdot \operatorname{iterate}\left(R, series, 6\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fifth and sixth compositional iterates are multiplied as power series. Adding X gives the transformation whose fixed point defines the sequence.

**Theorem 1.3 (Uniqueness by degree).**

$$\begin{aligned}\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall left: \operatorname{PowerSeries}\left(R\right), \forall right: \operatorname{PowerSeries}\left(R\right), \\(\operatorname{constantCoeff}\left(left\right) = 0) \implies (\operatorname{constantCoeff}\left(right\right) = 0) \implies (left = \operatorname{step}\left(R, left\right)) \implies (right = \operatorname{step}\left(R, right\right)) \implies left = right\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.fixed_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement below degree d is preserved by powers and by substitution of zero-constant series. The difference of the two products is split into two terms, each gaining an additional factor X. Thus step improves agreement to degree d+1. Induction and coefficient extensionality prove uniqueness over every commutative ring, including rings with zero divisors.

**Definition 1.4 (Successive approximations).**

$$\begin{aligned}\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall depth: \mathbb{N}, \\\operatorname{approximation}\left(R, 0\right) = 0\\\operatorname{approximation}\left(R, depth + 1\right) = \operatorname{step}\left(R, \operatorname{approximation}\left(R, depth\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.approximation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start from zero and apply step repeatedly. The degree-contraction argument proves that approximation d and every later approximation agree below d.

**Definition 1.5 (The integer coefficient sequence).**

$$\forall index: \mathbb{N}, \operatorname{a}\left(index\right) = \operatorname{coeff}\left(index, \operatorname{approximation}\left(\mathbb{Z}, index + 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficient n is read from approximation n+1, where it has stabilized. This construction does not choose an assumed fixed point.

**Definition 1.6 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.7 (Existence with the OEIS equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (\operatorname{generatingSeries} = X + \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 5\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 6\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized coefficients agree to every finite degree with sufficiently late approximations. Applying degree contraction once more gives the generating equation. Together with fixed_unique, this characterizes a as the unique integer coefficient sequence with zero constant term and the stated compositional equation.

**Definition 1.8 (The geometric family).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall parameter: R, \operatorname{mobius}\left(R, parameter\right) = X \cdot \operatorname{rescale}\left(parameter, \operatorname{mk}\left(1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This series is X times the geometric series with parameter c, equivalently X/(1-cX). The denominator has constant term one and is a unit over every commutative ring; no field division is assumed.

**Theorem 1.9 (Iterating the geometric family).**

$$\begin{aligned}\forall R: Type, [\operatorname{CommRing}\left(R\right)], \forall parameter: R, \forall count: \mathbb{N}, \\\operatorname{iterate}\left(R, \operatorname{mobius}\left(R, parameter\right), count\right) = \operatorname{mobius}\left(R, \operatorname{cast}\left(count, R\right) \cdot parameter\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rescaling Mathlib's geometric-series identity gives the denominator identity. Apply substitution to it and multiply by the inner denominator to prove that composition adds parameters. Induction gives the displayed formula for every parameter and every iteration count.

**Theorem 1.10 (A fixed point modulo ten).**

$$\operatorname{mobius}\left(\operatorname{ZMod}\left(10\right), 1\right) = X + \operatorname{iterate}\left(\operatorname{ZMod}\left(10\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(10\right), 1\right), 5\right) \cdot \operatorname{iterate}\left(\operatorname{ZMod}\left(10\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(10\right), 1\right), 6\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mod_ten_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In ZMod(10), the product (1-5X)(1-6X) equals 1-X: the quadratic coefficient 30 vanishes and 11 equals 1. The geometric-family iteration formula and cancellation of the unit denominator prove the fixed-point identity for the entire unbounded series.

**Theorem 1.11 (The A396807 conjecture).**

$$\forall index: \mathbb{N}, (1 \le index) \implies \operatorname{a}\left(index\right) \bmod 10 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.coefficient_congruence` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396807-compositional-iterate-congruence` (proved) by `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.coefficient_congruence`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396807-compositional-iterate-congruence","declaration_gid":"D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.coefficient_congruence","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396807, G.f. satisfies A(x) = x + A^5(x)*A^6(x)*. URL: <https://oeis.org/A396807>.

*Commentary.*

Map the constructed integer generating equation to ZMod(10). Substitution commutes with this map. Uniqueness identifies the mapped series with mobius(1), whose positive-degree coefficients are all one. Mathlib's integer-cast congruence equivalence gives the integer remainder statement. The conjecture is from the cited entry; its proof is derived here.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.approximation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.coefficient_congruence`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.fixed_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.iterate`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mobius_iterate`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.mod_ten_fixed`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.step`
