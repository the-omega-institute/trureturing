# Hanna's Three-Four Iterate Product Congruence

## Abstract

Every positive-index coefficient of OEIS A396797 is congruent to one modulo six.

The entry cited in hanna2026a396797 defines its generating series by A(x)=x+A^3(x)A^4(x) and conjectures that a(n)=1 modulo 6 for n at least one. Superscripts in this equation denote compositional iterates. The construction below proves existence and uniqueness of a zero-constant integer series satisfying this equation.

PowerSeries(R) is the formal power-series ring over R, and X is its indeterminate. Ring parameters implicit in Lean are displayed explicitly. The operations iterate and mobius are those of CompositionalIterateCongruence: iterate(f,0)=X, and each successor substitutes f into the preceding iterate; mobius(c) is X times the geometric series with coefficients c^n. All indices are natural numbers, mk constructs a series from its coefficients, and the final remainder is integer remainder.

**Definition 1.1 (The integer coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approx}\left(\mathbb{Z}, n + 1\right)\right)\\\operatorname{approx}\left(\mathbb{Z}, 0\right) = 0\\\forall d: \mathbb{N}, \operatorname{approx}\left(\mathbb{Z}, d + 1\right) = X + \operatorname{iterate}\left(\mathbb{Z}, \operatorname{approx}\left(\mathbb{Z}, d\right), 3\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{approx}\left(\mathbb{Z}, d\right), 4\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here approx is local notation for successive applications of the displayed transformation, starting at the zero integer series. Its degree-n coefficient has stabilized by approximation n+1, which defines a(n).

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer generating series is constructed with coefficient function a.

**Theorem 1.3 (Existence with the defining equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (\operatorname{generatingSeries} = X + \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 4\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution preserves agreement below degree d for zero-constant series. For any two compositional iterate counts, the difference of their products splits into two terms, each divisible by X^(d+1). This degree improvement stabilizes the approximations. Their diagonal coefficient sequence has zero constant term and satisfies the entire functional equation.

**Theorem 1.4 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (B = X + \operatorname{iterate}\left(\mathbb{Z}, B, 3\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, B, 4\right)) \implies B = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two zero-constant fixed points, induction on the degree applies the product comparison repeatedly. Every coefficient agrees, so every integer series B satisfying the two displayed hypotheses equals generatingSeries.

**Theorem 1.5 (A geometric fixed point modulo six).**

$$\operatorname{mobius}\left(\operatorname{ZMod}\left(6\right), 1\right) = X + \operatorname{iterate}\left(\operatorname{ZMod}\left(6\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(6\right), 1\right), 3\right) \cdot \operatorname{iterate}\left(\operatorname{ZMod}\left(6\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(6\right), 1\right), 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.mod_six_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric-family iteration formula gives mobius(3) and mobius(4). In ZMod(6), (1-3X)(1-4X)=1-X because 3+4=1 and 3 times 4 is zero. Multiplying by these denominators and cancelling the unit 1-X proves the identity of formal power series.

**Theorem 1.6 (The first A396797 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(n\right) \bmod 6 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396797-three-four-iterate-product-mod-six` (proved) by `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396797-three-four-iterate-product-mod-six","declaration_gid":"D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396797, G.f. satisfies A(x) = x + A^3(x)*A^4(x)*. URL: <https://oeis.org/A396797>.

*Commentary.*

Map the integer generating equation to ZMod(6). Coefficient mapping commutes with substitution, and the degree comparison proves uniqueness over this ring as well. The mapped series therefore equals mobius(1), whose positive-degree coefficients are all one. The integer-cast congruence equivalence gives the displayed remainder. The conjecture is recorded in hanna2026a396797.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.mod_six_fixed`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
