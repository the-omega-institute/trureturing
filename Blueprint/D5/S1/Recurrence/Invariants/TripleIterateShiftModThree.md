# Hanna's Triple Iterate Shift Congruence

## Abstract

Every positive-index coefficient of OEIS A396102 is congruent to one modulo three.

The entry cited in hanna2026a396102 defines A(x)=x+... by A(A(A(x)))=(1+x)A(A(x)) and conjectures that a(n)=1 modulo three for every n at least one. The construction below proves existence and uniqueness of an integer series with constant coefficient zero and linear coefficient one satisfying this equation.

PowerSeries(R) denotes the formal power-series ring over R, and X is its indeterminate. The ring argument of iterate and mobius, implicit in Lean, is displayed explicitly. These operations come from CompositionalIterateCongruence: iterate(f,0)=X, and each successor substitutes f into the preceding iterate; mobius(c) is X times the geometric series with coefficients c^n. Indices are natural numbers, mk constructs a series from its coefficient function, and the final remainder is integer remainder.

**Definition 1.1 (The integer coefficient sequence).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(\mathbb{Z}, n\right)\right)\\\operatorname{approximation}\left(\mathbb{Z}, 0\right) = X\\\forall d: \mathbb{N}, \operatorname{approximation}\left(\mathbb{Z}, d + 1\right) = (\operatorname{approximation}\left(\mathbb{Z}, d\right) + (1 + X) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{approximation}\left(\mathbb{Z}, d\right), 2\right)) - \operatorname{iterate}\left(\mathbb{Z}, \operatorname{approximation}\left(\mathbb{Z}, d\right), 3\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local notation approximation denotes the integer series defined by the displayed iteration, starting at X. Agreement below degree d, for d at least two, improves to agreement below degree d+1 after one step. Thus the diagonal coefficient defines a(n).

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer series is constructed with coefficient function a.

**Theorem 1.3 (Existence and the functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right) = (1 + X) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n greater than one and two zero-constant series agreeing below degree n with linear coefficient one, the difference at degree n of the j-th compositional iterates is j times the original coefficient difference. The correction step therefore cancels this difference with multiplier 1+2-3=0; the factor X uses only the preceding coefficient. The stabilized coefficients form a fixed point of the correction step, which is exactly the displayed functional equation.

**Theorem 1.4 (Uniqueness of the normalized integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies (\operatorname{iterate}\left(\mathbb{Z}, f, 3\right) = (1 + X) \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 2\right)) \implies f = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two solutions satisfy the correction fixed-point identity. Their constant and linear coefficients agree. Applying degree contraction inductively proves agreement at every degree, hence equality.

**Theorem 1.5 (The geometric solution modulo three).**

$$\operatorname{iterate}\left(\operatorname{ZMod}\left(3\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(3\right), 1\right), 3\right) = (1 + X) \cdot \operatorname{iterate}\left(\operatorname{ZMod}\left(3\right), \operatorname{mobius}\left(\operatorname{ZMod}\left(3\right), 1\right), 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.mod_three_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric-family iteration identity gives mobius(3)=X and mobius(2) for the third and second iterates over ZMod(3). Since -2=1 in that ring, the geometric denominator of mobius(2) is 1+X. Multiplication by this denominator gives X, proving the equation.

**Theorem 1.6 (Hanna's A396102 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(n\right) \bmod 3 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396102-triple-iterate-shift-mod-three` (proved) by `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396102-triple-iterate-shift-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396102, g.f. satisfying A(A(A(x))) = (1+x)*A(A(x))*. URL: <https://oeis.org/A396102>.

*Commentary.*

Map the integer generating equation into ZMod(3). Mapping coefficients commutes with substitution. The degree comparison proves uniqueness over this ring too, so the mapped series equals mobius(1). Its positive-degree coefficients are all one. The integer-cast congruence equivalence gives the claimed remainder, as conjectured in hanna2026a396102.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.mod_three_fixed`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
