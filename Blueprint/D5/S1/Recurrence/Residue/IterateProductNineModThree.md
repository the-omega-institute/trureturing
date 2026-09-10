# Hanna's Iterate-Product Congruence Modulo Three

## Abstract

Every coefficient above degree one in OEIS A396793 is divisible by three.

Paul D. Hanna's OEIS A396793 entry states the generating equation and conjecture recorded in hanna2026a396793. All series below have integer coefficients, and all coefficient indices are natural numbers. The normalization is zero constant coefficient and coefficient one at degree one.

PowerSeries(Z) denotes the formal power-series ring with indeterminate X. The iterate operation is defined in D5/S1/Recurrence/Invariants/CompositionalIterateCongruence: iterate(Z,f,0)=X and iterate(Z,f,j+1)=iterate(Z,f,j).subst(f). Thus iterate(Z,f,2)=f(f(X)) when the constant coefficient is zero. Powers and products are ordinary power-series operations. The operator choose selects a witness of the displayed proved existential proposition.

**Theorem 1.1 (The lift from modulo three to modulo nine).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\forall n: \mathbb{N}, 3 \mid \operatorname{coeff}\left(n, f - X\right)) \implies (\forall n: \mathbb{N}, 9 \mid \operatorname{coeff}\left(n, f \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 2\right) - X^{2}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductNineModThree.lift_mod_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write f=X+3B using coefficientwise exact integer division. Over ZMod(9), the scalar 3 has square zero. The factorization of u^k-v^k shows that 3(B(X+3B)-B(X))=0, so the second iterate is X+6B. Multiplying X+3B by X+6B gives X squared modulo nine. Mapping coefficients back to integers gives the displayed divisibility at every degree.

**Definition 1.2 (The normalized generating series).**

$$\operatorname{generatingSeries} = \operatorname{choose}\left(\exists f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((f \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 2\right) = X^{2} + 9 \cdot X^{3}) \land ((\operatorname{constantCoeff}\left(f\right) = 0) \land (\operatorname{coeff}\left(1, f\right) = 1)))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/IterateProductNineModThree.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existence follows from successive coefficient corrections starting at X. At degree n greater than one, the error at degree n+1 is divided by three using integer division. The lifting lemma makes this exact and makes the correction divisible by three. The stabilized coefficients give an integer series satisfying all three existential clauses.

**Definition 1.3 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/IterateProductNineModThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the degree-n coefficient of generatingSeries. Its constant coefficient is zero and its degree-one coefficient is one.

**Theorem 1.4 (The OEIS equation and normalization).**

$$(\operatorname{generatingSeries} \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 2\right) = X^{2} + 9 \cdot X^{3}) \land ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductNineModThree.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed series satisfies the product equation as a formal power-series identity, together with both normalization conditions. Witness selection preserves these three proved properties.

**Theorem 1.5 (Uniqueness of the normalized integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (f \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 2\right) = X^{2} + 9 \cdot X^{3}) \implies ((\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies (f = \operatorname{generatingSeries})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductNineModThree.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two normalized series agree below degree n greater than one, their second iterates differ at degree n by twice their coefficient difference. Their products differ at degree n+1 by three times that difference. Equal products force equal coefficients over the integers, and strong induction proves equality of the series.

**Theorem 1.6 (The A396793 divisibility conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (3 \mid \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductNineModThree.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396793-iterate-product-nine-mod-three` (proved) by `D5/S1/Recurrence/Residue/IterateProductNineModThree.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396793-iterate-product-nine-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductNineModThree.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396793, g.f. satisfying A(x) A(A(x)) = x^2 + 9 x^3*. URL: <https://oeis.org/A396793>.

*Commentary.*

Induct on n and truncate the solution below degree n. The earlier coefficients make this prefix congruent to X modulo three. The lifting lemma makes its product error divisible by nine. Comparing the prefix with the solution using the coefficient perturbation gives nine dividing 3a(n), hence three dividing a(n), for every n greater than one.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.a`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductNineModThree.lift_mod_nine`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../Invariants/CompositionalIterateCongruence.md)
