# Hanna's Iterate-Product Congruence Modulo Five

## Abstract

Every coefficient above degree one in OEIS A396795 is divisible by five.

Paul D. Hanna's OEIS A396795 entry states the generating equation and conjecture recorded in hanna2026a396795. All series below have integer coefficients except in the two lemmas over an arbitrary commutative ring R. All coefficient and iterate indices are natural numbers. The generating series is normalized by zero constant coefficient and coefficient one at degree one.

PowerSeries(Z) denotes the formal power-series ring with indeterminate X. The iterate operation is defined in D5/S1/Recurrence/Invariants/CompositionalIterateCongruence: iterate(Z,f,0)=X and iterate(Z,f,j+1)=iterate(Z,f,j).subst(f). Thus iterate(Z,f,2)=f(f(X)) when the constant coefficient is zero. Powers and products are ordinary power-series operations. The operator choose selects a witness of the displayed proved existential proposition. C embeds a scalar as a constant series, subst is formal substitution, and natCast(R,k) is the natural-number cast into R. Type ranges over types in any universe; CommRing(R) supplies the commutative ring structure.

**Theorem 1.1 (Scalar annihilation survives substitution).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall r: R, \forall f: \operatorname{PowerSeries}\left(R\right), \forall u: \operatorname{PowerSeries}\left(R\right), \forall v: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(u\right) = 0) \implies ((\operatorname{constantCoeff}\left(v\right) = 0) \implies ((\operatorname{C}\left(r\right) \cdot (u - v) = 0) \implies (\operatorname{C}\left(r\right) \cdot (\operatorname{subst}\left(f, u\right) - \operatorname{subst}\left(f, v\right)) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.subst_annihilate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor u to the power k minus v to the power k by u-v. The scalar r annihilates each such difference, hence every coefficient in the difference of substitutions. The zero constant coefficients justify computing substitution coefficients by finite sums.

**Theorem 1.2 (Iteration with a square-zero scalar).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall r: R, (r \cdot r = 0) \implies (\forall b: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(X + \operatorname{C}\left(r\right) \cdot b\right) = 0) \implies (\forall j: \mathbb{N}, \operatorname{iterate}\left(R, X + \operatorname{C}\left(r\right) \cdot b, j\right) = X + \operatorname{C}\left(\operatorname{natCast}\left(R, j\right) \cdot r\right) \cdot b)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.nilpotent_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any commutative ring and any scalar r with r*r=0, scalar annihilation makes each substitution add the same term C(r)*b. Induction gives the formula for every natural iterate index.

**Theorem 1.3 (Square-zero lifting for two iterate indices).**

$$\forall m: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\forall n: \mathbb{N}, \operatorname{natCast}\left(\mathbb{Z}, m\right) \mid \operatorname{coeff}\left(n, f - X\right)) \implies (\forall i: \mathbb{N}, \forall j: \mathbb{N}, (m \mid (i + j)) \implies (\forall n: \mathbb{N}, \operatorname{natCast}\left(\mathbb{Z}, m\right)^{2} \mid \operatorname{coeff}\left(n, \operatorname{iterate}\left(\mathbb{Z}, f, i\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, f, j\right) - X^{2}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.iterate_product_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write f=X+C(m)*b by exact coefficientwise division and map to ZMod(m^2). There m*m=0, so the two iterates are X+C(i*m)*b and X+C(j*m)*b. Their quadratic correction vanishes because it carries m*m. Their linear correction vanishes because m divides i+j. Mapping back proves integer coefficient divisibility, including modulus zero.

**Definition 1.4 (The normalized generating series).**

$$\operatorname{generatingSeries} = \operatorname{choose}\left(\exists f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{iterate}\left(\mathbb{Z}, f, 2\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 3\right) = X^{2} + \operatorname{C}\left(25\right) \cdot X^{3}) \land ((\operatorname{constantCoeff}\left(f\right) = 0) \land (\operatorname{coeff}\left(1, f\right) = 1)))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existence follows from successive coefficient corrections starting at X. At degree n greater than one, the error at degree n+1 is divided by five using integer division. The lifting lemma makes this exact and makes the correction divisible by five. The stabilized coefficients give an integer series satisfying all three existential clauses.

**Definition 1.5 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer a(n) is the degree-n coefficient of generatingSeries. Its constant coefficient is zero and its degree-one coefficient is one.

**Theorem 1.6 (The OEIS equation and normalization).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 2\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right) = X^{2} + \operatorname{C}\left(25\right) \cdot X^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed series satisfies the product equation as a formal power-series identity, together with both normalization conditions. Witness selection preserves these three proved properties.

**Theorem 1.7 (Uniqueness of the normalized integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{iterate}\left(\mathbb{Z}, f, 2\right) \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 3\right) = X^{2} + \operatorname{C}\left(25\right) \cdot X^{3}) \implies ((\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{coeff}\left(1, f\right) = 1) \implies (f = \operatorname{generatingSeries})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two normalized series agree below degree n greater than one, their second and third iterates differ at degree n by twice and three times their coefficient difference. Their products differ at degree n+1 by five times that difference. Equal products force equal coefficients over the integers, and strong induction proves equality of the series.

**Theorem 1.8 (The A396795 divisibility conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (5 \mid \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396795-iterate-product-twenty-five-mod-five` (proved) by `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396795-iterate-product-twenty-five-mod-five","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396795, g.f. satisfying A^2(x) A^3(x) = x^2 + 25 x^3*. URL: <https://oeis.org/A396795>.

*Commentary.*

Induct on n and truncate the solution below degree n. The earlier coefficients make this prefix congruent to X modulo five. The lifting lemma makes its product error divisible by twenty-five. Comparing the prefix with the solution using the coefficient perturbation gives twenty-five dividing 5a(n), hence five dividing a(n), for every n greater than one.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.a`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.iterate_product_lift`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.nilpotent_iterate`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive.subst_annihilate`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../Invariants/CompositionalIterateCongruence.md)
