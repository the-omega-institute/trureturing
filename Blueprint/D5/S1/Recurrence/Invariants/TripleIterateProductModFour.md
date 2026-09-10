# Hanna's Triple-Iterate Product Congruence

## Abstract

Every coefficient above degree one in OEIS A396794 is divisible by four.

Paul D. Hanna's OEIS A396794 entry states the generating equation and divisibility conjecture recorded in hanna2026a396794. The normalization is zero constant coefficient and coefficient one at degree one. All series below have integer coefficients.

PowerSeries(Z) denotes the formal power-series ring, with indeterminate X. The imported iterate(Z,f,3) is the third compositional iterate f(f(f(X))); the powers of X and the displayed multiplication are ordinary power-series operations. The operator choose selects a witness of the displayed proved existential proposition. All coefficient indices are natural numbers.

**Definition 1.1 (The normalized generating series).**

$$\operatorname{generatingSeries} = \operatorname{choose}\left(\exists f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((f \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 3\right) = X^{2} + 16 \cdot X^{3}) \land ((\operatorname{constantCoeff}\left(f\right) = 0) \land (\operatorname{coeff}\left(1, f\right) = 1)))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existence is proved by successive coefficient corrections, starting from X. At degree n, the error coefficient at degree n+1 is divided by four using integer division. The mod-sixteen product identity makes this division exact and makes the correction divisible by four. The stabilized coefficients give an integer series satisfying all three clauses of the existential proposition.

**Definition 1.2 (The coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value a(n) is the degree-n coefficient of generatingSeries. The generating equation below gives a(0)=0 and a(1)=1.

**Theorem 1.3 (The OEIS equation and normalization).**

$$(\operatorname{generatingSeries} \cdot \operatorname{iterate}\left(\mathbb{Z}, \operatorname{generatingSeries}, 3\right) = X^{2} + 16 \cdot X^{3}) \land ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land (\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed series satisfies the product equation as an identity of formal power series, together with both normalization conditions. Existential witness selection preserves these three proved properties.

**Theorem 1.4 (Uniqueness among normalized integer series).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (f \cdot \operatorname{iterate}\left(\mathbb{Z}, f, 3\right) = X^{2} + 16 \cdot X^{3}) \implies (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies f = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose two normalized series agree below degree n. Their third iterates differ at degree n by three times their coefficient difference. Their products therefore differ at degree n+1 by four times that difference. Equal products force equal coefficients, and strong induction proves equality of the series.

**Theorem 1.5 (The A396794 divisibility conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies 4 \mid \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396794-triple-iterate-product-mod-four` (proved) by `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396794-triple-iterate-product-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/TripleIterateProductModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396794, G.f. A(x) satisfies A(x)*A(A(A(x))) = x^2 + 16*x^3*. URL: <https://oeis.org/A396794>.

*Commentary.*

Induct on n and truncate the solution below degree n. Earlier coefficients make this prefix congruent to X modulo four. Over ZMod(16), writing it as X+4B gives its jth iterate as X+4jB, so its product with the third iterate is X squared. Comparing the prefix with the solution by the coefficient-perturbation identity gives 16 dividing 4a(n), hence 4 dividing a(n). This proves the conjecture for every n greater than one.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.hanna_conjecture`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
