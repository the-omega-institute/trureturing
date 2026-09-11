# Scaled Reversion and Coefficient Congruence

## Abstract

Scaled reversion proves Hanna's coefficient congruences in OEIS A393856 and A393857.

Paul D. Hanna's entries hanna2026a393856 and hanna2026a393857 specify A(x-x*A(q*x)/q)=x for q=4 and q=5 and conjecture that every positive-index coefficient is one modulo q+1. The theorem below treats every positive natural q. The separate parity conjecture in A393856 is not addressed.

PowerSeries(R) denotes formal power series over R, X is the indeterminate, coeff(n,f) extracts coefficient n, and mk builds a series from its coefficient function. The notation subst(f,g) means f composed with g. The constant-series embedding is C; rescale(r,f) multiplies coefficient n by r to the power n. All indices and q are natural numbers. Sequence values and the final remainders are integers. In the formulas G(q) denotes generatingSeries(q), and P denotes the auxiliary iteration specified with the definition of a.

**Definition 1.1 (Stabilized integer coefficients).**

$$\begin{aligned}\forall q: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(q, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(q, n + 1\right)\right)\\\forall q: \mathbb{N}, \operatorname{P}\left(q, 0\right) = 0\\\forall q: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{P}\left(q, k + 1\right) = \operatorname{P}\left(q, k\right) + X - \operatorname{subst}\left(\operatorname{P}\left(q, k\right), \operatorname{inner}\left(q, \operatorname{P}\left(q, k\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting with the zero series, the correction P+X-subst(P,inner(q,P)) gains one degree of agreement at each iteration. Coefficient n is read at iteration n+1, where it has stabilized.

**Definition 1.2 (The integer generating series).**

$$\forall q: \mathbb{N}, \operatorname{G}\left(q\right) = \operatorname{mk}\left(\operatorname{a}\left(q\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function a(q) defines G(q) over the integers.

**Definition 1.3 (The integral inner argument).**

$$\forall q: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{inner}\left(q, f\right) = X - (X)^{2} \cdot \operatorname{mk}\left((n: \mathbb{N} \mapsto (\operatorname{cast}\left(q, \mathbb{Z}\right))^{n} \cdot \operatorname{coeff}\left(n + 1, f\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.inner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of degree n+2 subtracted from X is q to the power n times coefficient n+1 of f. This expression is integral and its constant and linear coefficients are zero and one, respectively.

**Theorem 1.4 (Existence and the rescaling identity).**

$$\begin{aligned}\forall q: \mathbb{N}, \\(\operatorname{subst}\left(\operatorname{G}\left(q\right), \operatorname{inner}\left(q, \operatorname{G}\left(q\right)\right)\right) = X) \land ((\operatorname{constantCoeff}\left(\operatorname{G}\left(q\right)\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{G}\left(q\right)\right) = 1) \land (\operatorname{C}\left(\operatorname{cast}\left(q, \mathbb{Z}\right)\right) \cdot (X - \operatorname{inner}\left(q, \operatorname{G}\left(q\right)\right)) = X \cdot \operatorname{rescale}\left(\operatorname{cast}\left(q, \mathbb{Z}\right), \operatorname{G}\left(q\right)\right))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement with arbitrarily late approximations proves the substitution equation. The first two coefficients follow from the initial iterations. The last conjunct identifies the inner argument by clearing the scalar denominator q; all four identities hold even at q=0.

**Theorem 1.5 (Uniqueness by first difference).**

$$\forall q: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{subst}\left(f, \operatorname{inner}\left(q, f\right)\right) = X) \implies f = \operatorname{G}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two series agree below degree d, their inner arguments agree below d+1. Substitution into a series beginning with X preserves the first nonzero coefficient of their difference. The correction therefore improves agreement by one degree. Induction proves uniqueness; no constant-coefficient assumption on f is needed.

**Theorem 1.6 (The functional equation with division by q).**

$$\forall q: \mathbb{N}, (1 \le q) \implies \operatorname{let} A = \operatorname{map}\left(\operatorname{intCastRingHom}\left(\mathbb{Q}\right), \operatorname{G}\left(q\right)\right), \operatorname{subst}\left(A, X - \operatorname{C}\left((\operatorname{cast}\left(q, \mathbb{Q}\right))^{-1}\right) \cdot X \cdot \operatorname{rescale}\left(\operatorname{cast}\left(q, \mathbb{Q}\right), A\right)\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_equation_rational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map the integer equation to rational coefficients. For positive q, multiplication by its reciprocal converts the rescaling identity into the displayed inner argument. Thus the constructed series satisfies exactly A(x-x*A(q*x)/q)=x.

**Theorem 1.7 (The parametric congruence).**

$$\forall q: \mathbb{N}, (1 \le q) \implies \forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(q, n\right) \bmod (q + 1) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.coeff_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduce the proved integer equation to ZMod(q+1), where q=-1. The series E=X/(1-X) has inner argument X/(1+X), and substituting this into E gives X. These identities follow by multiplying by unit denominators. The first-difference uniqueness proof works over every commutative ring, including ZMod(q+1), so the reduced generating series equals E. Its positive-degree coefficients are one. Since q+1 is at least two, one is the integer remainder.

**Theorem 1.8 (The A393856 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(4, n\right) \bmod 5 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393856` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393856-scaled-reversion-mod-five` (proved) by `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393856`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393856-scaled-reversion-mod-five","declaration_gid":"D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393856","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A393856, G.f. satisfies A(x - x*A(4*x)/4) = x*. URL: <https://oeis.org/A393856>.

*Commentary.*

Specializing the parametric theorem to q=4 proves the mod-five conjecture in hanna2026a393856 for every positive index.

**Theorem 1.9 (The A393857 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{a}\left(5, n\right) \bmod 6 = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393857` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393857-scaled-reversion-mod-six` (proved) by `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393857`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393857-scaled-reversion-mod-six","declaration_gid":"D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393857","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A393857, G.f. satisfies A(x - x*A(5*x)/5) = x*. URL: <https://oeis.org/A393857>.

*Commentary.*

Specializing the parametric theorem to q=5 proves the mod-six conjecture in hanna2026a393857 for every positive index.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.coeff_congruence`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_equation_rational`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393856`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.hanna_a393857`
- Truth anchor: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.inner`
