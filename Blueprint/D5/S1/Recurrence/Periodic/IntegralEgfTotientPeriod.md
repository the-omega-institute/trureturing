# Totient Periods for Integral Exponential Substitutions

## Abstract

Integral exponential substitutions have totient periods, including OEIS A305550.

The notes bala2022a305550 and bala2022egfgeneral record Bala's specific and broader conjectures. The broader sentence appears on both A305550 and A004123 and is one conjecture, settled once. Every positive modulus m has period totient(m) from n at least m. Neither the onset nor the period is asserted to be minimal.

All indices are natural numbers. The function g maps natural numbers to integers. The functions Q, a, egfCoefficient and the imported T are integer-valued. Here T(g,n) is the factorial-weighted Stirling transform from StirlingTransformTotientPeriod: the sum of g(k) times k! times Nat.stirlingSecond(n,k) over k at most n. The notation rat denotes the cast to the rationals, integer denotes the natural-number cast to the integers, and residue(m,z) denotes the integer cast to ZMod m. The function factorial is Nat.factorial and totient is Nat.totient.

Every power series here has rational coefficients. The symbols X and exp denote PowerSeries.X and PowerSeries.exp over the rationals. The function mk forms a power series from its coefficients, coeff(n,F) extracts its coefficient at n, and subst(F,H) substitutes H into F. The function num returns the numerator of a rational in reduced form with positive denominator. Fractions in the generating identity are rational division. HasProd(f,F) states convergence of the finite products of f to F in the coefficientwise topology; tprod(f) is the corresponding infinite product. The function distincts is Mathlib's Nat.Partition.distincts, and card is finite-set cardinality.

**Theorem 1.1 (The exponential Stirling bridge).**

$$\forall g: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{rat}\left(\operatorname{factorial}\left(n\right)\right) \cdot \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{mk}\left((k: \mathbb{N} \mapsto \operatorname{rat}\left(\operatorname{g}\left(k\right)\right))\right), (exp - 1)\right)\right) = \operatorname{rat}\left(\operatorname{T}\left(g, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.egf_shift_eq_stirling_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand each power of exp(X)-1 by the binomial theorem. Powers of exp are rescaled exponentials, whose degree-n coefficients are j^n/n!. The imported Stirling inclusion-exclusion identity therefore gives n! times coeff(n,(exp(X)-1)^k) equal to k! times S(n,k). Since exp(X)-1 has zero constant coefficient, its k-th power is divisible by X^k. Terms with k greater than n vanish, turning substitution into a finite sum and proving the displayed bridge. Its integer right-hand side proves integrality as well.

**Definition 1.2 (Distinct-part partition counts).**

$$\forall n: \mathbb{N}, \operatorname{Q}\left(n\right) = \operatorname{integer}\left(\operatorname{card}\left(\operatorname{distincts}\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q counts partitions into distinct positive parts using Mathlib's existing finite set, and casts the count to an integer.

**Theorem 1.3 (The ordinary partition product).**

$$\operatorname{HasProd}\left((j: \mathbb{N} \mapsto 1 + (X)^{j + 1}), \operatorname{mk}\left((k: \mathbb{N} \mapsto \operatorname{rat}\left(\operatorname{Q}\left(k\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.distinct_parts_generating_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's count-restricted partition product at multiplicity bound two is the distinct-part product. Each factor is 1+X^(j+1).

**Definition 1.4 (The integer exponential coefficients).**

$$\forall g: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{egfCoefficient}\left(g, n\right) = \operatorname{num}\left(\operatorname{rat}\left(\operatorname{factorial}\left(n\right)\right) \cdot \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{mk}\left((k: \mathbb{N} \mapsto \operatorname{rat}\left(\operatorname{g}\left(k\right)\right))\right), (exp - 1)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.egfCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bridge proves the scaled rational coefficient is an integer. Taking its reduced numerator therefore extracts that integer exactly, and yields T(g,n). Thus egfCoefficient is the coefficient sequence of the e.g.f. G(exp(X)-1), for integral G with coefficients g.

**Definition 1.5 (The sequence of OEIS A305550).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{egfCoefficient}\left(Q, n\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the distinct-part counts Q as the integral coefficients of G. The next identity establishes the product e.g.f. at every degree, with offset zero.

**Theorem 1.6 (The defining product e.g.f.).**

$$\operatorname{mk}\left((n: \mathbb{N} \mapsto \frac{\operatorname{rat}\left(\operatorname{a}\left(n\right)\right)}{\operatorname{rat}\left(\operatorname{factorial}\left(n\right)\right)})\right) = \operatorname{tprod}\left((j: \mathbb{N} \mapsto 1 + ((exp - 1))^{j + 1})\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In each degree, substitution is a finite linear combination of coefficients and hence is continuous. Applying its algebra homomorphism to the ordinary partition product gives the product of 1+(exp(X)-1)^(j+1). The coefficient bridge identifies its degree-n coefficient with a(n)/n!, giving exactly the e.g.f. recorded in bala2022a305550.

**Theorem 1.7 (Bala's broader e.g.f. conjecture).**

$$\forall g: \mathbb{N} \to \mathbb{Z}, \forall m, n: \mathbb{N}, (0 < m) \implies ((m \le n) \implies (\operatorname{residue}\left(m, \operatorname{egfCoefficient}\left(g, n + \operatorname{totient}\left(m\right)\right)\right) = \operatorname{residue}\left(m, \operatorname{egfCoefficient}\left(g, n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_egf_general` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a305550-integral-egf-substitution-totient-period` (proved) by `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_egf_general`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a305550-integral-egf-substitution-totient-period","declaration_gid":"D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_egf_general","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *Bala's general totient-period conjecture for integral G(exp(x) - 1)*. URL: <https://oeis.org/A305550>.

*Commentary.*

The bridge identifies egfCoefficient(g,n) with the imported T(g,n). The weighted Stirling-transform totient-period theorem gives the displayed equality for every integral g and positive m from n at least m. This settles the single broader conjecture documented in bala2022egfgeneral, including its duplicate occurrence on A004123.

**Theorem 1.8 (Bala's A305550 conjecture).**

$$\forall m, n: \mathbb{N}, (0 < m) \implies ((m \le n) \implies (\operatorname{residue}\left(m, \operatorname{a}\left(n + \operatorname{totient}\left(m\right)\right)\right) = \operatorname{residue}\left(m, \operatorname{a}\left(n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_a305550` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a305550-distinct-part-egf-totient-period` (proved) by `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_a305550`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a305550-distinct-part-egf-totient-period","declaration_gid":"D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_a305550","resolution_kind":"proved"} -->

*Citation.* Peter Bala (2022). *OEIS A305550, Expansion of e.g.f. Product_{k>=1} (1 + (exp(x) - 1)^k)*. URL: <https://oeis.org/A305550>.

*Commentary.*

Specialize the broader theorem to Q. The proved generating_equation identifies a with the sequence of the defining A305550 product e.g.f., so the equality proves the conjecture in bala2022a305550.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.Q`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_a305550`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.bala_conjecture_egf_general`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.distinct_parts_generating_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.egfCoefficient`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.egf_shift_eq_stirling_transform`
- Truth anchor: `D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.generating_equation`
- Dependency: [D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod](StirlingTransformTotientPeriod.md)
