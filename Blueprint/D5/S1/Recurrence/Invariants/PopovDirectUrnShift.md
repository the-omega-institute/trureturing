# A direct first-urn bijection for Popov's shift

## Abstract

Chronological first-urn deletion and reinsertion give Popov’s shift identity.

Write U(m,t,k) for the orbits of legal chronological urn histories of length t with exactly k occupied pairs. The first m marbles must fill the first urn. Deletion records the tail positions J that avoid this urn, and records a first-urn color at every complementary position. It keeps the placements on J in increasing chronological order and drops the first urn from their rank system.

**Definition 1.1 (First-urn deletion and reinsertion).**

$$\forall m \in \mathbb{N}, \forall n \in \mathbb{N}, \forall r \in \mathbb{N}, 0 < m \implies \operatorname{U}\left(m, n + m, m + r\right) \sim \Sigma_{J \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)} (\operatorname{Colors}\left(m, n, J\right) \times \operatorname{U}\left(m, \operatorname{card}\left(J\right), r\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.firstUrnEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Colors(m,n,J) is the function type from the subtype of positions outside J to Fin(m). The dependent sum is called Payload(m,n,r). Reinsertion first puts back the forced prefix and then traverses the tail, inserting the recorded color or the next residual placement. A color is always legal in the full first urn, including when a later urn is partly full. The used pairs are the disjoint union of the m first-urn pairs and the shifted residual pairs.

**Theorem 1.2 (Reinsertion recovers the source orbit).**

$$\forall m \in \mathbb{N}, \forall n \in \mathbb{N}, \forall r \in \mathbb{N}, 0 < m \implies \forall q \in \operatorname{U}\left(m, n + m, m + r\right), \operatorname{reinsert}\left(\operatorname{delete}\left(q\right)\right) = q$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.reinsert_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The composite recovers the forced prefix and each chronological tail entry.

**Theorem 1.3 (Deletion recovers all payload data).**

$$\forall m \in \mathbb{N}, \forall n \in \mathbb{N}, \forall r \in \mathbb{N}, 0 < m \implies \forall b \in \operatorname{Payload}\left(m, n, r\right), \operatorname{delete}\left(\operatorname{reinsert}\left(b\right)\right) = b$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.delete_reinsert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank ranges separate selected placements and colors, so the composite recovers the subset, each color, and the residual orbit.

For k below m, the source fiber is empty because the forced prefix uses m distinct pairs. The signed payload uses the same subset and colors with the residual fiber in column k−m. That column is negative and its fiber is empty, so the payload is empty for every choice of tail positions.

**Theorem 1.4 (The urn count satisfies the published recurrence).**

$$\forall m \in \mathbb{N}, 0 < m \implies \forall t \in \mathbb{N}, \forall k \in \mathbb{N}, \operatorname{card}\left(\operatorname{U}\left(m, t, k\right)\right) = \operatorname{stirling}\left(m, t, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.card_urn_eq_stirling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one empty history and zero histories of positive length in column zero. At a positive column k the last move reuses one of the m floor(k/m) slots in complete urns or opens the unique fresh slot from column k−1. This gives Definition 7.1 and recurrence (7.1). The signed count S vanishes at negative columns.

**Theorem 1.5 (Popov's shift identity by finite counting).**

$$\forall m \in \mathbb{N}, \forall n \in \mathbb{N}, \forall k \in \mathbb{N}, 0 < m \implies \operatorname{S}\left(m, n + m, k\right) = \sum_{j=0}^{n} \operatorname{choose}\left(n, j\right) \cdot \operatorname{pow}\left(m, n - j\right) \cdot \operatorname{S}\left(m, j, k - m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.shift_7_2` (`✓ std3`). ∎

*Resolves.* `Problems/popov-2026-direct-urn-shift` (proved) by `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.shift_7_2` and `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.delete_reinsert` and `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.reinsert_delete`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"popov-2026-direct-urn-shift","declaration_gid":"D5/S1/Recurrence/Invariants/PopovDirectUrnShift.shift_7_2","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"popov-2026-direct-urn-shift","declaration_gid":"D5/S1/Recurrence/Invariants/PopovDirectUrnShift.delete_reinsert","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"popov-2026-direct-urn-shift","declaration_gid":"D5/S1/Recurrence/Invariants/PopovDirectUrnShift.reinsert_delete","resolution_kind":"proved"} -->

*Citation.* Vencislav Popov (2026). *m-Bell and m-Stirling numbers: Iterated binomial transforms, hyper-Bessel functions, and moments of the Conway–Maxwell–Poisson distribution*. DOI: [10.48550/arXiv.2608.12011](https://doi.org/10.48550/arXiv.2608.12011). URL: <https://arxiv.org/abs/2608.12011v1>.

*Commentary.*

Take the cardinalities of the exhibited equivalence. Subsets of cardinality j contribute the binomial coefficient and there are m to the power n−j complement color functions. The residual quotient contributes S(m,j,k−m). Popov's Theorem 7.3 gives the prior algebraic proof of the same identity.

At capacity one, the construction deletes the block containing the initial marble. If the tail is empty, the only occupied-count column is m, with one forced-prefix orbit and one empty residual orbit. In column m for any tail length, every tail marble uses one of the first-urn colors. Columns above the number of marbles are empty.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.card_urn_eq_stirling`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.delete_reinsert`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.firstUrnEquiv`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.reinsert_delete`
- Truth anchor: `D5/S1/Recurrence/Invariants/PopovDirectUrnShift.shift_7_2`
- Dependency: [D5/S1/Recurrence/Invariants/PopovUrnNormalization](PopovUrnNormalization.md)
