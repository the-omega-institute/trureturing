# Counting the arbitrary-interface H0 composition

## Abstract

Counting the arbitrary-interface H0 composition

Each selected vertex belongs to exactly one block. The exact fiber-cardinality sum converts the local six-vertex cap to a global bound and combines it with the displayed minimal selection. Empty index types remain in scope. The canonical SF and beta consequences are proved in Semantics; this module itself concerns actual minimal selections and their cardinalities.

**Theorem 1.1 (card eq sum blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.card_eq_sum_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ExactCard.card_eq_sum_blocks` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_eq_sum_blocks {I : Type*} [Fintype I] [DecidableEq I] (S : Finset (I × Fin 10)) : S.card = ∑ block : I, (blockSelection (↑S : Set (I × Fin 10)) block).card.

**Theorem 1.2 (family card upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.family_card_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ExactCard.family_card_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_card_upper {I : Type*} [Fintype I] [DecidableEq I] (interfaces : I → I → Prop) (S : Finset (I × Fin 10)) (hminimal : Minimal (family interfaces) (↑S : Set (I × Fin 10))) : S.card ≤ 6 * Fintype.card I.

**Theorem 1.3 (exact composition card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.exact_composition_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ExactCard.exact_composition_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exact_composition_card {I : Type*} [Fintype I] [DecidableEq I] (interfaces : I → I → Prop) : (∀ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) → S.card ≤ 6 * Fintype.card I) ∧ (∃ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) ∧ S.card = 6 * Fintype.card I).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.card_eq_sum_blocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.exact_composition_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ExactCard.family_card_upper`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Composition](Composition.md)
