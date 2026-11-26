# Local replacement and the exact H0 block cap

## Abstract

Local replacement and the exact H0 block cap

A minimal ambient selection cannot retain seven vertices in an induced H0 block whose nonport neighborhoods are unchanged. A local dense-selection certificate gives either a safe nonport deletion or an isolated nonport; the latter contradicts formation. The proof replaces an actual local selection and preserves formation throughout the ambient graph. It does not assert the same upper bound for unrestricted attachments.

**Theorem 1.1 (forms erase of local replacement).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Composition.forms_erase_of_local_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Composition.forms_erase_of_local_replacement` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_erase_of_local_replacement {V : Type*} (G : SimpleGraph V) (S tile : Set V) (deleted : V) (hdeleted : deleted ∈ tile) (hforms : Forms G S) (hinside : ∀ x ∈ tile, x ∉ S \ {deleted} → TwoAt G (S \ {deleted}) x) (hnooutside : ∀ x, x ∉ tile → ¬ G.Adj x deleted) (hreplace : ∀ center ∈ S, G.Adj center deleted → ∀ x, x ∉ tile → G.Adj x center → ∃ leaf ∈ S \ {deleted}, G.Adj center leaf) : Forms G (S \ {deleted}).

**Definition 1.2 (HasLocalDeletion).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Composition.HasLocalDeletion`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Composition.HasLocalDeletion` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def HasLocalDeletion (selection : Finset (Fin 10)) : Prop.

**Definition 1.3 (HasIsolatedNonport).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Composition.HasIsolatedNonport`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Composition.HasIsolatedNonport` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def HasIsolatedNonport (selection : Finset (Fin 10)) : Prop.

**Theorem 1.4 (local dense certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Composition.local_dense_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Composition.local_dense_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem local_dense_certificate (selection : Finset (Fin 10)) (hcard : 7 ≤ selection.card) : HasIsolatedNonport selection ∨ HasLocalDeletion selection.

**Theorem 1.5 (family block upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Composition.family_block_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Composition.family_block_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem family_block_upper {I : Type*} (interfaces : I → I → Prop) (S : Set (I × Fin 10)) (hminimal : Minimal (family interfaces) S) (block : I) : (blockSelection S block).card ≤ 6.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Composition.HasIsolatedNonport`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Composition.HasLocalDeletion`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Composition.family_block_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Composition.forms_erase_of_local_replacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Composition.local_dense_certificate`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Amplification](Amplification.md)
