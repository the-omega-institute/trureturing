# Separated long-core words and actual cardinality

## Abstract

Separated long-core words and actual cardinality

The original two twenty-vertex patterns, internal adjacency table and forward edges are retained unchanged. No consecutive A patterns is an explicit hypothesis. It forces every selected edge to be internal, giving dissociation for arbitrary successor maps. The canonical finite graph selection has size equal to the sum of twelve per A block and ten per B block, and provides that actual beta lower bound. It does not establish all parameters, boundary charges or the full L_k graph identity.

**Definition 1.1 (insideRows).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideRows`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideRows` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def insideRows : List (List Nat).

**Definition 1.2 (insideAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def insideAdj (first second : Fin 20) : Prop.

**Definition 1.3 (pattern).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pattern (kind : Bool) : List Nat.

**Definition 1.4 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selected (kind : Bool) (vertex : Fin 20) : Prop.

**Definition 1.5 (forward).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forward (first second : Fin 20) : Prop.

**Definition 1.6 (wordAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.wordAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.wordAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def wordAdj {Block : Type} (successor : Block → Block) (first second : Block × Fin 20) : Prop.

**Theorem 1.7 (inside dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_dissociates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_dissociates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem inside_dissociates (kind : Bool) : Dissociates insideAdj (selected kind).

**Theorem 1.8 (pattern counts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern_counts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pattern_counts : ∀ kind : Bool, ((List.finRange 20).filter (fun vertex => decide (selected kind vertex))).length = (if kind then 12 else 10) ∧ (([(12, 13), (14, 15), (16, 17)] : List (Nat × Nat)).filter (fun pair => !(pattern kind).contains pair.1 && !(pattern kind).contains pair.2)).length = (if kind then 1 else 2).

**Theorem 1.9 (forward selected forces A).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward_selected_forces_A`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward_selected_forces_A` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forward_selected_forces_A : ∀ firstKind secondKind : Bool, ∀ first second : Fin 20, selected firstKind first → selected secondKind second → forward first second → firstKind = true ∧ secondKind = true.

**Theorem 1.10 (selected edge internal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected_edge_internal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected_edge_internal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_edge_internal {Block : Type} (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) (first second : Block × Fin 20) (hfirst : selected (word first.1) first.2) (hsecond : selected (word second.1) second.2) (hedge : wordAdj successor first second) : first.1 = second.1 ∧ insideAdj first.2 second.2.

**Theorem 1.11 (word dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.word_dissociates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.word_dissociates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem word_dissociates {Block : Type} (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) : Dissociates (wordAdj successor) (fun vertex => selected (word vertex.1) vertex.2).

**Theorem 1.12 (inside simple).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_simple` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem inside_simple : (∀ v : Fin 20, ¬ insideAdj v v) ∧ (∀ v w : Fin 20, insideAdj v w ↔ insideAdj w v).

**Definition 1.13 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph {Block : Type} (successor : Block → Block) : SimpleGraph (Block × Fin 20).

**Definition 1.14 (selectedSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedSet (word : Block → Bool) : Finset (Block × Fin 20).

**Theorem 1.15 (selectedSet card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selectedSet_card (word : Block → Bool) : (selectedSet word).card = ∑ i : Block, (if word i then 12 else 10).

**Theorem 1.16 (beta word lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.beta_word_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.beta_word_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_word_lower (successor : Block → Block) (word : Block → Bool) (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) : (∑ i : Block, (if word i then 12 else 10)) ≤ beta (graph successor) 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.beta_word_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.forward_selected_forces_A`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.insideRows`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_dissociates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_simple`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.pattern_counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selectedSet_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.selected_edge_internal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.wordAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.word_dissociates`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
