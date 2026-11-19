# Local star formation on arbitrary graphs

## Abstract

Local star formation on arbitrary graphs

The local witness predicate describes a non-induced two-leaf star containing each outside vertex. Inclusion-minimality is characterized by actual failures after single deletions. The graph, vertex type and selected set are arbitrary. These local proofs come from the original Amplification source in subquorum-colorings revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.

**Definition 1.1 (TwoAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.TwoAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.TwoAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def TwoAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.

**Definition 1.2 (Forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Forms`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Forms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Forms {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.

**Definition 1.3 (Minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Minimal`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Minimal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Minimal {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop.

**Definition 1.4 (LiteralAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.LiteralAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.LiteralAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def LiteralAt {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) : Prop.

**Theorem 1.5 (literal iff local).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.literal_iff_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.literal_iff_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem literal_iff_local {V : Type*} (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∉ S) : LiteralAt G S x ↔ TwoAt G S x.

**Theorem 1.6 (twoAt mono).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.twoAt_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.twoAt_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem twoAt_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) {x : V} : TwoAt G S x → TwoAt G T x.

**Theorem 1.7 (minimal of deletion failures).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.minimal_of_deletion_failures`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.minimal_of_deletion_failures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem minimal_of_deletion_failures {V : Type*} (G : SimpleGraph V) (S : Set V) (hforms : Forms G S) (hfail : ∀ selected ∈ S, ∃ x, x ∉ S \ {selected} ∧ ¬ TwoAt G (S \ {selected}) x) : Minimal G S.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.LiteralAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.Minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.TwoAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.literal_iff_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.minimal_of_deletion_failures`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation.twoAt_mono`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants](Invariants.md)
