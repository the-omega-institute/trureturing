# Canonical finite maxima for H0 compositions

## Abstract

Canonical finite maxima for H0 compositions

The set-valued local predicate is equivalent to the canonical non-induced two-leaf-star predicate, and set minimality is equivalent to canonical finite-set inclusion-minimality. For every finite index type I and arbitrary directed port relation R, including the empty family and same-block entries, the graph has SF two equal to 6|I| and beta two equal to 5|I|. The beta upper bound restricts any dissociation set to actual H0 fibers; a whole bipartition side attains the lower bound. No connectivity or cycle restriction is introduced.

**Theorem 1.1 (forms iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Semantics.forms_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Semantics.forms_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Forms G (↑S : Set V) ↔ IsStarForming G 2 S.

**Theorem 1.2 (minimal iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Semantics.minimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Semantics.minimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Minimal G (↑S : Set V) ↔ IsMinimalStarForming G 2 S.

**Theorem 1.3 (sf family).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Semantics.sf_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Semantics.sf_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : SF (Amplification.family R) 2 = 6 * Fintype.card I.

**Theorem 1.4 (beta family).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Semantics.beta_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Semantics.beta_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : beta (Amplification.family R) 2 = 5 * Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.beta_family`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.forms_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.minimal_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.sf_family`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ExactCard](ExactCard.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting](../SubQuorum/DoubleStarGrafting.md)
