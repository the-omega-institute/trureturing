# Canonical local star semantics

## Abstract

Canonical local star semantics

For every finite simple graph, the set-valued local predicate equals the canonical non-induced two-leaf-star predicate. Set inclusion-minimality equals canonical finset inclusion-minimality, including the empty vertex type. The graph-specific H0 maxima are stated in CompositionParameters.

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

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.forms_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Semantics.minimal_iff`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants](Foundations/Invariants.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Foundations/LocalFormation](Foundations/LocalFormation.md)
