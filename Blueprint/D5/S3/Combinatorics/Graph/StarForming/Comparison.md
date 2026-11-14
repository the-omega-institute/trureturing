# Dissociation gives minimal star formation

## Abstract

Dissociation gives minimal star formation

Every inclusion-maximal dissociation set is inclusion-minimal two-star-forming, without bipartiteness or degree assumptions. An uncovered outside vertex could be adjoined while preserving selected degree at most one, contradicting maximality. Removing any selected vertex fails at that vertex itself. Actual finite attainment then gives beta two at most SF two. The lower comparison is attributed to Chellali and Favaron in the received source, without a novelty claim.

**Theorem 1.1 (independent self failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_self_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_self_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem independent_self_failure (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (v : V) (hv : v ∈ S) : ¬ Amplification.TwoAt G (↑(S.erase v)) v.

**Theorem 1.2 (independent insert of failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_insert_of_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_insert_of_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem independent_insert_of_failure (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (x : V) (hx : x ∉ S) (hfail : ¬ Amplification.TwoAt G (↑S) x) : IsKIndependent G 2 (insert x S).

**Theorem 1.3 (maximal independent minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Comparison.maximal_independent_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Comparison.maximal_independent_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem maximal_independent_minimal (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (hmax : ∀ x, x ∉ S → ¬ IsKIndependent G 2 (insert x S)) : IsMinimalStarForming G 2 S.

**Theorem 1.4 (beta le sf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Comparison.beta_le_sf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Comparison.beta_le_sf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_le_sf (G : SimpleGraph V) [DecidableRel G.Adj] : beta G 2 ≤ SF G 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Comparison.beta_le_sf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_insert_of_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Comparison.independent_self_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Comparison.maximal_independent_minimal`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DisjointUnion](DisjointUnion.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Semantics](Semantics.md)
