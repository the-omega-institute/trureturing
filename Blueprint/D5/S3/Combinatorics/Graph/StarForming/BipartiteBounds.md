# Bipartition classes bound the actual maximum

## Abstract

Bipartition classes bound the actual maximum

Each color class of an actual two-coloring is independent and therefore dissociation. The two class cardinalities add to the whole finite order, proving n<=2 beta two with no regularity, nonempty or connectedness restriction. The classes need not have equal size.

**Theorem 1.1 (color class independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.color_class_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.color_class_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem color_class_independent (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) (i : Fin 2) : IsKIndependent G 2 (Finset.univ.filter (fun v => c v = i)).

**Theorem 1.2 (card le two beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.card_le_two_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.card_le_two_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem card_le_two_beta (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Colorable 2) : Fintype.card V ≤ 2 * beta G 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.card_le_two_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.color_class_independent`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Comparison](Comparison.md)
