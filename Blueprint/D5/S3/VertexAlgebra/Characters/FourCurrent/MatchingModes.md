# Exact ordered matching coefficient

## Abstract

Exact ordered matching coefficient.

**Theorem 1.1 (Exact ordered matching coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes.bounded_coefficient_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes.bounded_coefficient_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive-definite lattice D, every current-label function i : Fin 4 → Fin D.rank and every natural grade function n : Fin 4 → Nat, the original bounded ten-matching coefficient equals orderedFourCurrentCoefficient D hD i n. Each nonzero matching assignment determines its positive edge frequency and arc orientation uniquely from the signed current modes; its initial grade equation is the creation delay plus independent winding energies and the residual and charge energies.

The signed pair trace is reduced using the original two-current result, including negative intermediate grades. Arc endpoint differences, disjoint labeled edges and signed-frequency recovery prove exact compatibility and uniqueness. Finite sums eliminate only assignments whose guarded weight vanishes. No matching or repeated-frequency multiplicity is identified or divided out. The ordered coefficient is consumed by the constant-grade and positive-channel proofs; this is the original finite coefficient proof, with no analytic or literature novelty assertion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes.bounded_coefficient_ordered`
- Dependency: [D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence](TraceRecurrence.md)
