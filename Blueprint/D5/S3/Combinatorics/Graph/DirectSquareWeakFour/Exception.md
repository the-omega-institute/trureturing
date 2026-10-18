# The exceptional order-five obstruction

## Abstract

The exceptional order-five obstruction

The universal linear lower bound permits eleven landmarks at order five. Their incidence structure forces an additional contradiction.

**Theorem 1.1 (Eleven landmarks are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception.five_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception.five_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No actual weak-four landmark set on Fin 5 times Fin 5 has eleven elements. Each incidence part would have one degree-three vertex and four degree-two vertices. A low vertex with two low neighbors forces a four-cycle with degree total nine, whose diagonal pair is separated by only three. Thus each of the eight low vertices needs an edge to a high vertex, but the two high degrees provide only six incidences.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception.five_obstruction`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound](Bound.md)
