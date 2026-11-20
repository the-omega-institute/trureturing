# Topologically exact maps on finite bouquets of circles

## Abstract

Topologically exact maps on finite bouquets of circles

Identify the origins of N labelled circles to form a bouquet. Projection forgets the label. A traversal of the bouquet visits all circles consecutively, sending each junction of the traversal to the common vertex.

**Theorem 1.1 (The traversal descends continuously to the circle).**

Lean statement: `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.continuous_traverse`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.continuous_traverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive number of circles, concatenate the labelled circles at their common vertex. The finite closed quotient identifies the adjacent parameter endpoints and gives a continuous map from the circle onto the bouquet.

**Theorem 1.2 (A topologically exact map of positive expansivity order N).**

Lean statement: `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.exact_order`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.exact_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two, compose projection with traversal to obtain a continuous surjection of the compact bouquet. On the projected circle the map multiplies by N. The projection of any nonempty open set contains an arc, and a sufficiently large multiplication iterate maps the arc onto the circle. One more traversal covers the bouquet.

At a sufficiently small scale each strict forward Bowen ball lies in a projection fiber of size at most N. Points on different circles approach the shared vertex at the same projected phase, stay distinct at time zero, and coalesce at time one. At every positive scale they witness failure of a bound by N minus one.

Gangloff, Guillon and Oprocha's Remark 3.10 already realizes exact finite orders on bouquets. Its example of order greater than one maps into a proper subbouquet. The construction here adds surjectivity and topological exactness.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.continuous_traverse`
- Truth anchor: `D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.exact_order`
- Dependency: [D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic](CircleFinitePositiveExpansiveness/Basic.md)
- Dependency: [D5/S1/Dynamics/Shadowing/InvarianceGluedSheets](InvarianceGluedSheets.md)
