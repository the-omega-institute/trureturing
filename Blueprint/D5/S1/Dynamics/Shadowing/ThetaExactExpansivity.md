# Sharp finite positive expansivity on parallel-edge graphs

## Abstract

Sharp finite positive expansivity on parallel-edge graphs

**Theorem 1.1 (A topologically exact map of order one below the valence).**

Lean statement: `D5/S1/Dynamics/Shadowing/ThetaExactExpansivity.exists_exact_order_on_graph`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ThetaExactExpansivity.exists_exact_order_on_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two, the graph with two vertices and m plus one parallel edges admits a continuous surjection of least forward Bowen order m. Realize the m parallel arcs over one semicircle and identify the m copies of the other semicircle. The model is homeomorphic to the closed-edge quotient of the graph.

Identifying corresponding points of the negative semicircles across the labelled bouquet yields the graph map. Topological exactness descends from the bouquet, and projection to the circle semiconjugates the map to multiplication by m. Small forward Bowen balls are confined to one projection fiber. Distinct points over the same phase near a vertex have a common first image and witness the lower bound at every positive radius.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ThetaExactExpansivity.exists_exact_order_on_graph`
- Dependency: [D5/S1/Dynamics/Shadowing/BouquetExactExpansivity](BouquetExactExpansivity.md)
- Dependency: [D5/S1/Dynamics/Shadowing/TripleEdgeSubdivisionRealization](TripleEdgeSubdivisionRealization.md)
