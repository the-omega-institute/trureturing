# Actual Natural Real Classification

## Abstract

Construct and uniquely classify the actual natural real interval-sum decomposition.

**Definition 1.1 (The full real decomposition object).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.Decomposition`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.Decomposition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The output has one finite occurrence type, positive real half-open intervals with finite or infinite deaths, and an actual natural isomorphism from the real module to their supported coordinate sum. Universe lifting allows the field and original vector-space carriers to inhabit independent universes; it changes neither the maps nor the field.

**Theorem 1.2 (Existence and uniqueness against arbitrary finite competitors).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For every arbitrary field, finite-dimensional finite diagram and strictly increasing real grid, choose the already constructed homogeneous interval basis. Birth is its birth breakpoint; death is the next breakpoint after its last vertex or infinity for a final survivor.

Supported coordinate restriction, Basis.equivFun and its reconstruction sum give component isomorphisms. The existing occurrence naturality equations give all real arrow squares, including the zero prefix and unrestricted final tail. An empty or zero chain has an empty occurrence set. These coordinate suppliers are applied inside the substantive classification proof, not retained as a separate wrapper.

Every competing finite positive-length interval family, with arbitrary real births and finite or infinite deaths, that is naturally isomorphic to the same actual module has the same endpoint occurrence counts. Component isomorphisms and naturality transport actual image ranks using the pinned range and finrank suppliers. The proof constructs the surviving-coordinate image equivalence, then uses common finite endpoint cuts and integer differences to isolate each multiplicity. Induced matching, quantitative estimates, exact interleaving iff matching and extended isometry remain separate obligations.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.Decomposition`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/RealExtension](RealExtension.md)
