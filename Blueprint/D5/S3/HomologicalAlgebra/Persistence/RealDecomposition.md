# Actual Natural Real Classification

## Abstract

Classify real interval sums, estimate image matching and construct actual interleavings.

**Theorem 1.1 (Existence and uniqueness against arbitrary finite competitors).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For every arbitrary field, finite-dimensional finite diagram and strictly increasing real grid, choose the already constructed homogeneous interval basis. Birth is its birth breakpoint; death is the next breakpoint after its last vertex or infinity for a final survivor.

Supported coordinate restriction, Basis.equivFun and its reconstruction sum give component isomorphisms. The existing occurrence naturality equations give all real arrow squares, including the zero prefix and unrestricted final tail. An empty or zero chain has an empty occurrence set. These coordinate suppliers are applied inside the natural classification proof.

Every competing finite positive-length interval family, with arbitrary real births and finite or infinite deaths, that is naturally isomorphic to the same actual module has the same endpoint occurrence counts. Component isomorphisms and naturality transport actual image ranks using the pinned range and finrank suppliers. The proof constructs the surviving-coordinate image equivalence, then uses common finite endpoint cuts and integer differences to isolate each multiplicity. The exact stability theorem transfers interleavings through these natural classifications.

**Theorem 1.2 (Fixed same-image matching with quantitative coverage).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_quantitative_image_matching`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_quantitative_image_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The sorted union of both families' births and finite deaths determines a common grid. Endpoint membership establishes invertible source, target and image transports inside each cell. The zero prefix follows from actual target support, including an empty grid. Compatible sampled-image maps, using the image functor on invertible squares, form a natural isomorphism to the same categorical image; finite-diagram classification constructs one image family. Both transported factors use that family and compose to the original morphism. A finite reindexing preserves arbitrary occurrence universes. Sorted birth and death fibers and both ordinal-preserving embeddings are returned once, before the universal quantifier over the independent nonnegative kernel and cokernel parameters. Actual kernel and range conditions for the original morphism transfer to these same factors. Their trim estimates give target birth at most image birth, equal image and source births, and image birth at most target birth plus the cokernel parameter. Image and target deaths agree and are at most source death; finite source death is at most image death plus the kernel parameter. The fixed embeddings cover every source or target interval longer than its corresponding parameter and every essential. Source essential death is equivalent to image essential death on paired occurrences. Every unmatched finite interval has length at most its parameter. A zero kernel parameter forces full source coverage and equal deaths; a zero cokernel parameter forces full target coverage and equal births. Empty and zero families are allowed. The exact stability theorem applies these estimates to an actual shifted interleaving map.

**Theorem 1.3 (Exact actual interleaving, occurrence matching and extended isometry).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_exact_stability`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_exact_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For any two finite-dimensional finite diagrams over an arbitrary field and their independently chosen strictly increasing real grids, the natural classifications supply positive-length finite occurrence families and actual real-extension isomorphisms. These families are chosen before the radius. At every nonnegative real radius, actual natural maps satisfying both shifted composite equations exist if and only if there is a partial occurrence matching with both endpoint deviations at most that radius and every unmatched length at most twice the radius. Infinite deaths must be paired to infinite deaths. The forward proof uses both equations to obtain the kernel condition and the cokernel range condition at the correctly shifted component. A natural coordinate comparison expresses the shifted target by translated endpoints, and the fixed same-image estimates provide one occurrence matching. Conversely, conditional scalar coordinate copies satisfy every naturality square and both actual composites, including short or disjoint pairs. Conjugation by the classifications transfers both directions to the original real extensions. The finite nonnegative feasible-radius sets agree, hence their infima in the extended nonnegative reals agree. Empty feasible sets have infimum infinity. Zero radius, critical lengths, tied occurrences, empty diagrams, essential bars and unrestricted tails are included.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_exact_stability`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_quantitative_image_matching`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.exists_unique_decomposition`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition](FiniteIntervalDecomposition.md)
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness](RealIntervalUniqueness.md)
