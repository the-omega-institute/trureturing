# Weighted cancellation on arbitrary finite incidence relations

## Abstract

General weighted-incidence cancellation and the consumed six-object grid reduction.

Objects and both key types are arbitrary and need not be finite types. The structural cancellation theorem allows every positive column degree and arbitrary complex weights. The six-object consequences use degree inequalities and finite-set bijections to obtain the actual lattice grid. There is no finite incidence catalog, certified instance or exhaustive computation.

**Theorem 1.1 (Bounds for occupied key sets).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.occupied_key_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.occupied_key_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite set s of six objects and arbitrary row and column key types, assume that the pair of keys is injective and each occupied row and column contains at least two objects. The number of occupied rows is between two and three. Summing row degrees gives the upper bound; injectivity embeds any column fiber into the occupied rows and gives the lower bound. This result is used in nonzero_weight_incidence and in the lattice grid proof.

**Theorem 1.2 (Cancellation forces a uniquely omitted weight to vanish).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.missing_column_weight_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.missing_column_weight_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be any finite set of objects, with arbitrary row and column key types and jointly injective keys. Let d be any positive natural number, every occupied column have degree d, and w be any complex function on column keys. Suppose every occupied row has weighted sum zero. If an occupied row contains all occupied columns except exactly j, then w(j)=0. There is no bound on the number of objects or keys and no modulus or nonvanishing assumption on w. Summing by rows gives zero; summing by columns gives d times the total column weight, hence that total is zero. Joint injectivity identifies the row sum with the sum over its column image. Subtracting it from the column total leaves w(j)=0. The proof directly uses Mathlib Finset.sum_fiberwise_of_maps_to, Finset.sum_fiberwise_of_maps_to', Finset.sum_image and Finset.sum_sdiff. The live consumer nonzero_weight_incidence applies this theorem at d=2 and contradicts its nonzero-weight hypothesis.

**Theorem 1.3 (The six-object cancellation reduction).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.nonzero_weight_incidence`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.nonzero_weight_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For six arbitrary objects with jointly injective row and column keys and minimum occupied fiber degree two on both sides, let every occupied column carry a nonzero complex weight and let all row sums vanish. Then one occupied key set has cardinality two. If neither did, the degree bounds would force three occupied rows and three occupied columns, each of degree two. An actual row then omits exactly one occupied column, whose nonzero weight contradicts missing_column_weight_eq_zero. This is a symbolic finite-set argument, with no enumeration of matrices or specialization to Fin 3. Its lattice consumer is KhetanLatticeGeometry.actual_incidence_two, on the proof path to two_direction_cancellation_grid.

**Theorem 1.4 (Completeness has witnesses among the original objects).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.complete_incidence_of_two`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.complete_incidence_of_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For six arbitrary objects with jointly injective keys, if exactly two row keys and at most three column keys occur, exactly three columns occur and every occupied row-column pair has a witness in s. The key image is a subset of the occupied Cartesian product; injectivity and equal cardinality make it the whole product. The actual grid proof in KhetanLatticeGeometry uses these original-object witnesses in both orientations.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.complete_incidence_of_two`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.missing_column_weight_eq_zero`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.nonzero_weight_incidence`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.occupied_key_bounds`
