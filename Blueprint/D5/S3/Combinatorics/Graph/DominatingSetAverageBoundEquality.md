# Equality Graphs for the Two-Thirds Bound

## Abstract

The equality characterization is Theorem 2.9 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475. A graph is star-like precisely when every vertex is a leaf or a stem having one or two leaf neighbours.

**Theorem 1.1 (Strictness outside stem blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.residual_total_lt_of_core_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.residual_total_lt_of_core_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an isolate-free graph has a vertex in no stem block, the residual critical-incidence estimate is strict.

**Theorem 1.2 (Strictness for three leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.active_block_total_lt_of_large_stem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.active_block_total_lt_of_large_stem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a stem has at least three leaf neighbours, the active-block critical-incidence estimate is strict.

**Theorem 1.3 (Equality of incidence counts).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.critical_total_eq_of_avd_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.critical_total_eq_of_avd_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the two-thirds average bound gives equality of the total critical and omitted incidence counts.

**Theorem 1.4 (Equality forces a star-like graph).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.starLike_of_avd_eq_two_thirds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.starLike_of_avd_eq_two_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An isolate-free graph attaining average 2|V(G)|/3 is star-like. A vertex outside all stem blocks or a stem with three leaves would give a strict incidence inequality.

**Theorem 1.5 (Star-like graphs attain equality).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_of_starLike`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_of_starLike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite star-like graph without isolated vertices has dominating-set average equal to two thirds of its order.

**Theorem 1.6 (Beaton–Cameron equality characterization).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_iff_starLike`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_iff_starLike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite graph without isolated vertices, the average cardinality of dominating sets equals two thirds of the graph order if and only if every vertex is a leaf or a stem with one or two leaf neighbours.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.active_block_total_lt_of_large_stem`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_iff_starLike`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.avd_eq_two_thirds_of_starLike`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.critical_total_eq_of_avd_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.residual_total_lt_of_core_nonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality.starLike_of_avd_eq_two_thirds`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBound](DominatingSetAverageBound.md)
