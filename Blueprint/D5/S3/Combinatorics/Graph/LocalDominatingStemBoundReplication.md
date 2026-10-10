# One-leaf replication of partial dominating families

## Abstract

A hub with one pendant leaf connects replicated graph copies at a prescribed vertex set.

**Definition 1.1 (Partial domination).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.PartialDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.PartialDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph H on V, a finite subset U of V, and S⊆V, PartialDominating(H,U,S) means that every x outside U either belongs to S or has an H-neighbor in S.

**Definition 1.2 (The partial dominating family).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.partialSets`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.partialSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The family partialSets(H,U) contains exactly the finite vertex subsets partially dominating outside U. Every dominating set of H belongs to this family. The full vertex set belongs to both families, including when V is empty.

**Definition 1.3 (The one-leaf hub graph).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any nonnegative integer r, the vertex type is (Fin(r)×V)⊕Fin(2). Two copied vertices (i,x),(j,y) are adjacent exactly when i=j and H has edge xy. The hub z is the right vertex 0, its pendant w is the right vertex 1, and z is joined to (i,u) exactly for u∈U. The right vertices are adjacent. There are rh+2 vertices, where h is the order of H.

**Theorem 1.4 (Absence of isolated vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_no_isolates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_no_isolates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H with decidable adjacency, subset U, and r≥0, if every vertex of H has positive degree, every vertex of the replicated graph has positive degree. Copied vertices retain an H-neighbor; z and w are neighbors of each other.

**Theorem 1.5 (Domination with the hub selected).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_with_hub_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_with_hub_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, subset U, r≥0, and subset S of the replicated vertices containing z, S dominates the replicated graph if and only if each slice {x:(i,x)∈S} partially dominates H outside U. The pendant can be freely selected.

**Theorem 1.6 (Domination with the hub omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_without_hub_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_without_hub_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, subset U, r≥0, and subset S of the replicated vertices omitting z, S dominates the replicated graph if and only if w∈S and each slice {x:(i,x)∈S} dominates H internally.

**Theorem 1.7 (Count with the hub selected).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, U⊆V and r≥0, write a=|partialSets(H,U)|. The number of dominating sets of the replicated graph containing z equals 2a^r.

**Theorem 1.8 (Count with the hub omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, U⊆V and r≥0, write b=|domSets(H)|. The number of dominating sets of the replicated graph omitting z equals b^r.

**Theorem 1.9 (Cardinality sum with the hub selected).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, U⊆V and r≥0, write a=|partialSets(H,U)| and α=familyAverage(partialSets(H,U)). The sum of |S| over the replicated dominating sets containing z equals 2a^r(3/2+rα). The hub contributes one, the free pendant contributes one half on average, and the r slices contribute rα.

**Theorem 1.10 (Cardinality sum with the hub omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, U⊆V and r≥0, write b=|domSets(H)| and β=avd(H). The sum of |S| over the replicated dominating sets omitting z equals b^r(1+rβ).

**Theorem 1.11 (Exact replicated average).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_average`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H, U⊆V and r≥0, with a=|partialSets(H,U)|, b=|domSets(H)|, α=familyAverage(partialSets(H,U)) and β=avd(H), the average order of the replicated graph equals [2a^r(3/2+rα)+b^r(1+rβ)]/[2a^r+b^r]. All averages and divisions are rational.

**Theorem 1.12 (The global bound rearranged).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replication_inequality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replication_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H and U⊆V, suppose every replicated graph has average at most two thirds of its order. Put h=|V| and c=2h/3. For every r≥0, a^r[1+6r(α−c)]≤b^r[1+3r(c−β)].

**Theorem 1.13 (Bound and equality for the partial family).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.relaxed_average_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.relaxed_average_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph H and U⊆V, suppose avd(H)≤2|V|/3 and every replicated graph has average at most two thirds of its order. Then familyAverage(partialSets(H,U))≤2|V|/3. If equality holds, partialSets(H,U)=domSets(H). If the first family is larger, the finite quadratic replication estimate gives strict inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.PartialDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_with_hub_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.dominating_without_hub_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.hubSets_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.omittedSets_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.partialSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.relaxed_average_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_average`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replicated_no_isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.replication_inequality`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](DominatingSetAverage.md)
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic](LocalDominatingStemBoundArithmetic.md)
