# Actual edges and landmark distance multisets

## Abstract

Actual edges and landmark distance multisets

Every actual unordered edge has a unique representation e(u,v) with u different from v. Its distance from a landmark is the minimum of the two actual shortest endpoint distances. Mapping the landmark multiset retains multiplicities. The four distance classes exhaust every landmark, including both original and midpoint vertices. These are the edge-multiset conventions of arXiv:2607.10311v1, section 6.1, printed page 20.

**Definition 1.1 (incidence).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

An incidence is the actual unordered edge joining u to the midpoint of uv.

**Theorem 1.2 (incidence mem).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every ordered pair of distinct originals supplies an actual graph edge.

**Theorem 1.3 (incidence eq iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Two incidence edges coincide exactly when both ordered original indices coincide.

**Theorem 1.4 (edge iff incidence).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edge_iff_incidence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edge_iff_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every actual graph edge is represented by an ordered pair of distinct originals.

**Definition 1.5 (edgeDistance).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The unordered-edge distance is the minimum of its two actual shortest endpoint distances.

**Theorem 1.6 (edgeDistance original).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_original`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

An original landmark has edge distance zero, one or two according to whether it is the first, second or another original.

**Theorem 1.7 (edgeDistance midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A midpoint landmark has edge distance zero at the edge midpoint, one when incident to its original endpoint, two when incident only to its other original, and three otherwise.

**Theorem 1.8 (edgeDistance le three).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every actual edge distance to every graph vertex is at most three.

**Definition 1.9 (profile).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The distance multiset maps every landmark once and keeps repeated distance values.

**Definition 1.10 (Resolves).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.Resolves`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.Resolves` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Resolution means injectivity of the multiset profile on the entire actual unordered edge set.

**Theorem 1.11 (profile count).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The multiplicity of k is exactly the number of selected vertices at actual edge distance k.

**Theorem 1.12 (profile eq iff four counts).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_eq_iff_four_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_eq_iff_four_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Equality of profiles on actual edges is equivalent to equality of the four multiplicities for distances zero through three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.Resolves`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_le_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_midpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edgeDistance_original`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.edge_iff_incidence`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.incidence_mem`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles.profile_eq_iff_four_counts`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric](CompleteSubdivisionMetric.md)
