# An obstruction to compatible categorical homotopies

## Abstract

An obstruction to compatible categorical homotopies

**Theorem 1.1 (A noncontractible face poset forces disjoint images of a shared singleton).**

Lean statement: `D5/S3/Topology/StableCategory/CompatibleLowerCoverFence.exists_disjoint_singleton_of_schedule`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/CompatibleLowerCoverFence.exists_disjoint_singleton_of_schedule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Suppose two lower sets cover a face poset that admits no contraction. At each stage of the two regional homotopies, the regional maps may change in either order direction independently. The homotopies start at the inclusions and use a common constant endpoint or take place in a connected ambient face poset. Some stage must send a shared singleton to disjoint faces. Otherwise the regional maps glue by taking their intersection on the overlap, and taking the larger map independently on each side inserts a compatible common upper stage between consecutive pairs. The assembled homotopy would contract the ambient face poset.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/CompatibleLowerCoverFence.exists_disjoint_singleton_of_schedule`
- Dependency: [D5/S3/Topology/BarycentricGraphDistance](../BarycentricGraphDistance.md)
- Dependency: [D5/S3/Topology/ConnectedCategoryGraft](../ConnectedCategoryGraft.md)
