# Code inheritance along every intermediate subgroup

## Abstract

Perfect and total perfect subgroup codes in the actual induced sum graph.

**Definition 1.1 (The same connection inside the subgroup).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.connection`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.connection` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The connection is the preimage of the given ambient normal subset under the subgroup inclusion. No inverse closure or choice of a transversal is added.

**Theorem 1.2 (Inherited conjugation invariance).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Conjugation by a subgroup element is the ambient conjugation, so the restricted connection remains normal as a subset of the subgroup.

**Theorem 1.3 (Equality with the induced loopless graph).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.graph_induce`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.graph_induce` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The restricted sum graph is exactly the ambient simple graph induced on the subgroup. Self-neighbors remain excluded; this is a graph equality on all subgroup vertices, not merely an equivalence of existential code witnesses.

**Theorem 1.4 (Every intermediate subgroup preserves the total code).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.total` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For H contained in M contained in G, every vertex of M retains its unique open neighbor in H, since that neighbor belongs to M. The connection set is the specified ambient connection restricted to M. No subnormality of M, normality of H, finiteness, or singleton-transversal criterion is used. This supplies a direct repaired route for the total-code part of antecedent Theorem 2.7 and stays distinct from normal-transversal inheritance. It asserts no quotient total-code inheritance.

**Theorem 1.5 (Perfect codes restrict through the closed neighborhood).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.perfect`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.perfect` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The unique member of H in each closed neighborhood of a vertex of M remains unique in the induced graph. This separately proves the perfect-code part, for arbitrary intermediate subgroups and arbitrary groups. The correction's unaffected-antecedent attribution is preserved; no CFSG case or quotient-class perfect-code criterion is certified by this restriction argument.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.connection`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.graph_induce`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.perfect`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SubgroupCodeRestriction.total`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
