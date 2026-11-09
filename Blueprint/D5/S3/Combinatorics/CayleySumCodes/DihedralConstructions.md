# Retained constructions and exact corrected examples

## Abstract

DihedralConstructions in the actual loopless sum graphs.

**Theorem 1.1 (The all-reflection normal connection).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

All reflections in the actual DihedralGroup n form a conjugation-invariant subset.

**Theorem 1.2 (The full complete bipartite graph).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_adjacency` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Adjacency is exactly between the rotation and reflection parts, so the entire graph is K_n,n. No loop is introduced.

**Theorem 1.3 (Every reflection subgroup in the all-reflection graph).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_total` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every order-two reflection subgroup is a total perfect code, for all source n. The theorem even allows the infinite n=0 model without using it as a replacement source domain.

**Theorem 1.4 (The two normal parity families).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For any additive parity character, odd rotations together with the selected reflection parity class form a normal subset.

**Theorem 1.5 (The complete retained parity total codes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_total` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every reflection subgroup matching the selected parity class is a total perfect code, with the exact open-neighbor convention. The source even n=2*l character is DihedralConstructions.parity; c=0 and c=-1 recover both families.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.parity_total`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_adjacency`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.reflections_total`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
