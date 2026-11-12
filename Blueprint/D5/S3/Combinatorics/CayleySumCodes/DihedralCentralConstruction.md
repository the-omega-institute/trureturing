# Retained constructions and exact corrected examples

## Abstract

DihedralCentralConstruction in the actual loopless sum graphs.

**Theorem 1.1 (Normality for every inverse-closed transversal).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.connection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.connection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The selected rotations are Z outside the central half-turn subgroup together with the half-turn, and the selected reflections form either parity class. Inverse closure and h+h=0 prove full conjugation invariance.

**Theorem 1.2 (The full retained central-half-turn total construction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.total` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every n, every half-turn h with h+h=0 and h nonzero, every inverse-closed actual additive transversal Z of {0,h}, and every parity character sending h to 1, the source connection admits {1,r(h)} as a total code. Both reflection classes and either internal representative of Z are retained. At n=4*k+2, h=2*k+1 and the source parity character satisfy these hypotheses for every k>=1.

**Theorem 1.3 (Normality of the exact perfect-code connection).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfectConnection_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfectConnection_normal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Removing the half-turn subgroup leaves exactly the source reflection class and Z outside that subgroup.

**Theorem 1.4 (The full retained central-half-turn perfect construction).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfect`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfect` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The same full parameter domain yields the source perfect code before the central half-turn is added. Outside the subgroup the total-code neighbor remains; inside it, only the vertex itself is in the closed neighborhood. These sufficient constructions do not supply the refuted exhaustive classification.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.connection_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfect`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.perfectConnection_normal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.total`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions](DihedralConstructions.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
