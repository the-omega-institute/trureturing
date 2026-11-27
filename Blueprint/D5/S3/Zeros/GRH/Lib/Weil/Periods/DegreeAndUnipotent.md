# Degree And Unipotent

## Abstract

Degree And Unipotent

Graded hermitian spaces: definite part plus string, unipotent and Bessel subgroups. Degree of graded matrices, adjoints, basic facts on the Bessel subgroup.

**Theorem 1.1 (mem_besselGroup_iff_sub_one).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeAndUnipotent.mem_besselGroup_iff_sub_one`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeAndUnipotent.mem_besselGroup_iff_sub_one` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

g lies in Grading.besselGroup if and only if it fixes each string vector of grade ≥ 0 up to higher grades: for such an index k, the entry (i, k) of its matrix minus 1 vanishes whenever grade(i) ≤ grade(k).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeAndUnipotent.mem_besselGroup_iff_sub_one`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceBasic](../../Adelic/Unitary/SpaceBasic.md)
