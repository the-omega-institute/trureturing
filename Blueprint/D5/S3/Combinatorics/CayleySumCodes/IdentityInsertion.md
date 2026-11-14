# Connection sets and loopless graphs

## Abstract

Identity insertion for subgroup total codes, with the exact simple-graph equality boundary.

**Theorem 1.1 (When the graph changes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.graph_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.graph_eq_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

If 1 is absent from a finite group's normal connection set Y, inserting it preserves the simple sum graph precisely when g*g=1 for every ambient element g. Otherwise the distinct vertices g and g inverse gain an edge. In an exponent-at-most-two group insertion adds only excluded loops. The revised source says another connection set, repairing the original version's unconditional another-graph wording.

**Theorem 1.2 (Preserving the subgroup code).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

If the squares of H form the singleton {1}, H is a total perfect code for Y union {1} if and only if it is a total perfect code for Y. No restriction on ambient squares outside H is assumed. Any new product g*h=1 with h in H forces g=h, so it contributes only an excluded loop. This preserves all code incidences even if other graph edges change. The square-set-two conversion and general regular classifications remain separate source statements.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.graph_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
