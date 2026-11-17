# Counting actual conjugacy classes in both branches

## Abstract

The full centralizer-index identity for normal total perfect subgroup codes.

**Theorem 1.1 (The extra reciprocal-index term).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite group, normal subgroup H and actual total-code connection set Y, choose any complete disjoint family of its conjugacy classes. The normal-core theorem proves H lies in each representative's centralizer. Thus [C_G(y_i):H] is a genuine subgroup index. Orbit-stabilizer and the actual disjoint class partition give the sum of reciprocal indices equal to one in case (a), and one plus 1/[G:H] in case (b). The identity is retained in counting Y despite the absence of graph loops. This is correction Proposition 3.1(iii), not an assumed numerical partition or a square-free-only formula.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers](CodeCentralizers.md)
