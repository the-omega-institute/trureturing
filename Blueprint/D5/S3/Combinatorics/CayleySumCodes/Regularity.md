# The exact square-set regularity dichotomy

## Abstract

Degrees and regularity of finite normal-connection sum graphs.

**Theorem 1.1 (The exact open degree).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/Regularity.degree_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/Regularity.degree_card` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

At g the actual neighbor set is bijective with Y minus {g squared}, by h maps to g h. Its cardinal is therefore |Y| minus one when the square lies in Y and |Y| otherwise. Self-neighbors are excluded; inverse closure of Y is unnecessary. This is the degree calculation used in correction section 3.2 and the regularity antecedents.

**Theorem 1.2 (All squares or no squares).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/Regularity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/Regularity.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite group and every conjugation-invariant connection set Y, all actual graph degrees are equal if and only if Y contains every square of G or contains none. Regularity is expressed by the neighbor cardinal at every vertex equaling that at the identity, which exists in every group. This supplies the full graph-regularity part of C7; abelian subgroup PC/TPC classifications, Frattini identities, the trivial-subgroup positive case and all reported enumeration tables remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/Regularity.degree_card`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/Regularity.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
