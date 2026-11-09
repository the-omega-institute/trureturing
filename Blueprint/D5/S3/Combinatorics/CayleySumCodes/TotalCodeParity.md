# Open-neighbor parity

## Abstract

A finite total perfect code induces a matching and has even cardinality.

**Theorem 1.1 (Degree one on the code).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/TotalCodeParity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/TotalCodeParity.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

In any simple graph on a finite group, a total perfect code C has exactly one neighbor at every vertex of the induced graph on C. Its components are therefore edges, and its cardinality is even. The proof transfers the actual unique-neighbor predicate to the induced graph and applies Mathlib's handshaking lemma. It includes arbitrary code subsets and hence the subgroup codes of the manuscripts. Self-neighbors never count. Even cardinality alone gives no converse existence theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/TotalCodeParity.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
