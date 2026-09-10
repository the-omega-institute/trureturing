# A Complete Checked Origin-Sector Traversal

## Abstract

A concrete rational forest excludes simultaneous small residuals on a proper signed-Cayley sector of the actual real-X seed.

**Theorem 1.1 (No six-residual near-zero occurs in the stated five-dimensional sector).**

Lean statement: `D5/S3/Quantum/Tomography/RealXCheckedOriginSector.no_common_unbiased_sublevel_in_checked_origin_sector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RealXCheckedOriginSector.no_common_unbiased_sublevel_in_checked_origin_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement displays the exact seed matrix over Q(i,sqrt(21)) and the dephased signed-Cayley vector. Each of the five free real parameters lies in [-1/5,1/5]. The conclusion excludes simultaneous absolute residuals at most 1/64 for all six outcomes.

The finite source contains 237 ordered nodes: 119 interval-expression exclusions and 118 closed splits. Every numerical annotation is independently rechecked, both split halves are retained, and each leaf expression must have the specified residual syntax. A separate identity relates that syntax to the actual conjugate-transpose measurement. No local enclosure or global cover is supplied as a premise.

This is an integration instance on a proper subregion of chart zero, not the full 32-chart cover or a new Hadamard neighborhood exclusion. The proof script requests kernel reduction of the literal check, but local Lean elaboration has not been executed. Existing Krawczyk contraction records still need their own executable proof adapter.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/RealXCheckedOriginSector.no_common_unbiased_sublevel_in_checked_origin_sector`
- Dependency: [D5/S0/Certificates/CheckedRationalBoxCover](../../../S0/Certificates/CheckedRationalBoxCover.md)
