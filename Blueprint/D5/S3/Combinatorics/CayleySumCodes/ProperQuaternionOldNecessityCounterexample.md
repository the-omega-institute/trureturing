# Actual finite-group refutation

## Abstract

Proper-normal necessity counterexample

**Theorem 1.1 (The source counterexample).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The exact Example2.3(3) uses G=QuaternionGroup2 times the multiplicative form of ZMod3, H=Q8 times the identity and Y={(1,0),(-1,0),(1,1),(1,2)} in additive notation. The finite proof establishes that H is proper, normal and a total perfect subgroup code in this same actual graph. The unique internal representative of any normal transversal is central, and every central member of H is a square of H. Thus the old necessity fails even on proper normal subgroups; this is independent of the two whole-group examples.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples](QuaternionDihedralCounterexamples.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
