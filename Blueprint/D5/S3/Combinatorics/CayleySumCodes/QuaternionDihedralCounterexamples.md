# Actual finite-group refutation

## Abstract

Quaternion necessity counterexample

**Theorem 1.1 (The shared whole-group argument).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.whole_transversal_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.whole_transversal_squares` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For any actual group whose center consists of squares, every normal transversal of the whole group consists of squares. This is consumed by both the quaternion and dihedral necessity refutations; it does not impose an order-eight hypothesis.

**Theorem 1.2 (The source counterexample).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The source Example2.3(1) uses every element of QuaternionGroup2, H=G and the normal connection set {1,-1}. Its exact center and square set are both {1,-1}; every vertex has one distinct neighbor. Every normal transversal of G in itself is a singleton central element, hence a square. The actual matching therefore refutes the old singleton-nonsquare necessity. The surviving sufficiency and the separate dihedral and proper-normal examples remain distinct. No new classification is inferred.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.result`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.whole_transversal_squares`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
