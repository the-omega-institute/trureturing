# CompatibleFamilyCheck

## Abstract

The original seven-dimensional written lower-bound proof.

**Theorem 1.1 (sound).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck.sound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck.sound` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The terminating include/omit recurrence checks every compatible extension, including empty and nonmaximal classes. The proof establishes soundness for arbitrary element types, original predicates and bounded candidate lists. The full126-minimum instance supplies all actual data and uses the resulting class property in the written graph obstruction.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck.sound`
- Dependency: [D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound](WeightedIndependentBound.md)
