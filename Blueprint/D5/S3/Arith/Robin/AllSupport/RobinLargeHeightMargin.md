# A quantitative Robin margin at large logarithmic height

## Abstract

The all-support Robin estimate gives a uniform quantitative margin under RH.

**Theorem 1.1 (Uniform normalized Robin margin above height 74500).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.normalized_robinLogMargin_large_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.normalized_robinLogMargin_large_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH, let H = log n be at least 74500. The log Robin margin times sqrt(H) log(H) strictly exceeds 17/500. The weighted prime cost contributes at least 2264003/1000000, and the adverse signed theta tail costs strictly less than 223/100. The remaining terms in the all-support identity are nonnegative.

**Theorem 1.2 (The original Robin inequality under RH).**

Lean statement: `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.original_robin_of_rh_all_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.original_robin_of_rh_all_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite certificates cover n greater than 5040 through log height 74500. The quantitative margin covers every larger height.

## References

- Truth anchor: `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.normalized_robinLogMargin_large_gt`
- Truth anchor: `D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.original_robin_of_rh_all_support`
- Dependency: [D5/S3/Arith/Robin/Finite/OriginalRobinThrough74500](../Finite/OriginalRobinThrough74500.md)
