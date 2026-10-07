# RotationAvoidanceAscendingOutside

## Abstract

The nonextreme ascending endpoint case forces separated decreasing blocks around an increasing middle pair.

**Theorem 1.1 (Ascending nonextreme endpoint normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside.ascending_nonextreme_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside.ascending_nonextreme_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with first, end with last, and have an interior list. If its first entry is positive, first is less than last, at least one endpoint lies away from the extreme values, and exactly the uncut rotation contains 1234, then first plus two is less than last. The interior is a decreasing block of values below first, followed by a decreasing block of values above last, with the remaining values split into decreasing lists before and after those blocks. Some value in the first remaining list is smaller than some value in the second.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside.ascending_nonextreme_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
