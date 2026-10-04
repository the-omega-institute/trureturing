# RotationAvoidanceOneAscent

## Abstract

Permutations with one ascent split into decreasing parts and supply a lower bound for a classical avoidance class.

**Theorem 1.1 (Count of one-ascent permutations).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every size, the permutations of one through size that are not wholly decreasing but split at some cut into two decreasing lists number 2 to the size minus size minus one. Every such permutation avoids 123 and 3412.

**Theorem 1.2 (One-ascent lower bound).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.ascending_one_ascent_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.ascending_one_ascent_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every size, 2 to the size minus size minus one is at most one less than the number of permutations avoiding 123 and 3412. For size at least four, the inequality is strict.

**Theorem 1.3 (Paired endpoint color order).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation have first and last entries and suppose exactly the uncut rotation contains 2143. Then first is less than last. The entries below first in the interior are increasing, the entries above last in the interior are increasing, and the interior contains an increasing pair whose first value is below first and whose second value is above last.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.ascending_one_ascent_gap`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration](RotationAvoidanceEnumeration.md)
