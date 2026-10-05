# RotationAvoidanceOneAscent

## Abstract

One-ascent enumeration and interval order constrain unique containing rotations.

**Theorem 1.1 (Enumeration and avoidance of one-ascent permutations).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every nonnegative size, the permutations of one through size that are not decreasing but can be split into two decreasing lists number 2^size minus size minus one. Every such permutation avoids 123 and 3412. Thus these are exactly the permutations with one ascent, counted by choosing the entries of their first decreasing block and excluding the decreasing concatenations.

**Theorem 1.2 (Order of lower and upper endpoint intervals).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let size be at least four. If a permutation begins with first, ends with last, and contains 2143 in exactly the uncut rotation, then first is less than last. The interior entries below first form an increasing list, and those above last form an increasing list. Some interior entry below first precedes an interior entry above last.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.one_ascent_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent.paired_endpoint_color_order`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration](RotationAvoidanceEnumeration.md)
