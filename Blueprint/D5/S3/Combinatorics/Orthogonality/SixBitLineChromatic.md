# The full weighted inequality and the original twelve-color witness

## Abstract

The independent six-dimensional line graph result.

**Theorem 1.1 (Complete weighted check).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Kernel reduction evaluates the complete include-or-omit recursion on all63 nonzero masks, using weight3 for even and4 for odd. The checked value19 supplies the numerical premise of the general soundness theorem; no sampled subsets or encoded answer premise are used.

**Theorem 1.2 (Every independent set).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weighted_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weighted_bound` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every finite subset avoiding zero and having nonzero dot product on every distinct pair has total weight at most19. This is exactly the full source independent-set domain.

**Theorem 1.3 (Parity and extremal size).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.independence_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.independence_profile` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

With t even and o odd members,3t+4o<=19 and size<=6. A size-six class has exactly five even and one odd member. A second complete restricted check bounds any all-even independent set by five.

**Theorem 1.4 (Every coloring needs twelve colors).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.coloring_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.coloring_lower_bound` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The31 nonzero even and32 odd vectors have total weight221. Every actual color fiber has weight at most19, and an exact finite fiber sum gives221<=19k for every k-coloring. Hence k>=12.

**Theorem 1.5 (The exact line chromatic number).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The original twelve literal classes define a coloring of all63 nonzero masks, checked on every distinct orthogonality pair. Combined with the universal weighted lower bound, the actual six-bit line graph has chromatic number12. A separate full coordinate/Submodule representation bridge remains necessary for target transport; the theorem does not establish the all-subspace answer15 or any n7 upper bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.coloring_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.independence_profile`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.result`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weighted_bound`
- Dependency: [D5/S3/Combinatorics/Orthogonality/SixBitCatalogue](SixBitCatalogue.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound](WeightedIndependentBound.md)
