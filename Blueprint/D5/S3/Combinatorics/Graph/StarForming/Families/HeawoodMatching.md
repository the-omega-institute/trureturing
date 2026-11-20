# A parametric matching in binary Heawood lifts

## Abstract

The same induced matching gives two independent improvements to the Heawood lift bound.

**Definition 1.1 (Gain coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

In the binary Fano coordinates the matrix rows are (v, a, b), (0, 0, c) and (1+v, u, v). The flag signs on (4,1), (4,2), (5,5), (1,2), (1,4) and (2,4) are respectively 1, u, v, a, b+v and c. All other signs are zero.

**Theorem 1.2 (Dissociation bounds for conjugate gains).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Select point lifts 2_0, 2_1, 3_0, 3_1, 4_0, 5_(1+u), 6_1 and 7_0. The six fixed line lifts 1_0, 2_u, 2_(1+u), 3_1, 6_1 and 6_0 have unique selected neighbors 2_0, 4_0, 5_(1+u), 3_1, 6_1 and 7_0 respectively.

When u=0, line lift 7_0 has 3_0 as its unique selected neighbor. When u+v=1, line lift 5_1 has 2_1 as its unique selected neighbor. The flag signs involving a, b and c do not affect these neighbor relations. Each selected line has a distinct selected point as its neighbor, so the selected graph has maximum degree one. Its order is fourteen plus one for each of the two conditions. Gain conjugacy transports this bound to the original lift, where SF=16 also gives beta at most sixteen.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatrixAction](HeawoodMatrixAction.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters](../HeawoodCoverParameters.md)
