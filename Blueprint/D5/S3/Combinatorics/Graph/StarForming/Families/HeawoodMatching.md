# A parametric matching in binary Heawood lifts

## Abstract

The same induced matching gives two independent improvements to the Heawood lift bound.

**Definition 1.1 (Gain coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary u, v, a, b and c in F2, the matrix rows in binary Fano coordinates are (v, a, b), (0, 0, c) and (1+v, u, v). The flag signs on (4,1), (4,2), (5,5), (1,2), (1,4) and (2,4) are respectively 1, u, v, a, b+v and c. All other signs are zero.

**Theorem 1.2 (Dissociation bounds for conjugate gains).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be any signing and let g be an invertible binary matrix. For any u, v, a, b and c in F2, suppose Phi(s) = g gain(u,v,a,b,c) g⁻¹. Then beta(graph(s),2) is at least fourteen plus one if u=0 and one if u+v=1, and beta(graph(s),2) is at most sixteen.

Select point lifts 2_0, 2_1, 3_0, 3_1, 4_0, 5_(1+u), 6_1 and 7_0. The six fixed line lifts 1_0, 2_u, 2_(1+u), 3_1, 6_1 and 6_0 have unique selected neighbors 2_0, 4_0, 5_(1+u), 3_1, 6_1 and 7_0 respectively.

When u=0, line lift 7_0 has 3_0 as its unique selected neighbor. When u+v=1, line lift 5_1 has 2_1 as its unique selected neighbor. The flag signs involving a, b and c do not affect these neighbor relations. Each selected line has a distinct selected point as its neighbor, so the selected graph has maximum degree one. Its order is fourteen plus one for each of the two conditions. HeawoodMatrixAction.isomorphic_of_phi_conjugate transports this bound to the original lift, where SF=16 also gives beta at most sixteen.

The Fano flag coordinates, binary sheet rule and gain conjugacy are from the subquorum-colorings contributors under Apache-2.0. The conjugacy step uses the existing formalization in HeawoodMatrixAction. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L26-L66

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.beta_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.gain`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatrixAction](HeawoodMatrixAction.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters](../HeawoodCoverParameters.md)
