# Original prime-cube lattice

## Abstract

The literal middle letters define an index-c congruence lattice. A shortest vector extends by Bezout to an oriented basis; centering the second vector gives bounded integer coordinates for every point in the original endpoint box. Dyadic scales supply the J1,J2 scale relations and the actual endpoint coefficient and pencil-height bounds. This is the long-chart lattice bridge, not the original six-tuple count.

For unit w modulo c, the physical endpoint lattice consists of (u,z) with w z - t u divisible by c. The anchor (-w,-t) belongs to this lattice and to the same literal box as the endpoints. The metric and reduction estimates assume c>0, X>0 and Y>0. The chosen metric has squared norm (Y/X)u^2+(X/Y)z^2 and determinant one; no fixed input unit is absorbed into an interval.

The proof takes a minimum in the finite weighted ball containing (c,0). The shortest vector is primitive in the explicit congruence basis, so Bezout completes it to an oriented determinant-c basis. An integer shift centers the second vector. The determinant identity gives 3 Q(R)^2 <= 4 c^2 and Q(R)Q(V) <= 2 c^2. Determinant bounds then place every literal endpoint and the anchor within the stated CoordinateBound rectangle.

Take H>0 with H^2=XY and s0>0. The long-chart condition is c^2<H^2 Q(R), and a dyadic s0 satisfies s0^2 <= Q(R) < 4 s0^2. With H^2=XY, J1=8H/s0 and J2=4Hs0/c satisfy J2<=J1, J2>2, J1 J2=32XY/c, J1<16XY/c and J2<5 sqrt(XY/c). These scales realize the original endpoint coefficient constant 3 and pencil height 18. The theorem does not infer that the shortest vector has unit coordinates; that is a separate chart condition required by later residue formulas.

**Definition 1.1 (Physical congruence lattice).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleLattice`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleLattice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Literal integer pairs satisfying w z - t u = 0 modulo c.

**Definition 1.2 (Oriented integer basis).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.MiddleBasis`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.MiddleBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

An oriented determinant-c basis with integer decomposition of every physical lattice point.

**Definition 1.3 (Explicit unit-slope basis).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleBasis_of_unit`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleBasis_of_unit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

A unit w modulo c supplies the kernel basis (1,k),(0,c), where k=t/w modulo c.

**Theorem 1.4 (Weighted determinant identity).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.weighted_det_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.weighted_det_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The area-preserving anisotropic metric satisfies Q(z)Q(z')-dot(z,z')^2=det(z,z')^2.

**Theorem 1.5 (Shortest physical vector).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_shortest_middle_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_shortest_middle_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

A finite weighted ball gives a shortest nonzero vector in the actual congruence lattice.

**Theorem 1.6 (Reduced oriented basis exists).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_reduced_middle_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_reduced_middle_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The shortest vector is primitive in the kernel basis; Bezout completion and an integer centering shift give a reduced oriented basis.

**Theorem 1.7 (Reduced basis constants).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.reduction_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.reduction_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Shortestness and centering imply 3 Q(R)^2 <= 4 c^2, Q(R)<2c and Q(V)Q(R)<=2c^2.

**Theorem 1.8 (Literal endpoint coordinate bound).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.coordinate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Each point in the original X by Y box has integral reduced coordinates bounded by J1 and J2.

**Theorem 1.9 (Long-chart scale relations).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.long_scale_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.long_scale_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The long condition and dyadic reduced length imply J2<=J1, J2>2, J1 J2=32XY/c, J1<16XY/c and J2<5 sqrt(XY/c).

**Theorem 1.10 (Dyadic reduced-length scale).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_dyadic_middle_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_dyadic_middle_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

A positive squared length has a power-of-two scale s0 with s0^2<=A<4s0^2.

**Theorem 1.11 (Actual coefficient and height inputs).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.actual_endpoint_inputs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.actual_endpoint_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Literal box membership for the anchor, baseline and endpoint supplies factor-cover scale order, endpoint coefficients with C=3, and actual pencil height H=18.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.MiddleBasis`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.actual_endpoint_inputs`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.coordinate_bound`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_dyadic_middle_scale`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_reduced_middle_basis`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_shortest_middle_vector`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.long_scale_bounds`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleBasis_of_unit`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleLattice`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.reduction_bounds`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalLattice.weighted_det_identity`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients](PascadiOriginalCoefficients.md)
