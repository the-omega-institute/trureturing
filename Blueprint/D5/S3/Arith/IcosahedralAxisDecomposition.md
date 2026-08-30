# Finite Icosahedral Axis Decomposition

## Abstract

The 31 points of P2(F5) split into the 6, 10, and 15 icosahedral axis classes.

**Theorem 1.1 (The finite projective plane has 31 points).**

$$\operatorname{card}(Projectivization) = 31 \land \operatorname{card}(FiniteProjectivePlane) = 31.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_plane_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalized representatives are proved equivalent to Mathlib's quotient projectivization. Both presentations therefore have 31 points.

**Theorem 1.2 (The three quadratic classes form a disjoint partition).**

$$\operatorname{union}(\operatorname{union}(P_{5}, P_{3}), P_{2}) = FiniteProjectivePlane \land pairwiseDisjoint(P_{5}, P_{3}, P_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_axis_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero, nonsquare, and square quadratic-value classes cover every projective point and are pairwise disjoint.

**Theorem 1.3 (The three projective classes have sizes 6, 10, and 15).**

$$\operatorname{card}(P_{5}) = 6 \land \operatorname{card}(P_{3}) = 10 \land \operatorname{card}(P_{2}) = 15.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_axis_cardinalities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact finite evaluation of the displayed quadratic matrix gives six isotropic, ten nonsquare, and fifteen square directions.

**Theorem 1.4 (The cyclic axes form three conjugacy orbits).**

$$\operatorname{card}(A_{5}) = 6 \land \operatorname{card}(A_{3}) = 10 \land \operatorname{card}(A_{2}) = 15 \land eachClassIsOneConjugacyOrbit.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.icosahedral_axis_orbits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical cyclic generators in A5 give single conjugacy classes at orders five, three, and two, with sizes six, ten, and fifteen.

**Theorem 1.5 (The axis stabilizers have orders 10, 6, and 4).**

$$\operatorname{card}(Normalizer5) = 10 \land \operatorname{card}(Normalizer3) = 6 \land \operatorname{card}(Normalizer2) = 4 \land Normalizer2 = Centralizer2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.icosahedral_axis_stabilizer_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic-axis normalizers have the stated orders. For every twofold axis, its normalizer equals the generator centralizer.

**Theorem 1.6 (The projective classes biject with the cyclic-axis orbits).**

$$P_{5} \sim A_{5} \land P_{3} \sim A_{3} \land P_{2} \sim A_{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.finite_icosahedral_axis_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each quadratic class is in finite bijection with the corresponding A5 axis orbit. The equivalences are noncanonical cardinality matches; no real-geometric or equivariant map is asserted.

**Theorem 1.7 (The degenerate order parameters are explicit).**

$$\operatorname{card}(A_{0}) = 59 \land \operatorname{card}(A_{1}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisDecomposition.cyclic_axes_degenerate_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter zero all 59 nonidentity elements pass the generator test; at parameter one none do. This records the degenerate inputs.

## References

- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.cyclic_axes_degenerate_orders`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.finite_icosahedral_axis_decomposition`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_axis_cardinalities`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_axis_partition`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.finite_projective_plane_cardinality`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.icosahedral_axis_orbits`
- Truth anchor: `D5/S3/Arith/IcosahedralAxisDecomposition.icosahedral_axis_stabilizer_orders`
