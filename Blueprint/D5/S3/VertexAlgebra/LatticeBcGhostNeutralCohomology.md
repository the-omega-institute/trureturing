# Native neutral BRST cohomology

## Abstract

The original neutral zero-energy BRST complex has explicit native coordinates, quotient inverses, relative reduction and graded dimensions.

This unit works inside the original lattice bc-BRST model. The native neutral zero-energy basis has the vacuum v, the c0 state u, one matter oscillator j(axis), its c0 partner k(axis), and the two ghost states z and w. The state space remains the full algebraic State D; E0 is defined as the intersection of the exact charge-zero submodule with the kernel of M D H 0 + G D 0.

The coordinate construction requires both actual matrix equations H*gramComplex D=1 and gramComplex D*H=1. Those equations are used for the L0 basis diagonalization, native spanning and Q action, full-image restriction, and all-energy homotopy. The differential nilpotence theorem and the absolute/full-neutral quotient equivalences, gradings and dimensions additionally carry D.rank=26. The relative equivalence, grading and dimensions require both inverse equations but no rank-26 premise. Native label enumeration and the direct J0 and B0 actions require neither inverse equation nor rank 26; z_absolute_exact likewise holds for arbitrary H without either inverse or a critical-rank premise.

Under both Gram inverse equations, Q sends u to -2 z and sends v, every j(axis), every k(axis), z and w to zero. The resulting differential is transported from the original Q, not substituted for it. Absolute cohomology quotients all E0 cycles by the pullback of the full original Q range, allowing full State preimages. Relative cohomology independently restricts to RelativeSpace=E0 intersect ker B0, then takes cycles and boundaries of relativeDifferential, the original Q restricted to that space. Relative boundaries use preimages in RelativeSpace, not arbitrary absolute preimages or a quotient by B0 images.

**Definition 1.1 (Six native neutral basis families).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.NativeIndex`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.NativeIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeIndex is the finite family v,u,j,k,z,w, with j and k indexed by Fin(rank). It is an index type for the derived basis, not a restriction of the original state space.

**Definition 1.2 (Neutral zero-energy submodule).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E0 is Support.neutral intersected with the kernel of the actual zero-mode operator M D H 0 + G D 0. Its definition carries no positivity or cutoff premise; the inverse-Gram conditions enter the theorems that identify its basis.

**Theorem 1.3 (Native labels exhaust the zero-energy labels).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeLabel_range`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeLabel_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of nativeLabel is exactly Support.zeroLabels. Thus the six native families, with their Fin(rank) multiplicities, cover the complete neutral zero-energy basis described by the support module.

**Definition 1.4 (Actual native basis of E0).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeBasis`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nativeBasis is obtained from the coordinate equivalence and has native D index. The basis theorem is valid under both Gram inverse equations and preserves the actual vectors vacuumState, uState, jState, kState, zState and wState.

**Theorem 1.5 (Original Q on every native vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.Q_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.Q_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, with no rank-26 premise, the exact native action is u ↦ -2 z and every other native family ↦ 0. This is a theorem about the original Q D H on actual State vectors, not a replacement abstract differential.

**Theorem 1.6 (Native differential squares to zero).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.differential_square_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.differential_square_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transported differential on E0 squares to zero under the two Gram inverse equations and the explicit critical-rank premise D.rank=26. The proof consumes the existing LatticeBcGhostBrstNilpotence.nilpotent result for the unchanged original Q.

**Theorem 1.7 (Cycle condition in native coordinates).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.cycle_iff_u_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.cycle_iff_u_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, for a state already in E0, Q-closedness is equivalent to its u-coordinate being zero. No rank-26 premise is needed. This converts the original Q-cycle condition into a coordinate statement only after the native basis and Q transport have been proved.

**Theorem 1.8 (Full State image inside E0).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0_full_image_iff_z`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0_full_image_iff_z` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, for a state already in E0, membership in the full original range of Q is equivalent to being a scalar multiple of z, with no rank-26 premise. The result uses the target-membership hypothesis of the full-image restriction theorem from the support unit and the native Q action; it is not a global range equality or merely a finite-dimensional matrix calculation.

**Definition 1.9 (Absolute quotient coordinates and inverse).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, absoluteEquiv identifies the quotient of all E0 cycles by the original Q boundaries with AbsoluteCoordinates D=ℂ × (Fin D.rank → ℂ) × (Fin D.rank → ℂ) × ℂ. The surviving coordinates are v, all j(axis), all k(axis), and w. absoluteEmbed sets the u and z coordinates to zero: u is excluded by closedness, and z is absolute-exact rather than a surviving absolute coordinate. The inverse is the explicit absoluteQuotientRepresentative map, with both inverse laws proved using the full-image boundary characterization.

**Theorem 1.10 (Absolute representative reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, absoluteEquiv_inverse identifies the inverse of absoluteEquiv with the quotient class of absoluteRepresentCycle. The mutual inverse laws belong to absoluteEquiv and use the readout kernel and quotient induction; this theorem gives the explicit inverse formula, not a dimension-only assertion.

**Theorem 1.11 (Absolute representatives are uniquely determined).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.representatives_full_image_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.representatives_full_image_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, the difference of two absoluteRepresentative states lies in the full range of Q exactly when their AbsoluteCoordinates are equal. Separately, absoluteToOriginal_injective states that absoluteToOriginal : AbsoluteCohomology D H → OriginalCohomology D H is injective for arbitrary H, without inverse-Gram or rank-26 premises. It proves injection only, not surjectivity or an equivalence with all OriginalCohomology; charged cohomology is not covered.

**Theorem 1.12 (Actual J0 ghost grading on native vectors).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.J_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.J_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J0, the existing LatticeBcGhostBrstGhostNumber.J D operator, acts on v,u,j(axis),k(axis),z,w with ghostDegree values 0,1,1,2,2,3 respectively. This direct native-vector calculation requires neither Gram inverse equations nor rank 26. The grading is an actual operator calculation on State, not an external ghost-number convention imposed after quotienting.

**Theorem 1.13 (Actual B0 ghost differential on native vectors).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B0 sends u to v, k(axis) to j(axis), w to -z, and v,j,z to zero, without Gram inverse or rank-26 premises. This direct native action is the independent relative input; it is not inferred from the absolute Q differential.

**Theorem 1.14 (Relative ker B0 coordinate condition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, within E0 the B0-kernel is characterized by vanishing u, every k(axis), and w coordinates, with no rank-26 premise. This describes the restriction to RelativeSpace before taking the relative Q quotient, not the removal of B0-exact states.

**Theorem 1.15 (Q vanishes on the relative space).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_Q_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_Q_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two Gram inverse equations, with no rank-26 premise, Q is zero on RelativeSpace=E0 intersect ker B0. Hence relativeDifferential_zero and relative_boundaries_bot give zero relative Q boundaries: preimages must themselves belong to RelativeSpace. This is independent of the absolute quotient, where arbitrary full State preimages are allowed.

**Definition 1.16 (Relative quotient coordinates and inverse).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, with no rank-26 premise, relativeEquiv identifies the independently constructed relative cohomology with RelativeCoordinates D=ℂ × (Fin D.rank → ℂ) × ℂ, with coordinates v, all j(axis), and z. relativeEmbed sets u, every k(axis), and w to zero. The quotient uses the relative Q image with RelativeSpace preimages, which is zero; the readout and representative maps are explicitly inverse by relative reconstruction. In particular, z survives here despite being absolute-exact.

**Theorem 1.17 (z is exact in the full original State image).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_absolute_exact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_absolute_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and arbitrary H, zState is in the full range of Q, with preimage -uState/2. This statement has no Gram inverse or critical-rank premise because it uses the direct c0 vacuum action.

**Theorem 1.18 (z is nonexact in the independent relative space).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_relative_nonexact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_relative_nonexact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, with no rank-26 premise, no preimage in RelativeSpace maps under the original Q to zState. The absolute preimage -uState/2 is not a relative preimage because B0 sends uState to v. Thus z is exact in the full State image but survives the independently defined relative restriction and relative Q quotient.

**Definition 1.19 (All-energy neutral quotient coordinates).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.fullNeutralEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.fullNeutralEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, fullNeutralEquiv identifies FullNeutralCohomology, the quotient of all neutral Q-cycles by the pullback of the full original Q range, with AbsoluteCoordinates v,j,k,w. It is assembled from the all-energy projection P0, the zero-energy absolute representative, and the exact inclusion/reconstruction maps. Neutral cycles here may have any energy; the result is not an equivalence with all-charge OriginalCohomology.

**Theorem 1.20 (Charge-energy projection assembly).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.charge_energy_projection_assembly`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.charge_energy_projection_assembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

charge_energy_projection_assembly states (neutralChargeProjection D).comp(Energy.P0 D)=Image.jointProjection D. This coordinate projection identity depends only on D, not H, either Gram inverse equation or rank 26. The separate neutralChargeProjection_commutes_Q theorem holds for arbitrary H. Energy commutation and homotopy require both inverse equations, and fullNeutralEquiv additionally requires D.rank=26; the projection identity alone is not a full cohomology equivalence.

**Theorem 1.21 (Absolute J0 grading).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_J`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, the absolute quotient coordinate equivalence intertwines the actual J0 operator with absoluteWeight, whose v,j,k,w weights are 0,1,2,3. This makes the absolute ghost-degree decomposition a derived operator statement, not an assumed decomposition.

**Theorem 1.22 (Relative J0 grading).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv_J`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, with no rank-26 premise, the relative quotient equivalence intertwines J0 with relativeWeight, whose v,j,z weights are 0,1,2. The relative construction first restricts to E0 intersect ker B0, then quotients by the relative Q image with independent RelativeSpace preimages. It does not quotient by B0 images or import absolute boundaries.

**Theorem 1.23 (Absolute total dimension and separate graded dimensions).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, absolute_finrank states the total dimension Module.finrank ℂ (AbsoluteCohomology D H)=2*D.rank+2. Separately, absolute_ghost_0_finrank, absolute_ghost_1_finrank, absolute_ghost_2_finrank and absolute_ghost_3_finrank state that AbsoluteGrade at degrees 0,1,2,3 has dimensions 1,D.rank,D.rank,1 respectively, under those same hypotheses. These individual grade results use the corresponding absoluteGhostZeroEquiv, absoluteGhostOneEquiv, absoluteGhostTwoEquiv and absoluteGhostThreeEquiv; the total-dimension handle is not itself a graded-dimension theorem or a physical BRST spectrum claim.

**Theorem 1.24 (Relative total dimension and separate graded dimensions).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, with no rank-26 premise, relative_finrank states the total dimension Module.finrank ℂ (RelativeCohomology D H hHG hGH)=D.rank+2. Separately, relative_ghost_0_finrank, relative_ghost_1_finrank and relative_ghost_2_finrank give dimensions 1,D.rank,1 for RelativeGrade at degrees 0,1,2, under the same inverse equations and without rank 26. These use relativeGhostZeroEquiv, relativeGhostOneEquiv and relativeGhostTwoEquiv for the independent relative quotient; neither its total dimension nor its individual grades are obtained by informally deleting absolute components.

**Theorem 1.25 (Finite dimension of the full neutral cohomology).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.full_neutral_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.full_neutral_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, full_neutral_finrank gives the total dimension Module.finrank ℂ (FullNeutralCohomology D H)=2*D.rank+2. The all-energy neutral quotient has the same total dimension as AbsoluteCoordinates because the homotopy contracts nonzero-energy contributions. This is not a dimension result for all OriginalCohomology or for a charged-sector quotient.

**Theorem 1.26 (Original Q image lies in original cycles).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.original_image_in_cycles`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.original_image_in_cycles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With both Gram inverse equations and D.rank=26, the full original Q image lies in the original cycle submodule because the existing nilpotence theorem gives Q squared zero. This is the precise critical-rank condition used when identifying the unprojected original quotient.

**Theorem 1.27 (Absolute grade support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_grade_outside`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_grade_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations and D.rank=26, absolute_grade_outside makes AbsoluteGrade zero for each integer degree unequal to 0,1,2,3. Separately, relative_grade_outside makes RelativeGrade zero for each degree unequal to 0,1,2 under both inverse equations, without a rank-26 premise. These are coordinate-support conclusions for the respective formal quotients, not physical no-ghost or string-spectrum claims.

Reuse and attribution: the source imports the existing lattice carrier, Sugawara, bc-Fock, BRST charge, nilpotence, ghost-number and quotient APIs. The native matrix laws and all quotient maps are proved against the unchanged original State and Q. The Scribe records the derived assumptions and dimensions so that inverse-Gram, zero-energy and critical-rank hypotheses are not conflated.

Formal boundary: the packet establishes a neutral formal-model cohomology reduction and its absolute/relative graded dimensions. It does not close charged-sector cohomology, a physical no-ghost theorem, analytic or unitary completion, the full VOA/CFT/string construction, or an AdS/CFT correspondence. Those remain active open goals.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_kernel_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.B_native`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.E0_full_image_iff_z`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.J_native`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.NativeIndex`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.Q_native`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_J`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absoluteEquiv_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.absolute_grade_outside`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.charge_energy_projection_assembly`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.cycle_iff_u_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.differential_square_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.fullNeutralEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.full_neutral_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeBasis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.nativeLabel_range`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.original_image_in_cycles`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relativeEquiv_J`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_Q_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.relative_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.representatives_full_image_injective`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_absolute_exact`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology.z_relative_nonexact`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber](LatticeBcGhostBrstGhostNumber.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix](LatticeBcGhostBrstNeutralMatrix.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence](LatticeBcGhostBrstNilpotence.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport](LatticeBcGhostNeutralCohomologySupport.md)
