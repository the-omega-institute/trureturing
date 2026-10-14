# Framed on-shell relative ghost-degree-one classes

## Abstract

The actual C0 pairing descends in both slots on the literal physical original-Q image.

Fix an arbitrary LatticeData D and H with H*gram=gram*H=1. Fix beta, an integer level, frame and inverse with both inverse-frame equations, rank 26, a null direction, nonzero chosenP, distinct x/y axes, the x row equal to the null direction and the y row equal to adaptedPartner. Retain both dual-row equations against every frame row and the shell equation chosenH(beta)+level-1=0. The physical cycles are exactly the original Q-cycles in this actual charge/energy sector, annihilated by B D 0 and in actual integer ghost degree one. No positivity, real longitudinal rows, occupation cutoff or alternate carrier is imposed.

physicalBoundaries is the actual OriginalBoundaries comap along the inclusion of physicalCycles into OriginalCycles. Thus PhysicalCohomology identifies precisely states with the same literal original absolute class; it does not impose a smaller relation. inclusion is induced by the actual OriginalBoundaries.mkQ. physicalImage is its range, proved equal to the image of physicalCycles under that same mkQ. imageEquiv identifies the subquotient with this literal subspace of OriginalCohomology.

**Theorem 1.1 (Simultaneous two-slot representative independence).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.representative_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.representative_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any four physical relative degree-one cycles in the same framed on-shell sector whose original classes agree pairwise, F(first,C0 third)=F(second,C0 fourth). The existing literal_physical_equality_iff_relative_preimage produces relative degree-zero sector preimages of both differences. The actual left and right obstruction laws vanish on those repaired preimages, establishing both changes of representatives simultaneously.

**Theorem 1.2 (The actual boundary comap annihilates both form slots).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physical_boundary_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physical_boundary_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the actual OriginalBoundaries begins with an unrestricted State preimage. relative_ambient_boundary_homotopy_preimage supplies the same explicit native finite-HPL preimage carrying relativity, ghost degree zero, charge and energy; applying the actual tensor boundary theorem kills both inserted pairings. No unrestricted relative-to-absolute injection is assumed. The existing neutral absolute-exact but relative-nonexact zState is outside the nonzero chosenP scope and remains unchanged.

**Theorem 1.3 (Faithful inclusion of the physical subquotient).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel of the restricted actual class map is precisely physicalBoundaries, so its quotient inclusion is injective. This is a first-isomorphism statement for an actual boundary comap, not a claim that every relative boundary relation equals the ambient one in all sectors.

**Theorem 1.4 (The inclusion uses the literal original class).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each physical cycle the quotient inclusion is exactly its OriginalBoundaries.mkQ class.

**Theorem 1.5 (The carrier is the literal physical image).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physicalImage_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physicalImage_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of inclusion equals the actual original class map applied to the full physical cycle submodule.

**Theorem 1.6 (Exact representative recovery on the physical subquotient).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

quotientForm is constructed by the two actual Submodule.liftQ operations, using the established two-slot boundary vanishing. It is conjugate-linear on the left and linear on the right, and on quotient representatives equals the original F(left,C D 0 right), without rescaling or changing the rotation phase.

**Theorem 1.7 (Exact representative recovery on the literal image).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

imageForm transports the constructed quotientForm through the proved canonical imageEquiv. On the literal original classes of physical representatives it returns their actual inserted C0 pairing.

**Theorem 1.8 (Hermitian symmetry from actual odd ghost parity).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing integral ghost-degree/parity result makes every degree-one physical representative odd for the actual Pi. Its minus sign cancels the negative C0 transpose in F_C, proving quotientForm(left,right)=star(quotientForm(right,left)). No reality hypothesis on frame rows is used.

**Theorem 1.9 (Hermitian form on the literal physical image).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact image form inherits Hermitian symmetry from the physical quotient. Descent and symmetry do not prove positivity, a radical calculation, an isometry, a no-ghost theorem, or complete moonshine, string theory or AdS/CFT realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.imageForm_recovery`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_injective`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.inclusion_mk`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physicalImage_eq`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.physical_boundary_vanishing`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.quotientForm_mk`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.representative_independent`
- Dependency: [D5/S3/VertexAlgebra/OriginalQRelativeAmbientPreimage](../OriginalQRelativeAmbientPreimage.md)
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm](TensorRelativeForm.md)
