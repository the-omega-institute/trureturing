# Original absolute zero-momentum BRST cohomology and native ghost grades

## Abstract

Original absolute zero-momentum BRST cohomology and native ghost grades

Let D be arbitrary LatticeData, including rank zero. H is indexed by Fin D.rank and satisfies H * gramComplex D = 1 and gramComplex D * H = 1. These are the only matrix hypotheses. Every operator below is the original tensor operator. No rank 26, signature, positivity, frame or nonzero momentum hypothesis occurs.

The absolute sector E0 is literally fixedMomentum D 0 intersect ker(totalL0 D H), where totalL0 is the original unshifted matter-plus-ghost zero mode. No b0 condition is imposed on E0. The original zero-mode CAR give x = b0 c0 x + c0 b0 x on all states. Pure ghost operators preserve the original charge support, and the original L0 commutes with b0 and c0. Consequently both b0 c0 x and b0 x lie in the full original relative zero-momentum shell whenever x lies in E0.

The supplier shellEquiv is applied only after this exhaustive original-state splitting. Its inverse Psi(A,v,C) is the original ground tensor empty occupation, the original frequency-zero currents tensor occupation {1}, and the original ground tensor occupation {1,5}, with the indicated coefficients. Thus every absolute state uniquely has the form Psi z + c0(Psi w). This equivalence is proved from the actual constraints, rather than assumed as the definition of the complex.

The actual finite ghost calculation uses the supplier all-integer R sum and its proved odd-occupation annihilation tail. At r=0 only p=-1,0,1 remain on these occupations. Both nonzero-index terms give plus ket {1,5} on the empty occupation; the zero term is zero. R0 therefore sends Psi(A,v,C) to Psi(0,0,2*A), and annihilates the other two branches. The actual Ward identity {Q,c0}=R0 and the original relative-shell Q=0 then give Q(Psi z+c0 Psi w)=Psi(0,0,2*w.A).

Q0 is defined by restricting the original totalCharge to E0, after proving preservation. Its square is zero at every rank because the computed original image lies in the original relative shell and Q vanishes there. This restricted statement makes no assertion about ambient noncritical Q squared.

Cycles are the actual kernel of Q0. In the unique split coordinates the cycle condition is w.A=0. The actual original image consists exactly of z.A=z.v=0 and w=0. A state with only z.C nonzero has the genuine boundary primitive c0 Psi(z.C/2,0,0). Boundaries are the actual range of the incoming Q0 map into its actual kernel. The first isomorphism theorem applies to the proved boundary/kernel equality for the class map, yielding Complex x ((Complex^rank) x ((Complex^rank) x Complex)). Canonical original representatives set z.C=w.A=0.

Native ghost number is exactly LatticeMatterGhostDegree.tensorNumber, relative to the original SL2 vacuum of grade zero. The actual c0 raises it by one. On a split state the six coordinate blocks have degrees 0,1,2,1,2,3. Homogeneous cycles are the actual Q0 kernel intersected with the actual number eigenspace at each integer q. Incoming boundaries are images of actual Q0 from the eigenspace of degree q-1, rather than an assigned coordinate differential or an intersection with an ungraded image.

The reverse graded boundary/kernel inclusion constructs the same primitive with w.A=z.C/2 and proves that it is homogeneous of degree q-1 from the original number equations. The quotient therefore has original canonical homogeneous representatives. In grades 0,1,2,3 it is linearly equivalent to Complex, Complex^rank, Complex^rank, Complex respectively. Every other integer grade is zero. The finrank formula is derived from these quotient equivalences and includes rank zero without a separate assumption.

The shell and finite-tail identities come from LatticeZeroMomentumBRST; the zero-mode CAR and projectors come from LatticeBRSTRelativeZeroMode. LatticeBRSTWard and LatticeMatterGhostDegree supply the original Ward and number identities. Their definitions and proofs retain their authorship. Mathlib supplies quotient, eigenspace and dimension machinery under Apache 2.0. This algebraic computation establishes neither an ambient signed pairing nor positivity or signature.

**Theorem 1.1 (bc_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.bc_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.bc_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine all-state CAR splitting, before imposing either charge or energy.

**Theorem 1.2 (ghost_preserves_fixedMomentum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ghost_preserves_fixedMomentum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ghost_preserves_fixedMomentum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ghost endomorphism preserves every original charge, with no mode cutoff. The proof uses the original tensor coefficient slices.

**Definition 1.3 (Absolute).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Absolute`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Absolute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Kernel of the actual original unshifted total L0.

**Definition 1.4 (E0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.E0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.E0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The absolute sector has no b0 constraint.

**Definition 1.5 (split0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.split0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.split0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Charge-preserving CAR splitting of the whole literal absolute shell.

**Definition 1.6 (stateEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.stateEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.stateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates are extracted AFTER exhaustive splitting in the actual shell.

**Theorem 1.7 (mem_E0_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.mem_E0_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.mem_E0_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustion of ALL original charge-zero absolute zero-energy states.

**Theorem 1.8 (M_Psi).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.M_Psi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.M_Psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact original zero-momentum M coefficient: +2 from the native unshifted rTerm convention. This proves a nontrivial map from coordinate 0 to coordinate 2, and cannot be replaced by M=0 or an automatic doubling argument.

**Theorem 1.9 (Q_representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only nonzero matrix entry is the actual M coefficient +2.

**Theorem 1.10 (Q_mem_E0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_mem_E0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_mem_E0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Q preserves the exact original fixed-charge absolute space.

**Definition 1.11 (Q0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal restriction of original Q; its definition does not prescribe a coordinate differential.

**Theorem 1.12 (Q0_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration Q0_coordinates is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.13 (Q0_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricted square-zero at every rank, from the computed original image and the actual zero action on the original relative shell.

**Definition 1.14 (Cycles).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cycles`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration Cycles is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.15 (cycle_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycle_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycle_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration cycle_coordinates is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.16 (range_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.range_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.range_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual range on actual E0; the unique surviving exact coordinate is z.c.

**Definition 1.17 (boundaryMap).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaryMap`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaryMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual incoming Q with codomain its actual kernel.

**Definition 1.18 (Boundaries).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Boundaries`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Boundaries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual range of Q0 with codomain its kernel.

**Definition 1.19 (Cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cohomology`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cohomology` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ORIGINAL state kernel/range quotient.

**Definition 1.20 (ClassCoordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Four retained ORIGINAL class coordinates, in the requested order.

**Definition 1.21 (classCoordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear map on actual cycles retains z.A, z.v, w.v and w.C.

**Definition 1.22 (representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.representative`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Canonical cycles are ORIGINAL states with z.c=w.a=0.

**Theorem 1.23 (coordinates_representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.coordinates_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.coordinates_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration coordinates_representative is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.24 (classCoordinates_surjective).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration classCoordinates_surjective is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.25 (boundaries_eq_ker).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaries_eq_ker`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaries_eq_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the load-bearing quotient calculation: actual Q-images are exactly the kernel of the FOUR-COORDINATE class map on actual Q-cycles.

**Definition 1.26 (cohomologyEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's first isomorphism theorem, applied to the proved actual kernel/image equality. No new generic cohomology/quotient framework.

**Theorem 1.27 (cohomologyEquiv_mk).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration cohomologyEquiv_mk is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.28 (classOf).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration classOf is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.29 (cohomologyEquiv_classOf).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_classOf`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_classOf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration cohomologyEquiv_classOf is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.30 (classOf_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every class has the stated canonical representative, with an actual Q preimage for the removed z.c already given in range_coordinates.

**Theorem 1.31 (number_Q).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual Q raises native ghost number on ALL original states. This consumes the committed all-integer finite-capture proof, rather than a grade premise.

**Theorem 1.32 (number_c0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_c0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_c0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All-state c0 degree +1, obtained from the committed all-integer relation.

**Theorem 1.33 (number_representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration number_representative is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.34 (number_mem_E0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_mem_E0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_mem_E0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration number_mem_E0 is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.35 (N0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction of the native number operator to the actual E0.

**Theorem 1.36 (N0_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration N0_coordinates is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.37 (Grade).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Grade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Grade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual homogeneous ORIGINAL states, over every integer ghost degree.

**Theorem 1.38 (grade_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.grade_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.grade_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native grading on ALL E0 states. The two scalars with degree two are z.c (exact) and w.v; w.a has degree one and is excluded by cycles.

**Theorem 1.39 (Q0_grade).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Incoming Q raises the ACTUAL native number eigenvalue by one. This proof uses the committed all-state number/Q relation, with no mode restriction.

**Definition 1.40 (GradedCycles).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCycles`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal original cycles intersected with a native homogeneous subspace.

**Definition 1.41 (gradedBoundaryMap).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaryMap`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaryMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q on the actual incoming eigenspace, with codomain the actual homogeneous cycle space. All-rank restricted square-zero supplies the cycle condition.

**Definition 1.42 (GradedBoundaries).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedBoundaries`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedBoundaries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The range of actual Q0 from incoming native number eigenspace of degree q-1.

**Definition 1.43 (GradedCohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCohomology`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCohomology` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No assigned dimensions: genuine native homogeneous kernel/image quotient.

**Definition 1.44 (canonicalState).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.canonicalState`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.canonicalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration canonicalState is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.45 (ClassGrade).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassGrade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate target grading is PULLED BACK from the native operator on the original canonical representatives. It is not an assumed grading certificate.

**Theorem 1.46 (classGrade_coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGrade_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGrade_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration classGrade_coordinates is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.47 (gradedCoordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration gradedCoordinates is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.48 (gradedRepresentative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedRepresentative`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration gradedRepresentative is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.49 (gradedCoordinates_representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration gradedCoordinates_representative is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.50 (gradedCoordinates_surjective).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source declaration gradedCoordinates_surjective is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.51 (gradedBoundaries_eq_ker).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaries_eq_ker`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaries_eq_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original graded Q-image, not merely intersection with an ungraded image, equals the coordinate kernel. Reverse inclusion constructs a genuine incoming state of native degree q-1 with w.a=z.c/2.

**Definition 1.52 (gradedCohomologyEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCohomologyEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCohomologyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Degreewise quotient transport uses Mathlib directly on the actual homogeneous original kernel and incoming Q-image.

**Definition 1.53 (classGradeZeroEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeZeroEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeZeroEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native degree zero has the ground scalar class.

**Definition 1.54 (classGradeOneEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeOneEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeOneEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native degree one has z.v; the scalar w.a is removed by the actual cycle condition, rather than being silently counted as a second copy.

**Definition 1.55 (classGradeTwoEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeTwoEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeTwoEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native degree two has w.v; z.c is exactly the actual Q-image.

**Definition 1.56 (classGradeThreeEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeThreeEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeThreeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native degree three has w.c.

**Definition 1.57 (H0Equiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H0Equiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H0Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration H0Equiv is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.58 (H1Equiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H1Equiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H1Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration H1Equiv is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.59 (H2Equiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H2Equiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H2Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration H2Equiv is part of the actual original kernel/image construction with the displayed source type.

**Definition 1.60 (H3Equiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H3Equiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H3Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source declaration H3Equiv is part of the actual original kernel/image construction with the displayed source type.

**Theorem 1.61 (other_grade_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.other_grade_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.other_grade_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every other integer degree, including negative degrees, is zero.

**Theorem 1.62 (native_dimensions).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_dimensions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_dimensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native dimensions are consequences of the explicit ORIGINAL quotient equivalences; they are not assumptions or certificates.

**Definition 1.63 (e0_addCommGroup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.e0_addCommGroup`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.e0_addCommGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine original absolute sector inherits the canonical additive group of its ambient tensor carrier, with explicit scalar and ambient types for native instance resolution.

**Definition 1.64 (cycles_addCommGroup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycles_addCommGroup`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycles_addCommGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual original Q0 kernel inherits the canonical submodule additive group; this is consumed by its original-image quotient.

**Definition 1.65 (gradedCycles_addCommGroup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCycles_addCommGroup`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCycles_addCommGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each actual homogeneous original cycle subspace inherits its canonical additive group, consumed by the incoming-image quotient.

**Theorem 1.66 (native_finrank).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire integer grading, including arbitrary rank zero, is derived from the original homogeneous kernel and incoming-image quotients.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Boundaries`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ClassGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cohomology`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Cycles`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.E0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedBoundaries`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCohomology`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.GradedCycles`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H0Equiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H1Equiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H2Equiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.H3Equiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.M_Psi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.N0_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q0_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_mem_E0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.Q_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.bc_split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaries_eq_ker`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.boundaryMap`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.canonicalState`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classCoordinates_surjective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeOneEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeThreeEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeTwoEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGradeZeroEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classGrade_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.classOf_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_classOf`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cohomologyEquiv_mk`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.coordinates_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycle_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.cycles_addCommGroup`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.e0_addCommGroup`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.ghost_preserves_fixedMomentum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.grade_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaries_eq_ker`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedBoundaryMap`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCohomologyEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCoordinates_surjective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedCycles_addCommGroup`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.gradedRepresentative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.mem_E0_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_dimensions`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.native_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_c0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_mem_E0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.number_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.other_grade_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.range_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.split0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology.stateEquiv`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode](LatticeBRSTRelativeZeroMode.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST](LatticeZeroMomentumBRST.md)
