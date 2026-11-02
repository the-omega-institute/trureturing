# Original quartet preservation of relative constraints

## Abstract

LatticeQuartetEnergyPreservation

The carrier is the original all-integral-charge lattice Fock space tensor the original algebraic bc Fock space. Let E be exactly matterMode D H 0 + ghostVirasoro D 0, the unshifted totalL0. Both matrix equations H gramComplex D = 1 and gramComplex D H = 1 are assumed. For an arbitrary null frame, d0 is the accepted pPlus-scaled locally finite signed current sum, R uses its original inverse scalar, M is the original quartet count, and h = R invM uses the reciprocal of that count on the actual original basis, zero on count zero. The fixed sector p and the operator parameter q are independent original integral charges. No nonzero momentum, nonzero pPlus, rank 26, Lorentzian signature or positivity hypothesis is used.

The energy commutator splits on pure original tensors into a matter commutator and a ghost commutator. The accepted Sugawara current Ward relation extends linearly to a(u,n); its weight -n cancels the original c(-n) weight +n in dm. For rr the a(ePlus,-n) weight +n cancels the b(n) weight -n. These identities hold for every signed integer n, including zero. The actual locally finite frequency families therefore commute with E; the original scalar factors give commutation with d0 and R, even at pPlus = 0. The unscaled contraction, which has no nonzero-momentum hypothesis, then gives commutation with M. Its proved actual-basis spectrum transfers commutation to invM through the accepted number-operator functional calculus. This proves the unshifted energy identity for h without assuming the desired preservation statement.

Charge projection and M are diagonal in the same actual basis, so inverse-count functional calculus makes invM commute with the original fixed-charge projection. Combining this with the accepted charge law for R proves the charge law for h. The accepted actual b0 anticommutators for d0 and h give preservation of ker b0. Evaluating these operator identities on an arbitrary vector proves preservation of the literal simultaneous fixed-charge, b0-kernel and unshifted-totalL0-kernel constraints. No finite cutoff, changed shell, shifted intercept, completion or surrogate differential is used. The d0 conclusion requires no choice of transverse basis; the h conclusion retains its defining actual transverse basis.

**Theorem 1.1 (d0 preserves the original relative constraints).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice D, null frame F, inverse-Gram matrix H satisfying both inverse equations, original charges p and q, and original vector x with chargeProject p x = x, ghostB0 x = 0 and E x = 0, the actual d0 F q x satisfies the same three equalities.

**Theorem 1.2 (h preserves the original relative constraints).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice D, null frame F, finite basis B of its transverse space, inverse-Gram matrix H satisfying both inverse equations, original charges p and q, and original vector x with chargeProject p x = x, ghostB0 x = 0 and E x = 0, the actual h F B q x satisfies the same three equalities. This remains valid at q = 0 and pPlus q = 0 because the original inverse scalar is defined there.

These are original-carrier algebraic consequences of the accepted Ward, finite-support and quartet suppliers, without a claim of literature novelty. Source-audit registration remains unfinished for both public targets; their missing exact-source selection and reconstruction obligations are disclosed at https://github.com/the-omega-institute/trureturing/issues/25847, with related supplier limitations in issue 25604. A source bridge or successful mathematical compilation is not declared_validated audit evidence. This unit supplies only preservation by d0 and h. Original full-Q shell stability, HPL transfer, cohomology, Hermitian descent, no-ghost positivity and the remaining supplier obligations are separate. It does not complete Monster moonshine, VOA/CFT, anomaly/fusion, original BRST/string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](LatticeQuartetContraction.md)
