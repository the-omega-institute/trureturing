# The original-carrier iterate families

## Abstract

Finite iterate expansion and the V tower for the actual Zhu associator.

For homogeneous original states u and v of nonnegative energies K and L, and every original state w, the native all-state iterate identity expands star(star(u,v),w) into USide minus VSide. Finite support from state-field regularity justifies the separation and reindexing of the two mode families.

The V family is regrouped by its outer mode. The signed V binomial kernel and ActualZhuMuIdentity.mu_identity identify its negative with the finite Vfam tower. Each term is a scalar multiple of a higherCircle of the original field; under positive-definiteness of the real Gram matrix, Ufam and Vfam belong to the literal ActualZhuFinite.zhuO. These private definitions and lemmas are consumed by ActualZhuAssociator, which completes the U-family calculation and proves membership of the associator for arbitrary original states. No smaller carrier, replacement O-space, assumed stability, or assumed associativity enters this argument.

This is a source-faithful native port of the finite iterate expansion and V-family regrouping in Fedor K. Popov's Apache-2.0 VOA/Modules/ZhuAssociator.lean at https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuAssociator.lean. The immutable upstream SHA256 is 733725cca0c4ac72112b440392242d853378e35a7db197e80e5518d2591f468f. The port uses the repository's original lattice fields and native Ring.choose. Upstream uses Lean v4.30.0 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the native port uses Lean v4.35.0 and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The argument is literature-attested Zhu/Frenkel--Zhu mathematics; these consumed helpers make no claim of independent mathematical novelty.

The public associator's four-slot escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/28745. These private helpers supply no declared_validated registration, quotient algebra, analytic CFT, string-theory model, or AdS/CFT correspondence.

## References

- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuAssociatorScalar](ActualZhuAssociatorScalar.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity](ActualZhuMuIdentity.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal](ActualZhuRightIdeal.md)
