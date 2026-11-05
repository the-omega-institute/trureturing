/- GID: D5/S3/FiniteGroups/CliffordConstituents
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CliffordConstituents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: CliffordConstituents. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top
Conjugates of a simple restricted constituent span the irreducible representation and account for every simple constituent.
MonoidAlgebra.conjNormalAlgAut | proof_shape: bind-only | escape_witness: none | consumer: Representation.asModuleConjEquiv_smul, Representation.conjHom, Representation.conjSubrepMap_smul
MonoidAlgebra.conjNormalAlgAut_single | proof_shape: bind-only | escape_witness: none | consumer: Representation.asModuleConjEquiv_smul
TauCeti.mem_conj_smul | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mem_mackeySubgroup_iff, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf
TauCeti.conj_mul_smul | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_conj
TauCeti.coe_conjSubgroupEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeyToH_apply
TauCeti.Representation.apply_conjNormal_inv | proof_shape: bind-only | escape_witness: none | consumer: Representation.asModuleConjEquiv_smul, TauCeti.Representation.conjSubrep, TauCeti.Representation.conjSubrepEquiv
TauCeti.conjNormal_inv_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepFunctor_one
TauCeti.conjNormal_inv_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepFunctor_mul
TauCeti.conjNormalFDRepFunctor | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.char_conjNormalFDRep, TauCeti.char_conjNormalFDRep_mk, TauCeti.char_conj_eq_of_mem_inertia, TauCeti.conjNormalFDRepFunctor_mul, TauCeti.conjNormalFDRepFunctor_one, TauCeti.conjNormalFDRepIso, TauCeti.conjNormalFDRepSkeletonMulAction, TauCeti.conjNormalFDRepSkeletonSMul, TauCeti.conjNormalFDRep_mul, TauCeti.conjNormalFDRep_one, TauCeti.le_inertia, TauCeti.mem_inertia_iff, TauCeti.smul_toSkeleton, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.finrank_cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.Representation.toSkeleton_fdRepOf_conjSubrep, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.restrictLinearEquivPi, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_of_normal, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_of_normal, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff
TauCeti.conjNormalFDRepFunctor_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRep_one
TauCeti.conjNormalFDRepFunctor_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRep_mul
TauCeti.conjNormalFDRep_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepSkeletonMulAction
TauCeti.conjNormalFDRep_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepSkeletonMulAction
TauCeti.conjNormalFDRepEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepEquiv_functor, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal
TauCeti.conjNormalFDRepEquiv_functor | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal
TauCeti.conjNormalFDRepIso | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.le_inertia
TauCeti.conjNormalFDRepSkeletonSMul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepSkeletonMulAction, TauCeti.mem_inertia_iff, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap_surjective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentsEquivOrbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentsEquivOrbit_apply, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.toSkeleton_fdRepOf_conjSubrep
TauCeti.smul_toSkeleton | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRepSkeletonMulAction, TauCeti.mem_inertia_iff, D5.S3.FiniteGroups.CliffordDecomposition.Representation.toSkeleton_fdRepOf_conjSubrep
TauCeti.conjNormalFDRepSkeletonMulAction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.char_conj_eq_of_mem_inertia, TauCeti.le_inertia, TauCeti.mem_inertia_iff, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.finrank_cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_symm_mk, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.finite_quotient_inertia, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.restrictLinearEquivPi, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.inertia_eq_of_fixedPointFree, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial, D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank
TauCeti.char_conjNormalFDRep | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.char_conjNormalFDRep_mk, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial
TauCeti.char_conjNormalFDRep_mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.char_conj_eq_of_mem_inertia
TauCeti.Representation.conjSubrep | proof_shape: bind-only | escape_witness: none | consumer: Representation.coe_conjSubrepIsotypicComponent, Representation.conjSubrepIsotypicComponent, Representation.exists_forall_finrank_linearMap_eq, Representation.finrank_linearMap_conjSubrep, Representation.finrank_linearMap_eq_of_isAtom, TauCeti.Representation.conjSubrepEquiv, TauCeti.Representation.conjSubrepOrderIso, TauCeti.Representation.conjSubrep_conjSubrep, TauCeti.Representation.conjSubrep_eq_self_of_mem, TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep, TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep, TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top, TauCeti.Representation.iSup_conjSubrep_eq_top, TauCeti.Representation.isAtom_conjSubrep_iff, TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom, TauCeti.Representation.isotypicComponents_eq_range, TauCeti.Representation.mem_conjSubrep_iff, TauCeti.Representation.toSubmodule_conjSubrep, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.toSkeleton_fdRepOf_conjSubrep, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.Representation.toSubmodule_conjSubrep | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.conjSubrepOrderIso, TauCeti.Representation.conjSubrep_conjSubrep, TauCeti.Representation.conjSubrep_eq_self_of_mem, TauCeti.Representation.iSup_conjSubrep_eq_top
TauCeti.Representation.mem_conjSubrep_iff | proof_shape: bind-only | escape_witness: none | consumer: Representation.finrank_linearMap_conjSubrep
TauCeti.Representation.conjSubrep_eq_self_of_mem | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.conjSubrep_one
TauCeti.Representation.conjSubrep_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.conjSubrepOrderIso
TauCeti.Representation.conjSubrep_conjSubrep | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.conjSubrepOrderIso, TauCeti.Representation.iSup_conjSubrep_eq_top
TauCeti.Representation.conjSubrepOrderIso | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.conjSubrepOrderIso_apply, TauCeti.Representation.isAtom_conjSubrep_iff
TauCeti.Representation.conjSubrepOrderIso_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.isAtom_conjSubrep_iff
TauCeti.Representation.isAtom_conjSubrep_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep, TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom, TauCeti.Representation.isotypicComponents_eq_range, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.Representation.conjSubrepEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep
TauCeti.Representation.iSup_conjSubrep_eq_top | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top
TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep, TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom
TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: TauCeti.Representation.isSemisimpleRepresentation_comp_subtype
TauCeti.Representation.isSemisimpleRepresentation_comp_subtype | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.restrictLinearEquivPi
TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: Representation.finrank_linearMap_eq_of_isAtom, TauCeti.Representation.exists_nonempty_linearEquiv_conjSubrep, TauCeti.Representation.isotypicComponents_eq_range, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit
TauCeti.Representation.exists_nonempty_linearEquiv_conjSubrep | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep
TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: Representation.exists_forall_finrank_linearMap_eq, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso
TauCeti.Representation.isotypicComponents_eq_range | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: Representation.conjSubrepIsotypicComponent
Representation.conjSubrepIsotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap_surjective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_symm_mk, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
Representation.coe_conjSubrepIsotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.le_isotypicComponent_iff_nonempty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simpleSubmoduleClassesEquiv
TauCeti.SimpleSubmoduleClasses | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.SimpleSubmoduleClasses.ind, TauCeti.SimpleSubmoduleClasses.lift, TauCeti.simpleSubmoduleClassesEquiv, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk
TauCeti.SimpleSubmoduleClasses.mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.SimpleSubmoduleClasses.ind, TauCeti.SimpleSubmoduleClasses.lift_mk, TauCeti.simpleSubmoduleClassesEquiv, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk
TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simpleSubmoduleClassesEquiv, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective
TauCeti.SimpleSubmoduleClasses.ind | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simpleSubmoduleClassesEquiv, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit
TauCeti.SimpleSubmoduleClasses.lift | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.SimpleSubmoduleClasses.lift_mk, TauCeti.simpleSubmoduleClassesEquiv, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk
TauCeti.SimpleSubmoduleClasses.lift_mk | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk
TauCeti.simpleSubmoduleClassesEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_mem_orbit
TauCeti.finrank_linearMap_pi_eq_natCard | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi
TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const
TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.nonempty_linearEquiv_isotypicComponent
TauCeti.isotypicComponent_self_eq_top | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.apply_mem_isotypicComponent
TauCeti.apply_mem_isotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.linearMapIsotypicComponentEquiv
TauCeti.linearMapIsotypicComponentEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_linearMap_isotypicComponent
TauCeti.finrank_linearMap_isotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.nonempty_linearEquiv_isotypicComponent
TauCeti.nonempty_linearEquiv_isotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.finrank_linearMap_pos_of_ne_bot | proof_shape: bind-only | escape_witness: none | consumer: Representation.finrank_linearMap_pos
Representation.asModuleConjEquiv | proof_shape: bind-only | escape_witness: none | consumer: Representation.asModuleConjEquiv_apply, Representation.asModuleConjEquiv_smul, Representation.conjHom, Representation.conjHomEquiv, Representation.conjHomₗ, Representation.conjSubrepMap, Representation.conjSubrepMap_add, Representation.conjSubrepMap_smul
Representation.asModuleConjEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.asModuleConjEquiv_smul
Representation.asModuleConjEquiv_smul | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHom, Representation.conjSubrepMap_smul
Representation.conjSubrepMap | proof_shape: bind-only | escape_witness: none | consumer: Representation.coe_conjSubrepMap, Representation.conjHom, Representation.conjHomEquiv, Representation.conjHomₗ, Representation.conjSubrepMap_add, Representation.conjSubrepMap_inv_self_apply, Representation.conjSubrepMap_self_inv_apply, Representation.conjSubrepMap_smul
Representation.coe_conjSubrepMap | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjSubrepMap_add, Representation.conjSubrepMap_smul
Representation.conjSubrepMap_add | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHom
Representation.conjSubrepMap_smul | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHom
Representation.conjSubrepMap_inv_self_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv
Representation.conjSubrepMap_self_inv_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv
Representation.conjHom | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv, Representation.conjHom_apply, Representation.conjHomₗ
Representation.conjHom_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv, Representation.conjHomₗ
Representation.conjHomₗ | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv, Representation.conjHomₗ_apply
Representation.conjHomₗ_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.conjHomEquiv
Representation.conjHomEquiv | proof_shape: bind-only | escape_witness: none | consumer: Representation.finrank_linearMap_conjSubrep
Representation.finrank_linearMap_conjSubrep | proof_shape: bind-only | escape_witness: none | consumer: Representation.finrank_linearMap_eq_of_isAtom
Representation.finrank_linearMap_eq_of_isAtom | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: Representation.finrank_linearMap_eq_of_isAtom_of_isAtom
Representation.finrank_linearMap_eq_of_isAtom_of_isAtom | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: Representation.exists_forall_finrank_linearMap_eq
Representation.finrank_linearMap_pos | proof_shape: bind-only | escape_witness: none | consumer: Representation.exists_forall_finrank_linearMap_eq
Representation.exists_forall_finrank_linearMap_eq | proof_shape: content | escape_witness: TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom
TauCeti.Representation.equivOfAsModuleLinearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.nonempty_equiv_iff, TauCeti.fdRepIsoOfAsModuleLinearEquiv, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom
TauCeti.Representation.asModuleLinearEquivOfEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.nonempty_equiv_iff, TauCeti.nonempty_fdRepIso_iff, D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.Representation.nonempty_equiv_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff
TauCeti.fdRepIsoOfAsModuleLinearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.nonempty_fdRepIso_iff, D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep
TauCeti.nonempty_fdRepIso_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit, D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk
TauCeti.mem_inertia_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.char_conj_eq_of_mem_inertia, TauCeti.le_inertia
TauCeti.le_inertia | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.inertia_eq_of_fixedPointFree
TauCeti.char_conj_eq_of_mem_inertia | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.inertia_eq_of_fixedPointFree
-/

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Isotypic
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace D5.S3.FiniteGroups.CliffordConstituents
namespace MonoidAlgebra
end MonoidAlgebra
namespace Representation
end Representation
namespace TauCeti
end TauCeti
namespace TauCeti.Representation
end TauCeti.Representation
namespace TauCeti.SimpleSubmoduleClasses
end TauCeti.SimpleSubmoduleClasses
section UpstreamSource3_2
open scoped _root_.MonoidAlgebra
namespace MonoidAlgebra
open _root_.MonoidAlgebra
variable (k : Type*) {G : Type*} [CommSemiring k] [Group G] (N : Subgroup G) [N.Normal]
private noncomputable def conjNormalAlgAut : G →* (k[N] ≃ₐ[k] k[N]) :=
  (domCongrAut (R := k) (A := k) (M := N)).comp MulAut.conjNormal
variable {k N}
@[simp]
private theorem conjNormalAlgAut_single (g : G) (n : N) (a : k) :
    conjNormalAlgAut k N g (single n a) = single (MulAut.conjNormal g n) a :=
  domCongr_single _ _ _
end MonoidAlgebra
end UpstreamSource3_2
section UpstreamSource3_3
open scoped Pointwise
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
variable {G : Type*} [Group G]
@[simp]
theorem mem_conj_smul (s : G) (H : Subgroup G) (x : G) :
    x ∈ (MulAut.conj s • H : Subgroup G) ↔ s⁻¹ * x * s ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp
theorem conj_mul_smul (s t : G) (H : Subgroup G) :
    MulAut.conj (s * t) • H = MulAut.conj s • (MulAut.conj t • H) := by
  rw [map_mul, mul_smul]
end TauCeti
end UpstreamSource3_3
section UpstreamSource3_4
open CategoryTheory
open scoped Pointwise
universe u v w
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
variable {k : Type u} {G : Type v} [Group G]
@[simp]
theorem coe_conjSubgroupEquiv_apply (s : G) (H : Subgroup G)
    (x : (MulAut.conj s • H : Subgroup G)) : ((Subgroup.equivSMul (MulAut.conj s) H).symm x : G) = s⁻¹ * (x : G) * s := by
  rfl
section Normal
variable {N : Subgroup G} [hN : N.Normal]
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
variable [Semiring k] [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
private theorem apply_conjNormal_inv (g : G) (n : N) (v : V) :
    ρ g (ρ (MulAut.conjNormal g⁻¹ n : G) v) = ρ (n : G) (ρ g v) := by
  have hg : g * (MulAut.conjNormal g⁻¹ n : G) = (n : G) * g := by
    rw [MulAut.conjNormal_apply]
    group
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]
end Representation
private theorem conjNormal_inv_one :
    (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = MonoidHom.id N :=
  MonoidHom.ext fun x => Subtype.ext (by simp)
private theorem conjNormal_inv_mul (s t : G) :
    (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom =
      (MulAut.conjNormal (t⁻¹) : MulAut N).toMonoidHom.comp
        (MulAut.conjNormal (s⁻¹) : MulAut N).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by
    simp only [MulAut.conjNormal_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    group)
section NormalFDRep
variable [Ring k]
def conjNormalFDRepFunctor (g : G) : FDRep k N ⥤ FDRep k N :=
  Action.res (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom
private theorem conjNormalFDRepFunctor_one :
    conjNormalFDRepFunctor (k := k) (N := N) (1 : G) = 𝟭 (FDRep k N) := by
  change Action.res (FGModuleCat k) (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_one]
  rfl
private theorem conjNormalFDRepFunctor_mul (s t : G) :
    conjNormalFDRepFunctor (k := k) (N := N) (s * t) =
      conjNormalFDRepFunctor t ⋙ conjNormalFDRepFunctor s := by
  change Action.res (FGModuleCat k) (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_mul, actionRes_comp]
  rfl
@[simp]
private theorem conjNormalFDRep_one (A : FDRep k N) : (conjNormalFDRepFunctor (1 : G)).obj A = A :=
  Functor.congr_obj conjNormalFDRepFunctor_one A
@[simp]
private theorem conjNormalFDRep_mul (s t : G) (A : FDRep k N) :
    (conjNormalFDRepFunctor (s * t)).obj A = (conjNormalFDRepFunctor s).obj ((conjNormalFDRepFunctor t).obj A) :=
  Functor.congr_obj (conjNormalFDRepFunctor_mul s t) A
def conjNormalFDRepEquiv (g : G) : FDRep k N ≌ FDRep k N :=
  Action.resEquiv (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N)
@[simp]
theorem conjNormalFDRepEquiv_functor (g : G) :
    (conjNormalFDRepEquiv (k := k) (N := N) g).functor = conjNormalFDRepFunctor g :=
  (rfl)
private def conjNormalFDRepIso (A : FDRep k N) (n : N) : (conjNormalFDRepFunctor (n : G)).obj A ≅ A :=
  Action.mkIso (A.ρAut n).asIso fun x => by
    change (Action.ρ A _).asHom ≫ (Action.ρ A _).asHom =
      (Action.ρ A _).asHom ≫ (Action.ρ A _).asHom
    rw [← End.mul_asHom, ← End.mul_asHom, ← map_mul, ← map_mul]
    exact congrArg (fun n => (Action.ρ A n).asHom) (Subtype.ext (by simp [mul_assoc]))
noncomputable instance conjNormalFDRepSkeletonSMul : SMul G (Skeleton (FDRep k N)) where
  smul g := (conjNormalFDRepFunctor g).mapSkeleton.obj
@[simp]
theorem smul_toSkeleton (g : G) (A : FDRep k N) :
    g • toSkeleton A = toSkeleton ((conjNormalFDRepFunctor g).obj A) :=
  (conjNormalFDRepFunctor g).mapSkeleton_obj_toSkeleton A
noncomputable instance conjNormalFDRepSkeletonMulAction : MulAction G (Skeleton (FDRep k N)) where
  one_smul X := by
    obtain ⟨A, rfl⟩ : ∃ A, toSkeleton A = X := ⟨_, toSkeleton_fromSkeleton_obj X⟩
    rw [smul_toSkeleton, conjNormalFDRep_one]
  mul_smul s t X := by
    obtain ⟨A, rfl⟩ : ∃ A, toSkeleton A = X := ⟨_, toSkeleton_fromSkeleton_obj X⟩
    rw [smul_toSkeleton, smul_toSkeleton, smul_toSkeleton, conjNormalFDRep_mul]
end NormalFDRep
section NormalCharacter
variable [Field k]
@[simp]
theorem char_conjNormalFDRep (g : G) (A : FDRep k N) (x : N) :
    ((conjNormalFDRepFunctor g).obj A).character x = A.character (MulAut.conjNormal g⁻¹ x) :=
  rfl
private theorem char_conjNormalFDRep_mk (g : G) (A : FDRep k N) (x : N) :
    ((conjNormalFDRepFunctor g).obj A).character x =
      A.character ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ := by
  rw [char_conjNormalFDRep]
  congr 1
  exact Subtype.ext (by simp)
end NormalCharacter
end Normal
end TauCeti
end UpstreamSource3_4
section UpstreamSource4_0
open scoped _root_.MonoidAlgebra
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
section Translate
variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
def conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Subrepresentation (ρ.comp N.subtype) where
  toSubmodule := σ.toSubmodule.map (ρ g)
  apply_mem_toSubmodule := by
    rintro n _ ⟨v, hv, rfl⟩
    exact ⟨_, σ.apply_mem_toSubmodule (MulAut.conjNormal g⁻¹ n) hv,
      apply_conjNormal_inv ρ g n v⟩
variable {ρ}
@[simp]
private theorem toSubmodule_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    (conjSubrep ρ g σ).toSubmodule = σ.toSubmodule.map (ρ g) :=
  (rfl)
@[simp]
private theorem mem_conjSubrep_iff {g : G} {σ : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ conjSubrep ρ g σ ↔ ρ g⁻¹ v ∈ σ := by
  refine ⟨?_, fun h => ⟨_, h, _root_.Representation.self_inv_apply ρ g v⟩⟩
  rintro ⟨u, hu, rfl⟩
  rwa [_root_.Representation.inv_self_apply]
@[simp]
private theorem conjSubrep_eq_self_of_mem {g : G} (hg : g ∈ N)
    (σ : Subrepresentation (ρ.comp N.subtype)) : conjSubrep ρ g σ = σ := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · rw [toSubmodule_conjSubrep]
    rintro _ ⟨v, hv, rfl⟩
    simpa using σ.apply_mem_toSubmodule ⟨g, hg⟩ hv
  · intro v hv
    rw [toSubmodule_conjSubrep]
    exact ⟨ρ g⁻¹ v, by simpa using σ.apply_mem_toSubmodule ⟨g⁻¹, inv_mem hg⟩ hv,
      _root_.Representation.self_inv_apply ρ g v⟩
private theorem conjSubrep_one (σ : Subrepresentation (ρ.comp N.subtype)) : conjSubrep ρ 1 σ = σ :=
  conjSubrep_eq_self_of_mem (one_mem N) σ
@[simp]
private theorem conjSubrep_conjSubrep (g h : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubrep ρ g (conjSubrep ρ h σ) = conjSubrep ρ (g * h) σ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [toSubmodule_conjSubrep, toSubmodule_conjSubrep, toSubmodule_conjSubrep,
      ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
variable (ρ) in
private def conjSubrepOrderIso (g : G) :
    Subrepresentation (ρ.comp N.subtype) ≃o Subrepresentation (ρ.comp N.subtype) where
  toFun := conjSubrep ρ g
  invFun := conjSubrep ρ g⁻¹
  left_inv σ := by rw [conjSubrep_conjSubrep, inv_mul_cancel, conjSubrep_one]
  right_inv σ := by rw [conjSubrep_conjSubrep, mul_inv_cancel, conjSubrep_one]
  map_rel_iff' {σ τ} := by
    change (conjSubrep ρ g σ).toSubmodule ≤ (conjSubrep ρ g τ).toSubmodule ↔
      σ.toSubmodule ≤ τ.toSubmodule
    simp only [toSubmodule_conjSubrep]
    exact Submodule.map_le_map_iff_of_injective
      (_root_.Representation.apply_bijective ρ g).injective _ _
@[simp]
private theorem conjSubrepOrderIso_apply (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubrepOrderIso ρ g σ = conjSubrep ρ g σ :=
  (rfl)
@[simp]
theorem isAtom_conjSubrep_iff {g : G} {σ : Subrepresentation (ρ.comp N.subtype)} :
    IsAtom (conjSubrep ρ g σ) ↔ IsAtom σ := by
  rw [← conjSubrepOrderIso_apply g σ]
  exact (conjSubrepOrderIso ρ g).isAtom_iff σ
variable (ρ) in
noncomputable def conjSubrepEquiv (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    _root_.Representation.Equiv
      (σ.toRepresentation.comp ((MulAut.conjNormal g⁻¹ : MulAut N) : N →* N))
      (conjSubrep ρ g σ).toRepresentation :=
  _root_.Representation.Equiv.mk
    (σ.toSubmodule.equivMapOfInjective (ρ g) (_root_.Representation.apply_bijective ρ g).injective)
    (fun n => by
      ext u
      exact apply_conjNormal_inv ρ g n u)
end Translate
section Clifford
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
private theorem iSup_conjSubrep_eq_top [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    ⨆ g : G, (conjSubrep ρ g σ).toSubmodule = ⊤ := by
  have hmap : ∀ h : G, (⨆ g : G, (conjSubrep ρ g σ).toSubmodule).map (ρ h)
      ≤ ⨆ g : G, (conjSubrep ρ g σ).toSubmodule := by
    intro h
    rw [Submodule.map_iSup]
    refine iSup_le fun g => ?_
    rw [← toSubmodule_conjSubrep h (conjSubrep ρ g σ), conjSubrep_conjSubrep]
    exact le_iSup (fun g : G => (conjSubrep ρ g σ).toSubmodule) (h * g)
  let τ : Subrepresentation ρ :=
    { toSubmodule := ⨆ g : G, (conjSubrep ρ g σ).toSubmodule
      apply_mem_toSubmodule := fun h v hv => hmap h ⟨v, hv, rfl⟩ }
  have hτσ : σ.toSubmodule ≤ τ.toSubmodule := by
    refine le_iSup_of_le 1 ?_
    rw [toSubmodule_conjSubrep, map_one, Module.End.one_eq_id, Submodule.map_id]
  rcases IsSimpleOrder.eq_bot_or_eq_top τ with h | h
  · refine absurd (Subrepresentation.toSubmodule_injective ?_) hσ
    have hbot : τ.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot]
    exact le_bot_iff.mp (hbot ▸ hτσ)
  · exact congrArg Subrepresentation.toSubmodule h
private theorem iSup_asSubmodule_conjSubrep_eq_top [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    ⨆ g : G, (conjSubrep ρ g σ).asSubmodule = ⊤ := by
  set S : Subrepresentation (ρ.comp N.subtype) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm
      (⨆ g : G, (conjSubrep ρ g σ).asSubmodule) with hS
  have hSeq : S.asSubmodule = ⨆ g : G, (conjSubrep ρ g σ).asSubmodule := by
    rw [hS, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      OrderIso.apply_symm_apply]
  have hle : ∀ g : G, conjSubrep ρ g σ ≤ S := fun g => by
    rw [← Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply, hSeq]
    exact le_iSup (fun g : G => (conjSubrep ρ g σ).asSubmodule) g
  have htop : S = ⊤ := by
    refine Subrepresentation.toSubmodule_injective (le_antisymm le_top ?_)
    rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top, ← iSup_conjSubrep_eq_top ρ hσ]
    exact iSup_le fun g => hle g
  rw [← hSeq, htop, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    OrderIso.map_top]
private theorem isSemisimpleRepresentation_comp_subtype_of_isAtom [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  rw [_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine IsSemisimpleModule.of_sSup_simples_eq_top (eq_top_iff.mpr ?_)
  rw [← iSup_asSubmodule_conjSubrep_eq_top ρ hσ.1]
  refine iSup_le fun g => le_sSup ?_
  rw [Set.mem_ofPred_eq]
  exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
theorem isSemisimpleRepresentation_comp_subtype [ρ.IsIrreducible] [FiniteDimensional k V] :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  have : Nontrivial V := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  obtain ⟨σ, hσ⟩ := exists_isAtom (ρ.comp N.subtype)
  exact isSemisimpleRepresentation_comp_subtype_of_isAtom ρ hσ
end Clifford
end Representation
end TauCeti
end UpstreamSource4_0
section UpstreamSource4_1
open scoped _root_.MonoidAlgebra
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
section Orbit
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
theorem exists_nonempty_linearEquiv_asSubmodule_conjSubrep [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (T : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    ∃ g : G, Nonempty (T ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  have hsimple : ∀ m : (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule),
      IsSimpleModule k[N] m := by
    rintro ⟨_, g, rfl⟩
    exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
  have hsSup : sSup (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule) = ⊤ := by
    rw [sSup_range]
    exact iSup_asSubmodule_conjSubrep_eq_top ρ hσ.1
  obtain ⟨_, ⟨g, rfl⟩, he⟩ :=
    Submodule.linearEquiv_of_sSup_eq_top T _ (h := hsimple) hsSup
  exact ⟨g, he⟩
private theorem exists_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) :=
  have := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hτ
  exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ τ.asSubmodule
theorem exists_isAtom_forall_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    [FiniteDimensional k V] :
    ∃ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ ∧
      ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
        ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  have : Nontrivial V := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  obtain ⟨σ, hσ⟩ := exists_isAtom (ρ.comp N.subtype)
  exact ⟨σ, hσ, fun _ hτ => exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ⟩
private theorem isotypicComponents_eq_range [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
      = Set.range fun g : G =>
          isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
            (conjSubrep ρ g σ).asSubmodule := by
  ext c
  constructor
  · rintro ⟨S, _, rfl⟩
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ S
    exact ⟨g, e.isotypicComponent_eq.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr
      (isAtom_conjSubrep_iff.mpr hσ), rfl⟩
end Orbit
end Representation
end TauCeti
namespace Representation
open _root_.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation
section Orbit
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
noncomputable def conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponents k[N] (Representation.asModule (ρ.comp N.subtype)) :=
  ⟨isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
      (conjSubrep ρ g σ).asSubmodule,
    (isotypicComponents_eq_range ρ hσ).symm ▸ Set.mem_range_self g⟩
@[simp]
theorem coe_conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (conjSubrepIsotypicComponent ρ σ hσ g :
      Submodule k[N] (Representation.asModule (ρ.comp N.subtype))) =
      isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
        (conjSubrep ρ g σ).asSubmodule :=
  by simp only [conjSubrepIsotypicComponent]
end Orbit
end Representation
end UpstreamSource4_1
section UpstreamSource4_2
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
universe u v w
variable {R : Type u} [Ring R]
section IsotypicComponent
variable {M : Type v} [AddCommGroup M] [Module R M]
private theorem le_isotypicComponent_iff_nonempty_linearEquiv {S : Type w} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (N : Submodule R M) [IsSimpleModule R N] :
    N ≤ isotypicComponent R M S ↔ Nonempty (S ≃ₗ[R] N) :=
  ⟨fun h ↦ ⟨(isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S) N h).some.symm⟩,
    fun ⟨e⟩ ↦ le_sSup ⟨e.symm⟩⟩
variable (R M) in
def SimpleSubmoduleClasses : Type _ :=
  Quot fun N N' : {N : Submodule R M // IsSimpleModule R N} ↦ Nonempty (N.1 ≃ₗ[R] N'.1)
namespace SimpleSubmoduleClasses
def mk (N : Submodule R M) [IsSimpleModule R N] : SimpleSubmoduleClasses R M := Quot.mk _ ⟨N, ‹_›⟩
theorem mk_eq_mk_iff {N N' : Submodule R M} [IsSimpleModule R N] [IsSimpleModule R N'] :
    mk N = mk N' ↔ Nonempty (N ≃ₗ[R] N') :=
  Quot.eq.trans <| Equivalence.eqvGen_iff
    ⟨fun _ ↦ ⟨.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩
@[elab_as_elim]
theorem ind {motive : SimpleSubmoduleClasses R M → Prop}
    (mk : ∀ (N : Submodule R M) (_ : IsSimpleModule R N), motive (.mk N))
    (c : SimpleSubmoduleClasses R M) : motive c :=
  Quot.ind (fun N ↦ mk N.1 N.2) c
def lift {α : Sort*} (f : ∀ (N : Submodule R M) [IsSimpleModule R N], α)
    (hf : ∀ (N N' : Submodule R M) [IsSimpleModule R N] [IsSimpleModule R N'],
      Nonempty (N ≃ₗ[R] N') → f N = f N')
    (c : SimpleSubmoduleClasses R M) : α :=
  Quot.lift (fun N ↦ @f N.1 N.2) (fun N N' h ↦ @hf N.1 N'.1 N.2 N'.2 h) c
@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (N : Submodule R M) [IsSimpleModule R N], α} {hf}
    (N : Submodule R M) [IsSimpleModule R N] : lift f hf (mk N) = f N := (rfl)
end SimpleSubmoduleClasses
variable (R M) in
noncomputable def simpleSubmoduleClassesEquiv :
    SimpleSubmoduleClasses R M ≃ isotypicComponents R M :=
  Equiv.ofBijective
    (SimpleSubmoduleClasses.lift
      (fun N hN ↦ (⟨isotypicComponent R M N, N, hN, rfl⟩ : isotypicComponents R M))
      fun _ _ _ _ ⟨e⟩ ↦ Subtype.ext e.isotypicComponent_eq)
    ⟨by
      refine SimpleSubmoduleClasses.ind fun N _ ↦ SimpleSubmoduleClasses.ind fun N' _ ↦ fun h ↦ ?_
      rw [SimpleSubmoduleClasses.mk_eq_mk_iff]
      have h' : isotypicComponent R M N = isotypicComponent R M N' := congrArg Subtype.val h
      exact ⟨((le_isotypicComponent_iff_nonempty_linearEquiv N).mp
        (h' ▸ N.le_isotypicComponent)).some.symm⟩,
     by rintro ⟨_, N, _, rfl⟩; exact ⟨.mk N, rfl⟩⟩
variable (R M)
variable {R M}
end IsotypicComponent
end TauCeti
end UpstreamSource4_2
section UpstreamSource4_3
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
section Multiplicity
variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]
private theorem finrank_linearMap_pi_eq_natCard :
    Module.finrank k (S →ₗ[A] ∀ i, N i) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : Module.finrank k (S →ₗ[A] ∀ i, N i) = ∑ i, Module.finrank k (S →ₗ[A] N i) := by
    rw [← (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k).finrank_eq]
    exact Module.finrank_pi_fintype k
  have hval : ∀ i, Module.finrank k (S →ₗ[A] N i)
      = if Nonempty (S ≃ₗ[A] N i) then 1 else 0 := by
    intro i
    split_ifs with h
    · exact finrank_linearMap_eq_one_of_nonempty_linearEquiv h.some
    · exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)
  rw [hpi, Finset.sum_congr rfl fun i _ ↦ hval i, Finset.sum_boole, Nat.cast_id,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
private theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [← finrank_linearMap_pi_eq_natCard (k := k) (S := S) (N := N),
    ← (homCongrRight k (S := S) e).finrank_eq]
end Multiplicity
section Isotypic
variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
private theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi_const {ι : Type*} [Finite ι] {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] (ι → S)) :
    Module.finrank k (S →ₗ[A] M) = Nat.card ι := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) (N := fun _ : ι ↦ S) e]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ ⟨LinearEquiv.refl A S⟩)
end Isotypic
section IsotypicComponent
variable {k A M S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
omit [IsSimpleModule A S] in
@[simp]
private theorem isotypicComponent_self_eq_top : isotypicComponent A S S = ⊤ :=
  eq_top_iff.mpr <| (Submodule.le_isotypicComponent ⊤).trans_eq
    Submodule.topEquiv.isotypicComponent_eq
private theorem apply_mem_isotypicComponent (f : S →ₗ[A] M) (s : S) :
    f s ∈ isotypicComponent A M S := by
  have h := LinearMap.le_comap_isotypicComponent (M := S) (N := M) S f
  rw [isotypicComponent_self_eq_top] at h
  exact h Submodule.mem_top
private noncomputable def linearMapIsotypicComponentEquiv :
    (S →ₗ[A] isotypicComponent A M S) ≃ₗ[k] (S →ₗ[A] M) :=
  LinearEquiv.ofBijective (LinearMap.compRight k (isotypicComponent A M S).subtype)
    ⟨(fun _ _ h => LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x)),
      (fun f => ⟨f.codRestrict _ (apply_mem_isotypicComponent f), rfl⟩)⟩
omit [Module k S] [IsScalarTower k A S] in
@[simp]
private theorem finrank_linearMap_isotypicComponent :
    Module.finrank k (S →ₗ[A] isotypicComponent A M S) = Module.finrank k (S →ₗ[A] M) :=
  (linearMapIsotypicComponentEquiv (k := k)).finrank_eq
variable [IsAlgClosed k] [FiniteDimensional k S] [FiniteDimensional k M]
theorem nonempty_linearEquiv_isotypicComponent :
    Nonempty (isotypicComponent A M S ≃ₗ[A] (Fin (Module.finrank k (S →ₗ[A] M)) → S)) := by
  have : Module.Finite k ↥(isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  have : Module.Finite A ↥(isotypicComponent A M S) :=
    Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent A M S).linearEquiv_fun
  have hn : Module.finrank k (S →ₗ[A] M) = n := by
    rw [← finrank_linearMap_isotypicComponent (k := k),
      finrank_linearMap_eq_natCard_of_linearEquiv_pi_const (k := k) e]
    simp
  rw [hn]
  exact ⟨e⟩
end IsotypicComponent
section Positivity
variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]
private theorem finrank_linearMap_pos_of_ne_bot {S : Submodule A M} (hS : S ≠ ⊥) :
    0 < Module.finrank k (S →ₗ[A] M) := by
  have : Module.Finite k ↥S :=
    .of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hS
  have : Nontrivial (S →ₗ[A] M) :=
    ⟨S.subtype, 0, fun hzero => hv0 (by simpa using DFunLike.congr_fun hzero ⟨v, hv⟩)⟩
  exact Module.finrank_pos
end Positivity
end TauCeti
end UpstreamSource4_3
section UpstreamSource4_4
open scoped _root_.MonoidAlgebra
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
namespace Representation
open _root_.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation
open MonoidAlgebra (conjNormalAlgAut conjNormalAlgAut_single)
section Translate
variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
private noncomputable def asModuleConjEquiv (g : G) :
    _root_.Representation.asModule (ρ.comp N.subtype) ≃ₗ[k]
      _root_.Representation.asModule (ρ.comp N.subtype) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.asGroupHom g)
omit [N.Normal] in
private theorem asModuleConjEquiv_apply (g : G)
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleConjEquiv ρ (N := N) g v = ρ g v :=
  (rfl)
@[simp]
private theorem asModuleConjEquiv_smul (g : G) (a : k[N])
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleConjEquiv ρ (N := N) g (a • v)
      = conjNormalAlgAut k N g a • asModuleConjEquiv ρ (N := N) g v := by
  have hconj : ∀ (n : N) (w : V), ρ g (ρ (n : G) w) = ρ (MulAut.conjNormal g n : G) (ρ g w) :=
    fun n w => by
      have h := apply_conjNormal_inv ρ g (MulAut.conjNormal g n) w
      rwa [map_inv, MulAut.inv_apply_self] at h
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | single n c =>
    rw [conjNormalAlgAut_single, asModuleConjEquiv_apply, _root_.Representation.single_smul,
      _root_.Representation.single_smul, map_smul]
    exact congrArg (fun w => c • w) (hconj n _)
end Translate
section Hom
variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] {ρ : Representation k G V}
  {σ τ : Subrepresentation (ρ.comp N.subtype)}
variable (ρ) in
private noncomputable def conjSubrepMap (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    τ.asSubmodule :=
  Subtype.map
    (fun v : _root_.Representation.asModule (ρ.comp N.subtype) =>
      asModuleConjEquiv ρ g v) h x
omit [N.Normal] in
@[simp]
private theorem coe_conjSubrepMap (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    (conjSubrepMap ρ g h x : _root_.Representation.asModule (ρ.comp N.subtype))
      = asModuleConjEquiv ρ g x.1 :=
  (rfl)
omit [N.Normal] in
@[simp]
private theorem conjSubrepMap_add (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x y : σ.asSubmodule) :
    conjSubrepMap ρ g h (x + y) = conjSubrepMap ρ g h x + conjSubrepMap ρ g h y :=
  Subtype.ext (by simp)
@[simp]
private theorem conjSubrepMap_smul (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (a : k[N]) (x : σ.asSubmodule) :
    conjSubrepMap ρ g h (a • x) = conjNormalAlgAut k N g a • conjSubrepMap ρ g h x :=
  Subtype.ext (by simp)
omit [N.Normal] in
@[simp]
private theorem conjSubrepMap_inv_self_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) (x : σ.asSubmodule) :
    conjSubrepMap ρ g⁻¹ h' (conjSubrepMap ρ g h x) = x :=
  Subtype.ext (_root_.Representation.inv_self_apply ρ g _)
omit [N.Normal] in
@[simp]
private theorem conjSubrepMap_self_inv_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) (y : τ.asSubmodule) :
    conjSubrepMap ρ g h (conjSubrepMap ρ g⁻¹ h' y) = y :=
  Subtype.ext (_root_.Representation.self_inv_apply ρ g _)
variable (ρ) in
private noncomputable def conjHom (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :
    σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype) where
  toFun x := asModuleConjEquiv ρ g⁻¹ (f (conjSubrepMap ρ g h x))
  map_add' x y := by simp
  map_smul' a x := by simp
@[simp]
private theorem conjHom_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
    (x : σ.asSubmodule) :
    conjHom ρ g h f x = asModuleConjEquiv ρ g⁻¹ (f (conjSubrepMap ρ g h x)) :=
  (rfl)
variable (ρ) in
private noncomputable def conjHomₗ (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) :
    (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) →ₗ[k]
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) where
  toFun := conjHom ρ g h
  map_add' f₁ f₂ := LinearMap.ext fun x => by
    simp only [conjHom_apply, LinearMap.add_apply, map_add]
  map_smul' c f := LinearMap.ext fun x => by
    simp only [conjHom_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]
@[simp]
private theorem conjHomₗ_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :
    conjHomₗ ρ g h f = conjHom ρ g h f :=
  (rfl)
variable (ρ) in
private noncomputable def conjHomEquiv (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) :
    (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) ≃ₗ[k]
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  LinearEquiv.ofLinearMap (conjHomₗ ρ g h) (conjHomₗ ρ g⁻¹ h')
    (LinearMap.ext fun f => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, conjHomₗ_apply, LinearMap.id_apply, conjHom_apply, inv_inv,
        conjSubrepMap_inv_self_apply]
      exact _root_.Representation.inv_self_apply ρ g _)
    (LinearMap.ext fun f => LinearMap.ext fun y => by
      simp only [LinearMap.comp_apply, conjHomₗ_apply, LinearMap.id_apply, conjHom_apply, inv_inv,
        conjSubrepMap_self_inv_apply]
      exact _root_.Representation.self_inv_apply ρ g _)
end Hom
section Conjugate
variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
@[simp]
private theorem finrank_linearMap_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Module.finrank k
        ((conjSubrep ρ g σ).asSubmodule →ₗ[k[N]]
          _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  (conjHomEquiv ρ g
    (fun _ hv => mem_conjSubrep_iff.mpr (by rwa [_root_.Representation.inv_self_apply]))
    (fun _ hv => mem_conjSubrep_iff.mp hv)).finrank_eq
end Conjugate
section Clifford
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
private theorem finrank_linearMap_eq_of_isAtom [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (T : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    Module.finrank k (T →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ T
  rw [(LinearEquiv.congrLeft
      (_root_.Representation.asModule (ρ.comp N.subtype)) k e).finrank_eq,
    finrank_linearMap_conjSubrep]
private theorem finrank_linearMap_eq_of_isAtom_of_isAtom [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    Module.finrank k (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  have := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  finrank_linearMap_eq_of_isAtom ρ hτ σ.asSubmodule
omit [N.Normal] in
private theorem finrank_linearMap_pos [FiniteDimensional k V] {σ : Subrepresentation (ρ.comp N.subtype)}
    (hσ : σ ≠ ⊥) :
    0 < Module.finrank k
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  refine finrank_linearMap_pos_of_ne_bot fun hc => hσ ?_
  refine Subrepresentation.subrepresentationSubmoduleOrderIso.injective ?_
  rw [Subrepresentation.subrepresentationSubmoduleOrderIso.map_bot,
    Subrepresentation.subrepresentationSubmoduleOrderIso_apply]
  exact hc
theorem exists_forall_finrank_linearMap_eq [ρ.IsIrreducible] [FiniteDimensional k V] :
    ∃ e : ℕ, 0 < e ∧ ∀ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ →
      Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e := by
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAtom_forall_nonempty_linearEquiv_conjSubrep ρ (N := N)
  exact ⟨_, finrank_linearMap_pos ρ hσ₀.1,
    fun σ hσ => finrank_linearMap_eq_of_isAtom_of_isAtom ρ hσ hσ₀⟩
end Clifford
end Representation
end UpstreamSource4_4
section UpstreamSource4_5
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
open CategoryTheory
open scoped _root_.MonoidAlgebra
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable {ρ : _root_.Representation k G V} {σ : _root_.Representation k G W}
noncomputable def equivOfAsModuleLinearEquiv (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) : ρ.Equiv σ :=
  _root_.Representation.IntertwiningMap.ofBijective
    ((_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm f.toLinearMap)
    f.bijective
noncomputable def asModuleLinearEquivOfEquiv (φ : ρ.Equiv σ) : ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap)
    φ.bijective
private theorem nonempty_equiv_iff :
    Nonempty (ρ.Equiv σ) ↔ Nonempty (ρ.asModule ≃ₗ[k[G]] σ.asModule) :=
  ⟨fun ⟨φ⟩ ↦ ⟨asModuleLinearEquivOfEquiv φ⟩, fun ⟨f⟩ ↦ ⟨equivOfAsModuleLinearEquiv f⟩⟩
end Representation
universe u v
variable {k V W : Type u} {G : Type v} [CommRing k] [Monoid G]
variable [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {ρ : Representation k G V} {σ : Representation k G W}
noncomputable def fdRepIsoOfAsModuleLinearEquiv (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    FDRep.of ρ ≅ FDRep.of σ :=
  (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).preimageIso
    (Rep.mkIso (Representation.equivOfAsModuleLinearEquiv f))
theorem nonempty_fdRepIso_iff {X Y : FDRep k G} :
    Nonempty (X ≅ Y) ↔ Nonempty (_root_.Representation.Equiv X.ρ Y.ρ) :=
  by
    constructor
    · rintro ⟨i⟩
      have e := _root_.Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep k G) (Rep k G)).mapIso i)
      rw [FDRep.forget₂_ρ, FDRep.forget₂_ρ] at e
      exact ⟨e⟩
    · rintro ⟨φ⟩
      have i := fdRepIsoOfAsModuleLinearEquiv
        (Representation.asModuleLinearEquivOfEquiv φ)
      rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.of_ρ_eq_self, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.of_ρ_eq_self] at i
      exact ⟨i⟩
theorem toSkeleton_fdRepOf_toRepresentation_eq_iff
    {K X : Type u} [CommRing K] [AddCommGroup X] [Module K X]
    {π : _root_.Representation K G X} (S T : Subrepresentation π)
    [Module.Finite K S.toSubmodule] [Module.Finite K T.toSubmodule] :
    toSkeleton (FDRep.of S.toRepresentation) = toSkeleton (FDRep.of T.toRepresentation) ↔
      Nonempty (S.asSubmodule ≃ₗ[K[G]] T.asSubmodule) := by
  rw [toSkeleton_eq_toSkeleton_iff, nonempty_fdRepIso_iff,
    Representation.nonempty_equiv_iff]
  exact Nonempty.congr
    (fun e => ((_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule S)).symm.trans e |>.trans
      (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule T))
    (fun e => (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule S).trans e |>.trans
      (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule T).symm)
end TauCeti
end UpstreamSource4_5
section UpstreamSource4_6
open CategoryTheory
open scoped Pointwise
universe u v
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [hN : N.Normal]
section Ring
variable [Ring k]
@[simp]
theorem mem_inertia_iff {A : FDRep k N} {g : G} :
    g ∈ (MulAction.stabilizer G (toSkeleton A)) ↔ Nonempty ((conjNormalFDRepFunctor g).obj A ≅ A) := by
  rw [MulAction.mem_stabilizer_iff, smul_toSkeleton, toSkeleton_eq_toSkeleton_iff]
theorem le_inertia (A : FDRep k N) : N ≤ (MulAction.stabilizer G (toSkeleton A)) :=
  fun n hn => mem_inertia_iff.2 ⟨conjNormalFDRepIso A ⟨n, hn⟩⟩
end Ring
section Field
variable [Field k]
theorem char_conj_eq_of_mem_inertia {A : FDRep k N} {g : G} (hg : g ∈ (MulAction.stabilizer G (toSkeleton A))) (x : N) :
    A.character ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ = A.character x := by
  obtain ⟨e⟩ := mem_inertia_iff.1 hg
  rw [← char_conjNormalFDRep_mk, FDRep.char_iso e]
end Field
end TauCeti
end UpstreamSource4_6
end D5.S3.FiniteGroups.CliffordConstituents
