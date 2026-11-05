/- GID: D5/S3/FiniteGroups/FiniteCharacterAlgebra
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FiniteCharacterAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: FiniteCharacterAlgebra. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: Representation.asAlgebraHom_surjective_of_isIrreducible
A linear operator is extended to an endomorphism commuting with the commutant using Schur scalars, then realized by the representation algebra.
Subrepresentation.toSubmodule_bot | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.iSup_conjSubrep_eq_top, Representation.IntertwiningMap.eq_zero_iff_range_eq_bot, TauCeti.Representation.exists_isAtom, TauCeti.Representation.isIrreducible_of_finrank_eq_one, TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom
Subrepresentation.toSubmodule_top | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top, Representation.IntertwiningMap.surjective_iff_range_eq_top, TauCeti.Representation.exists_isAtom, TauCeti.Representation.isIrreducible_of_finrank_eq_one, TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom
Subrepresentation.toSubmodule_le_toSubmodule | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.exists_isAtom_le
Subrepresentation.toSubmodule_lt_toSubmodule | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.exists_isAtom_le
Representation.IntertwiningMap.eq_zero_iff_range_eq_bot | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.subtype_eq_zero_iff
Representation.IntertwiningMap.surjective_iff_range_eq_top | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.subtype_surjective_iff
Subrepresentation.subtype | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.coe_subtype, Subrepresentation.range_subtype, Subrepresentation.subtype_eq_zero_iff, Subrepresentation.subtype_injective, Subrepresentation.subtype_surjective_iff, Subrepresentation.toLinearMap_subtype, epi_repOfHom_subtype_iff, isIso_subInclusion_iff, map_subInclusion, mono_map_subInclusion, mono_repOfHom_subtype, repOfHom_subtype_eq_zero_iff, subInclusion, subInclusion_eq_zero_iff
Subrepresentation.coe_subtype | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.subtype_injective
Subrepresentation.toLinearMap_subtype | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.range_subtype
Subrepresentation.range_subtype | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.subtype_eq_zero_iff, Subrepresentation.subtype_surjective_iff
Subrepresentation.subtype_injective | proof_shape: bind-only | escape_witness: none | consumer: mono_repOfHom_subtype
Subrepresentation.subtype_eq_zero_iff | proof_shape: bind-only | escape_witness: none | consumer: repOfHom_subtype_eq_zero_iff
Subrepresentation.subtype_surjective_iff | proof_shape: bind-only | escape_witness: none | consumer: epi_repOfHom_subtype_iff
Subrepresentation.coe_toRepresentation_asAlgebraHom_apply | proof_shape: bind-only | escape_witness: none | consumer: Subrepresentation.asModuleEquivAsSubmodule
Subrepresentation.asModuleEquivAsSubmodule | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
Subrepresentation.isSimpleModule_asSubmodule_iff | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.Representation.finrank_linearMap_eq_of_isAtom_of_isAtom, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_nonempty_linearEquiv_conjSubrep, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isotypicComponents_eq_range, D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent, D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv
Rep.simple_iff_isIrreducible | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_iff_isIrreducible
mono_repOfHom_subtype | proof_shape: bind-only | escape_witness: none | consumer: mono_map_subInclusion
repOfHom_subtype_eq_zero_iff | proof_shape: bind-only | escape_witness: none | consumer: subInclusion_eq_zero_iff
epi_repOfHom_subtype_iff | proof_shape: bind-only | escape_witness: none | consumer: isIso_subInclusion_iff
subInclusion | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_iff_isIrreducible, instMonoFDRepSubInclusion, isIso_subInclusion_iff, mono_map_subInclusion, subInclusion_eq_zero_iff
map_subInclusion | proof_shape: bind-only | escape_witness: none | consumer: isIso_subInclusion_iff, mono_map_subInclusion, subInclusion_eq_zero_iff
mono_map_subInclusion | proof_shape: bind-only | escape_witness: none | consumer: instMonoFDRepSubInclusion, isIso_subInclusion_iff
instMonoFDRepSubInclusion | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_iff_isIrreducible
subInclusion_eq_zero_iff | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_iff_isIrreducible
isIso_subInclusion_iff | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_iff_isIrreducible
FDRep.simple_iff_isIrreducible | proof_shape: bind-only | escape_witness: none | consumer: FDRep.isIrreducible_of_simple, FDRep.simple_of_isIrreducible
FDRep.simple_of_isIrreducible | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso, D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian, D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.simple_ofLinearCharacter
FDRep.isIrreducible_of_simple | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.abelian_character_eq_iff, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_quotient_card, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_square_le_card
FDRep.character_actionRes | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.comap_subtype_ofFDRep, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial
FDRep.moduleFiniteForgetObject | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.character_indFDRep_sum_quotient, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.finrank_indFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRepForgetEquiv
FDRep.finrankForgetObject | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.finrank_indFDRep
FDRep.characterForgetObject | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.character_indFDRep_sum_quotient
FDRep.of_ρ_eq_self | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.nonempty_fdRepIso_iff
FDRep.ofShrink | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, D5.S3.FiniteGroups.CliffordDecomposition.FDRep.finrank_cliffordSum, FDRep.character_ofShrink, FDRep.finrank_ofShrink, FDRep.ofShrinkEquiv, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRep
FDRep.ofShrinkEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom, FDRep.character_ofShrink, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRepForgetEquiv
FDRep.finrank_ofShrink | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.finrank_cliffordSum
FDRep.character_ofShrink | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum
TauCeti.ClassFunction | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.character_mul_character_inv_mem_classFunction, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, TauCeti.ClassFunction.characterPairing, TauCeti.ClassFunction.characterPairing_apply, TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank, TauCeti.ClassFunction.characterPairing_symm, TauCeti.ClassFunction.comap, TauCeti.ClassFunction.comap_apply, TauCeti.ClassFunction.comap_subtype_ofFDRep, TauCeti.ClassFunction.eq_of_isConj, TauCeti.ClassFunction.mem_iff, TauCeti.ClassFunction.ofCharacter, TauCeti.ClassFunction.ofCharacter_apply, TauCeti.ClassFunction.sum_eq_sum_conjClasses, TauCeti.ClassFunction.toConjClasses, TauCeti.ClassFunction.toConjClasses_mk, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_apply, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_ofFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.character_mem_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.frobenius_reciprocity_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_mem_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_eq_of_mk_eq, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.natCard_mul_indClassFun, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.natCard_mul_sum_indClassFun_mul, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.sum_indTerm_mul_eq_sum_subtype, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFun_mem_classFunction, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFunction, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFunction_coe, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.ofFDRep_res_mackeyToH
TauCeti.ClassFunction.mem_iff | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.character_mul_character_inv_mem_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.character_mem_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_mem_classFunction, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_eq_of_mk_eq, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.sum_indTerm_mul_eq_sum_subtype, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFun_mem_classFunction
TauCeti.ClassFunction.eq_of_isConj | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.toConjClasses
TauCeti.ClassFunction.toConjClasses | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, TauCeti.ClassFunction.sum_eq_sum_conjClasses, TauCeti.ClassFunction.toConjClasses_mk
TauCeti.ClassFunction.toConjClasses_mk | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, TauCeti.ClassFunction.sum_eq_sum_conjClasses
TauCeti.ClassFunction.comap | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.comap_apply, TauCeti.ClassFunction.comap_subtype_ofFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.ClassFunction.comap_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.comap_subtype_ofFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey
TauCeti.ClassFunction.sum_eq_sum_conjClasses | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card
TauCeti.ClassFunction.ofCharacter | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, TauCeti.ClassFunction.characterPairing_ofFDRep, TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank, TauCeti.ClassFunction.comap_subtype_ofFDRep, TauCeti.ClassFunction.ofCharacter_apply, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_ofFDRep, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.ofFDRep_res_mackeyToH
TauCeti.ClassFunction.ofCharacter_apply | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, TauCeti.ClassFunction.comap_subtype_ofFDRep, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_ofFDRep
TauCeti.actionRes_comp | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepFunctor_mul, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_of_normal
TauCeti.finrank_hom_res_mulEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_of_normal
TauCeti.resSubrepresentationOrderIso | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.isIrreducible_comp_surjective_iff
TauCeti.isIrreducible_comp_surjective_iff | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_quotient_card
TauCeti.ClassFunction.comap_subtype_ofFDRep | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.classSum | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.asAlgebraHom_classSum, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.trace_asAlgebraHom_classSum, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.isIntegral_classSumCenter, TauCeti.classSumCenter, TauCeti.classSum_commutes, TauCeti.classSum_eq_sum, TauCeti.classSum_mem_center
TauCeti.classSum_eq_sum | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.asAlgebraHom_classSum, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.isIntegral_classSumCenter, TauCeti.classSum_commutes
TauCeti.conjugateCarrierEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.classSum_commutes, TauCeti.conjugateCarrierEquiv_apply
TauCeti.conjugateCarrierEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.classSum_commutes
TauCeti.classSum_commutes | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.classSum_mem_center
TauCeti.classSum_mem_center | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.classSumCenter
TauCeti.classSumCenter | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.isIntegral_centralCharacter_classSumCenter, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.isIntegral_classSumCenter, TauCeti.classSumCenter_coe
TauCeti.classSumCenter_coe | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.isIntegral_classSumCenter
TauCeti.finite_end_of_smulCommClass | proof_shape: bind-only | escape_witness: none | consumer: Representation.asAlgebraHom_surjective_of_isIrreducible
TauCeti.hom_eq_zero_of_isEmpty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.subsingleton_linearMap_of_isEmpty_linearEquiv
TauCeti.subsingleton_linearMap_of_isEmpty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finiteDimensional_linearMap_of_isEmpty_linearEquiv, TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv
TauCeti.endAlgEquivSelfOfIsSimpleModule | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter, D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.smul_eq_centralCharacter_smul, Representation.asAlgebraHom_surjective_of_isIrreducible, TauCeti.endAlgEquivSelfOfIsSimpleModule_smul, TauCeti.endAlgEquivSelfOfIsSimpleModule_symm_apply, TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv
TauCeti.endAlgEquivSelfOfIsSimpleModule_symm_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.endAlgEquivSelfOfIsSimpleModule_smul
TauCeti.endAlgEquivSelfOfIsSimpleModule_smul | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.smul_eq_centralCharacter_smul, Representation.asAlgebraHom_surjective_of_isIrreducible
TauCeti.homCongrRight | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi, TauCeti.finiteDimensional_linearMap_of_isSimpleModule, TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv
TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_pi_eq_natCard
TauCeti.finiteDimensional_linearMap_of_isEmpty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finiteDimensional_linearMap_of_isSimpleModule
TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_pi_eq_natCard
TauCeti.finiteDimensional_linearMap_of_isSimpleModule | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_pi_eq_natCard
Representation.IsIrreducible.nontrivial | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isSemisimpleRepresentation_comp_subtype, Representation.IsIrreducible.finrank_pos, Representation.asAlgebraHom_surjective_of_isIrreducible
Representation.IsIrreducible.finrank_pos | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd
TauCeti.Representation.isIrreducible_of_finrank_eq_one | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.Representation.isIrreducible_linearCharacterRepresentation
TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso
Representation.asAlgebraHom_surjective_of_isIrreducible | proof_shape: content | escape_witness: Representation.asAlgebraHom_surjective_of_isIrreducible | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_square_le_card
TauCeti.Representation.exists_isAtom_le | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.exists_isAtom
TauCeti.Representation.exists_isAtom | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep, D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isSemisimpleRepresentation_comp_subtype
TauCeti.ClassFunction.card_inv_mul_sum_mul_smul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.characterPairing
TauCeti.ClassFunction.characterPairing | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.characterPairing_apply, TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank, TauCeti.ClassFunction.characterPairing_symm, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.ClassFunction.characterPairing_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.characterPairing_ofFDRep, TauCeti.ClassFunction.characterPairing_symm, D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.ClassFunction.characterPairing_symm | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey
TauCeti.ClassFunction.characterPairing_ofFDRep | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank
TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
-/
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.SimpleModule.Rank
namespace D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace FDRep
end FDRep
namespace Rep
end Rep
namespace Representation
end Representation
namespace Representation.IntertwiningMap
end Representation.IntertwiningMap
namespace Representation.IsIrreducible
end Representation.IsIrreducible
namespace Subrepresentation
end Subrepresentation
namespace TauCeti
end TauCeti
namespace TauCeti.ClassFunction
end TauCeti.ClassFunction
namespace TauCeti.Representation
end TauCeti.Representation
section Source0
namespace Subrepresentation
open _root_.Subrepresentation
variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}
@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
@[simp]
private lemma toSubmodule_le_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule ≤ ρ₂.toSubmodule ↔ ρ₁ ≤ ρ₂ := ge_iff_le
@[simp]
private lemma toSubmodule_lt_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule < ρ₂.toSubmodule ↔ ρ₁ < ρ₂ := gt_iff_lt
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.eq_zero_iff_range_eq_bot
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : f = 0 ↔ f.range = ⊥ := by
  rw [← (Representation.IntertwiningMap.toLinearMap_injective ρ τ).eq_iff,
    Representation.IntertwiningMap.zero_toLinearMap, ← LinearMap.range_eq_bot,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot]
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.surjective_iff_range_eq_top
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : Function.Surjective f ↔ f.range = ⊤ := by
  rw [← Representation.IntertwiningMap.coe_toLinearMap, ← LinearMap.range_eq_top,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top]
private def subtype (ρ' : Subrepresentation ρ) :
    Representation.IntertwiningMap ρ'.toRepresentation ρ where
  toLinearMap := ρ'.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl
@[simp]
private lemma coe_subtype (ρ' : Subrepresentation ρ) : ⇑(_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ') = Subtype.val := by rfl
@[simp]
private lemma toLinearMap_subtype (ρ' : Subrepresentation ρ) :
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ').toLinearMap = ρ'.toSubmodule.subtype := by rfl
@[simp]
private theorem range_subtype (ρ' : Subrepresentation ρ) : (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ').range = ρ' := by
  apply toSubmodule_injective
  rw [Representation.IntertwiningMap.range_toSubmodule, toLinearMap_subtype,
    Submodule.range_subtype]
private theorem subtype_injective (ρ' : Subrepresentation ρ) : Function.Injective (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ') := by
  simpa only [coe_subtype] using Subtype.val_injective
@[simp]
private theorem subtype_eq_zero_iff (ρ' : Subrepresentation ρ) : (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ') = 0 ↔ ρ' = ⊥ := by
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.eq_zero_iff_range_eq_bot, range_subtype]
private theorem subtype_surjective_iff (ρ' : Subrepresentation ρ) :
    Function.Surjective (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype ρ') ↔ ρ' = ⊤ := by
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.surjective_iff_range_eq_top, range_subtype]
@[simp]
private theorem coe_toRepresentation_asAlgebraHom_apply {k H V : Type*} [CommSemiring k] [Monoid H]
    [AddCommMonoid V] [Module k V] {σ : Representation k H V} (S : Subrepresentation σ)
    (a : MonoidAlgebra k H) (x : S.toSubmodule) :
    ((S.toRepresentation.asAlgebraHom a x : S.toSubmodule) : V) =
      σ.asAlgebraHom a (x : V) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
        congrArg₂ (fun u v => u + v) ha hb
  | single g r =>
      simp only [Representation.asAlgebraHom_single]
      congr 1
section AsSubmoduleEquiv
open scoped _root_.MonoidAlgebra
variable {A G W : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}
noncomputable def asModuleEquivAsSubmodule (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[A[G]] σ.asSubmodule where
  toFun x := ⟨(_root_.Representation.asModuleEquiv ρ).symm
      (σ.toRepresentation.asModuleEquiv x : W),
    (Subrepresentation.mem_asSubmodule_iff
      (v := (σ.toRepresentation.asModuleEquiv x : W))).mpr
        (σ.toRepresentation.asModuleEquiv x).2⟩
  invFun x := σ.toRepresentation.asModuleEquiv.symm
    ⟨_root_.Representation.asModuleEquiv ρ x.1,
      (Subrepresentation.mem_asSubmodule_iff
        (v := _root_.Representation.asModuleEquiv ρ x.1)).mp x.2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' a x := by
    apply Subtype.ext
    apply (_root_.Representation.asModuleEquiv ρ).injective
    simp only [LinearEquiv.apply_symm_apply, RingHom.id_apply,
      _root_.Representation.asModuleEquiv_map_smul]
    exact coe_toRepresentation_asAlgebraHom_apply σ a
      (σ.toRepresentation.asModuleEquiv x)
end AsSubmoduleEquiv
section AsSubmodule
open scoped _root_.MonoidAlgebra
variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}
@[simp]
theorem isSimpleModule_asSubmodule_iff {σ : Subrepresentation ρ} :
    IsSimpleModule A[G] σ.asSubmodule ↔ IsAtom σ :=
  isSimpleModule_iff_isAtom.trans (subrepresentationSubmoduleOrderIso.isAtom_iff σ)
end AsSubmodule
end Subrepresentation
end Source0
section Source1
open CategoryTheory
open scoped _root_.MonoidAlgebra
universe u v w
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Rep.simple_iff_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) : Simple A ↔ Representation.IsIrreducible A.ρ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    ← simple_iff_isSimpleModule' (ModuleCat.of k[G] A.ρ.asModule)]
  exact (simple_obj_iff (Rep.toModuleMonoidAlgebra (k := k) (G := G)) A).symm
section FDRep
variable {k : Type u} {G : Type v} [Field k] [Monoid G]
section Inclusion
variable {V : Type u} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  (W : Subrepresentation ρ)
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_repOfHom_subtype : Mono (Rep.ofHom (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype W)) :=
  (Rep.mono_iff_injective _).mpr (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_injective W)
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.repOfHom_subtype_eq_zero_iff : Rep.ofHom (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype W) = 0 ↔ W = ⊥ := by
  constructor
  · intro h
    apply (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_eq_zero_iff W).mp
    simpa using congrArg Rep.Hom.hom h
  · intro h
    rw [((_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_eq_zero_iff W).mpr h), Rep.ofHom_zero]
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.epi_repOfHom_subtype_iff : Epi (Rep.ofHom (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype W)) ↔ W = ⊤ := by
  rw [Rep.epi_iff_surjective]
  exact (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_surjective_iff W)
end Inclusion
private noncomputable def _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    FDRep.of W.toRepresentation ⟶ X :=
  (forget₂ (FDRep k G) (Rep k G)).preimage (Rep.ofHom (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype W))
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    (forget₂ (FDRep k G) (Rep k G)).map (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W) = Rep.ofHom (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype W) :=
  (forget₂ (FDRep k G) (Rep k G)).map_preimage _
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    Mono ((forget₂ (FDRep k G) (Rep k G)).map (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W)) := by
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion]
  exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_repOfHom_subtype W
private instance (X : FDRep k G) (W : Subrepresentation X.ρ) : Mono (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W) :=
  (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_map_subInclusion X W)
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion_eq_zero_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W = 0 ↔ W = ⊥ := by
  rw [← (forget₂ (FDRep k G) (Rep k G)).map_eq_zero_iff, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion]
  exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.repOfHom_subtype_eq_zero_iff W
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.isIso_subInclusion_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    IsIso (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W) ↔ W = ⊤ := by
  constructor
  · intro h
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X W)) := inferInstance
    rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion] at hepi
    exact (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.epi_repOfHom_subtype_iff W).mp hepi
  · rintro rfl
    have hmono := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_map_subInclusion X (⊤ : Subrepresentation X.ρ)
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map
        (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X (⊤ : Subrepresentation X.ρ))) := by
      rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion]
      exact (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.epi_repOfHom_subtype_iff _).mpr rfl
    have : IsIso ((forget₂ (FDRep k G) (Rep k G)).map
        (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion X (⊤ : Subrepresentation X.ρ))) := isIso_of_mono_of_epi _
    exact isIso_of_reflects_iso _ (forget₂ (FDRep k G) (Rep k G))
private theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_iff_isIrreducible (X : FDRep k G) :
    Simple X ↔ Representation.IsIrreducible X.ρ := by
  constructor
  · intro _
    have key : ∀ W : Subrepresentation X.ρ, W = ⊤ ↔ ¬W = ⊥ := fun W => by
      rw [← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.isIso_subInclusion_iff, ← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion_eq_zero_iff]
      exact Simple.mono_isIso_iff_nonzero _
    have hbot : (⊥ : Subrepresentation X.ρ) ≠ ⊤ := fun h => (key ⊥).mp h rfl
    have : Nontrivial (Subrepresentation X.ρ) := nontrivial_of_ne ⊥ ⊤ hbot
    exact ⟨fun W => (em (W = ⊥)).imp id (key W).mpr⟩
  · intro _
    have hirr : Representation.IsIrreducible
        ((forget₂ (FDRep k G) (Rep k G)).obj X).ρ := by
      rw [FDRep.forget₂_ρ]
      exact ‹Representation.IsIrreducible X.ρ›
    have : Simple ((forget₂ (FDRep k G) (Rep k G)).obj X) :=
      (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Rep.simple_iff_isIrreducible _).mpr hirr
    exact Functor.simple_of_simple_obj (forget₂ (FDRep k G) (Rep k G)) X
instance _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible (X : FDRep k G)
    [Representation.IsIrreducible X.ρ] : Simple X :=
  (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_iff_isIrreducible X).mpr ‹_›
theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple (X : FDRep k G) [Simple X] :
    Representation.IsIrreducible X.ρ :=
  (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_iff_isIrreducible X).mp ‹_›
end FDRep
end Source1
section Source2
universe u v w
namespace FDRep
open _root_.FDRep
open CategoryTheory
@[simp]
theorem character_actionRes {k : Type u} {G : Type v} {H : Type w} [Field k] [Monoid G]
    [Monoid H] (V : FDRep k G) (phi : H →* G) (h : H) :
    FDRep.character ((Action.res (FGModuleCat k) phi).obj V) h = V.character (phi h) :=
  (rfl)
instance moduleFiniteForgetObject {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A)
@[simp]
theorem finrankForgetObject {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl
@[simp]
theorem characterForgetObject {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G)
    (g : G) : ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ.character g = A.character g := by
  rw [FDRep.character, Representation.character, FDRep.forget₂_ρ]
  rfl
@[simp]
theorem of_ρ_eq_self {R : Type u} {G : Type v} [CommRing R] [Monoid G] (A : FDRep R G) :
    FDRep.of A.ρ = A := (rfl)
section Shrink
variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Monoid G] [AddCommGroup V]
  [Module k V] [Module.Finite k V] (ρ : Representation k G V)
noncomputable def ofShrink : FDRep k G :=
  have : Small.{u} V := Module.Finite.small k V
  FDRep.of ((Shrink.linearEquiv k V).symm.conjRingEquiv.toMonoidHom.comp ρ)
noncomputable def ofShrinkEquiv : Representation.Equiv (ofShrink ρ).ρ ρ := by
  have : Small.{u} V := Module.Finite.small k V
  apply Representation.Equiv.mk (Shrink.linearEquiv k V)
  intro g
  ext x
  simp [ofShrink]
@[simp]
theorem finrank_ofShrink : Module.finrank k (ofShrink ρ) = Module.finrank k V := by
  have : Small.{u} V := Module.Finite.small k V
  exact LinearEquiv.finrank_eq (Shrink.linearEquiv k V)
end Shrink
section ShrinkCharacter
variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
@[simp]
theorem character_ofShrink (g : G) : (ofShrink ρ).character g = ρ.character g :=
  congrFun (Representation.char_iso (ofShrinkEquiv ρ)) g
end ShrinkCharacter
end FDRep
end Source2
section Source3
namespace TauCeti
universe u v w w'
def ClassFunction (k : Type u) (G : Type v) [Semiring k] [Group G] : Submodule k (G → k) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' _ _ := rfl
  add_mem' hf₁ hf₂ g h := by rw [Pi.add_apply, Pi.add_apply, hf₁ g h, hf₂ g h]
  smul_mem' c f hf g h := by rw [Pi.smul_apply, Pi.smul_apply, hf g h]
namespace ClassFunction
variable {k : Type u} {G : Type v} [Semiring k] [Group G]
@[simp]
theorem mem_iff {f : G → k} :
    f ∈ ClassFunction k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl
private theorem eq_of_isConj (f : ClassFunction k G) {g h : G} (hgh : IsConj g h) :
    f.1 g = f.1 h := by
  obtain ⟨x, rfl⟩ := isConj_iff.mp hgh
  exact (f.2 g x).symm
noncomputable def toConjClasses (f : ClassFunction k G) : ConjClasses G → k :=
  Quotient.lift f.1 fun _ _ h => eq_of_isConj f h
@[simp]
theorem toConjClasses_mk (f : ClassFunction k G) (g : G) :
    toConjClasses f (ConjClasses.mk g) = f.1 g :=
  (rfl)
def comap {H : Type w} [Group H] (φ : H →* G) :
    ClassFunction k G →ₗ[k] ClassFunction k H where
  toFun f := ⟨fun x => f.1 (φ x), fun g h => by
    simp only [map_mul, map_inv]
    exact f.2 (φ g) (φ h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp]
theorem comap_apply {H : Type w} [Group H] (φ : H →* G) (f : ClassFunction k G) (x : H) :
    (comap φ f).1 x = f.1 (φ x) :=
  (rfl)
theorem sum_eq_sum_conjClasses [Fintype G] [Fintype (ConjClasses G)] (f : ClassFunction k G) :
    ∑ g : G, f.1 g = ∑ C : ConjClasses G, (Nat.card C.carrier : k) * toConjClasses f C := by
  classical
  rw [← Fintype.sum_fiberwise (ConjClasses.mk (α := G)) fun g => f.1 g]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hconst : ∀ x : {g : G // ConjClasses.mk g = C}, f.1 x.1 = toConjClasses f C := by
    rintro ⟨x, rfl⟩
    exact (toConjClasses_mk f x).symm
  have hcard : Nat.card C.carrier = Fintype.card {g : G // ConjClasses.mk g = C} :=
    (Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => ConjClasses.mem_carrier_iff_mk_eq)).trans
      (Nat.card_eq_fintype_card)
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]
end ClassFunction
namespace ClassFunction
variable {k : Type u} {G : Type v} [Field k] [Group G]
noncomputable def ofCharacter {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ClassFunction k G :=
  ⟨ρ.character, fun g h => ρ.char_conj g h⟩
@[simp]
theorem ofCharacter_apply {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (g : G) : (ofCharacter ρ).1 g = ρ.character g :=
  (rfl)
end ClassFunction
end TauCeti
end Source3
section Source4
open CategoryTheory
namespace TauCeti
universe u v w
variable {k : Type u} {G : Type v} [Group G]
section Functor
variable [Semiring k] {H K L : Type*} [Monoid H] [Monoid K] [Monoid L]
theorem actionRes_comp {V : Type*} [Category V] (φ : K →* L) (ψ : H →* K) :
    Action.res V (φ.comp ψ) = Action.res V φ ⋙ Action.res V ψ :=
  rfl
end Functor
section Intertwining
variable [Field k] {M M' : Type*} [Group M] [Group M']
theorem finrank_hom_res_mulEquiv (e : M ≃* M') (X Y : FDRep k M') :
    Module.finrank k ((Action.res (FGModuleCat k) (e : M →* M')).obj X ⟶
        (Action.res (FGModuleCat k) (e : M →* M')).obj Y) = Module.finrank k (X ⟶ Y) :=
  have hff : (Action.res (FGModuleCat.{u, u} k) (e : M →* M')).FullyFaithful :=
    (Action.resEquiv (FGModuleCat.{u, u} k) e).fullyFaithfulFunctor
  (LinearEquiv.ofBijective
    ((Action.res (FGModuleCat.{u, u} k) (e : M →* M')).mapLinearMap k (X := X) (Y := Y))
    hff.homEquiv.bijective).finrank_eq.symm
end Intertwining
section Subrepresentation
variable [Semiring k] {H K : Type*} [Monoid H] [Monoid K] {V : Type*} [AddCommMonoid V] [Module k V]
private def resSubrepresentationOrderIso (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ S.apply_mem_toSubmodule (f h) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl
end Subrepresentation
section Irreducible
variable [Field k] {H K : Type*} [Monoid H] [Monoid K]
@[simp]
theorem isIrreducible_comp_surjective_iff {V : Type*} [AddCommGroup V] [Module k V]
    (f : H →* K) (hf : Function.Surjective f) (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (resSubrepresentationOrderIso f hf ρ).isSimpleOrder_iff
end Irreducible
section Representation
variable [CommRing k]
end Representation
section Character
variable [Field k]
@[simp]
theorem ClassFunction.comap_subtype_ofFDRep (S : Subgroup G) (B : FDRep k G) :
    ClassFunction.comap S.subtype ((ClassFunction.ofCharacter (FDRep.ρ B))) =
      (ClassFunction.ofCharacter (FDRep.ρ (((Action.res (FGModuleCat k) (S).subtype).obj B)))) :=
  Subtype.ext (funext fun s => by
    rw [ClassFunction.comap_apply, ClassFunction.ofCharacter_apply,
      ClassFunction.ofCharacter_apply]
    exact (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_actionRes B S.subtype s).symm)
end Character
end TauCeti
end Source4
section UpstreamSource0_3
namespace TauCeti
open scoped BigOperators
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
section
noncomputable def classSum (k : Type*) [Semiring k] (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ x : C.carrier, MonoidAlgebra.of k G x
theorem classSum_eq_sum {k : Type*} [Semiring k] (C : ConjClasses G) :
    classSum k C = ∑ x : C.carrier, MonoidAlgebra.of k G x := by
  rfl
omit [Fintype G] [DecidableEq G] in
private def conjugateCarrierEquiv (g : G) (C : ConjClasses G) : C.carrier ≃ C.carrier :=
  Equiv.subtypeEquiv (MulAut.conj g).toEquiv (fun x => by
    change x ∈ C.carrier ↔ g * x * g⁻¹ ∈ C.carrier
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq]
    have hc : ConjClasses.mk (g * x * g⁻¹) = ConjClasses.mk x :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by simp [mul_assoc]⟩)
    rw [hc])
omit [Fintype G] [DecidableEq G] in
@[simp]
private theorem conjugateCarrierEquiv_apply (g : G) (C : ConjClasses G) (x : C.carrier) :
    (conjugateCarrierEquiv g C x : G) = g * x * g⁻¹ := by
  simp [conjugateCarrierEquiv]
private theorem classSum_commutes {k : Type*} [Semiring k] (C : ConjClasses G) (g : G) :
    classSum k C * MonoidAlgebra.of k G g = MonoidAlgebra.of k G g * classSum k C := by
  rw [classSum_eq_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of k G).map_mul]
  rw [← (conjugateCarrierEquiv g C).sum_comp fun x => MonoidAlgebra.of k G (x * g)]
  congr 1
  ext x
  simp [mul_assoc]
end
private theorem classSum_mem_center (k : Type*) [CommSemiring k] (C : ConjClasses G) :
    classSum k C ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g => exact (classSum_commutes C g).symm
  | add x y hx hy =>
    rw [mul_add, add_mul, hx, hy]
  | smul r x hx =>
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]
end TauCeti
end UpstreamSource0_3
section UpstreamSource0_4
namespace TauCeti
open scoped BigOperators
variable {G k : Type*} [Group G] [Fintype G] [DecidableEq G] [CommSemiring k]
noncomputable def classSumCenter (C : ConjClasses G) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨classSum k C, classSum_mem_center k C⟩
@[simp]
theorem classSumCenter_coe (C : ConjClasses G) :
    (classSumCenter (k := k) C : MonoidAlgebra k G) = classSum k C :=
  (rfl)
end TauCeti
end UpstreamSource0_4
section UpstreamSource0_7
namespace TauCeti
open _root_.Module
variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
private theorem finite_end_of_smulCommClass (K : Type*) [Semiring K] [Module K M] [SMulCommClass R K M]
    [Module.Finite K M] : Module.Finite (Module.End R M) M :=
  Module.Finite.of_restrictScalars_finite K (Module.End R M) M
variable (R M)
variable {R M}
end TauCeti
end UpstreamSource0_7
section UpstreamSource0_8
namespace TauCeti
universe u v w
section SimpleModules
variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [IsSimpleModule R M] [IsSimpleModule R N]
private theorem hom_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) (f : M →ₗ[R] N) :
    f = 0 := by
  rcases f.bijective_or_eq_zero with hf | hf
  · exact (h.false (LinearEquiv.ofBijective f hf)).elim
  · exact hf
private theorem subsingleton_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) :
    Subsingleton (M →ₗ[R] N) :=
  ⟨fun f g ↦ sub_eq_zero.mp (hom_eq_zero_of_isEmpty_linearEquiv h (f - g))⟩
end SimpleModules
section SimpleEnd
variable {k : Type u} {A : Type v} {S : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
noncomputable def endAlgEquivSelfOfIsSimpleModule : Module.End A S ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A S))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)).symm
@[simp]
private theorem endAlgEquivSelfOfIsSimpleModule_symm_apply (c : k) :
    (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm c =
      algebraMap k (Module.End A S) c :=
  (rfl)
@[simp]
theorem endAlgEquivSelfOfIsSimpleModule_smul (f : Module.End A S) (s : S) :
    endAlgEquivSelfOfIsSimpleModule (k := k) f • s = f s := by
  conv_rhs =>
    rw [← (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm_apply_apply f]
  rw [endAlgEquivSelfOfIsSimpleModule_symm_apply, Module.algebraMap_end_apply]
end SimpleEnd
section CongrRight
variable (k : Type*) {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable {S : Type*} [AddCommMonoid S] [Module A S]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
variable {P : Type*} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]
def homCongrRight (e : N ≃ₗ[A] P) : (S →ₗ[A] N) ≃ₗ[k] (S →ₗ[A] P) where
  __ := LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl A S) e
  map_smul' c f := by
    ext s
    exact e.map_smul_of_tower c (f s)
end CongrRight
section Vanishing
section Semiring
variable {k A S N : Type*} [CommSemiring k] [Nontrivial k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]
theorem finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    Module.finrank k (S →ₗ[A] N) = 0 := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.finrank_zero_of_subsingleton
end Semiring
variable {k A S N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]
private theorem finiteDimensional_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    FiniteDimensional k (S →ₗ[A] N) := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.Finite.of_surjective (0 : k →ₗ[k] (S →ₗ[A] N)) fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
end Vanishing
section SchurDimension
variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [IsSimpleModule A N]
omit [IsSimpleModule A N] in
theorem finrank_linearMap_eq_one_of_nonempty_linearEquiv (e : S ≃ₗ[A] N) :
    Module.finrank k (S →ₗ[A] N) = 1 := by
  have hend : Module.finrank k (Module.End A S) = 1 := by
    rw [(endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [← (homCongrRight k (S := S) e).finrank_eq]
  exact hend
theorem finiteDimensional_linearMap_of_isSimpleModule : FiniteDimensional k (S →ₗ[A] N) := by
  by_cases h : Nonempty (S ≃ₗ[A] N)
  · have hend : FiniteDimensional k (S →ₗ[A] S) := LinearMap.finiteDimensional'


    exact Module.Finite.equiv (homCongrRight k (S := S) h.some)
  · exact finiteDimensional_linearMap_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)
end SchurDimension
end TauCeti
end UpstreamSource0_8
section UpstreamSource0_9
namespace TauCeti
namespace Representation
variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
open scoped _root_.MonoidAlgebra in
theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial {ρ : Representation k G V}
    (h : ρ.IsIrreducible) : Nontrivial V :=
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  ρ.asModuleEquiv.symm.toEquiv.nontrivial
theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.finrank_pos [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : 0 < Module.finrank k V :=
  have := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial h
  Module.finrank_pos
theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have hsimple : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k V) (by
      rw [← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot (ρ := ρ), ← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top
        (ρ := ρ), hc])
  have : Nontrivial (Subrepresentation ρ) := nontrivial_of_ne ⊥ ⊤ hne
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top.symm)
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  have hσ : σ.toSubmodule ≠ ⊥ := fun hc =>
    h.1 (Subrepresentation.toSubmodule_injective (hc.trans _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hσ
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k σ.toSubmodule) (by
      rw [← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot (ρ := σ.toRepresentation),
        ← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top (ρ := σ.toRepresentation), hc])
  have : Nontrivial (Subrepresentation σ.toRepresentation) := nontrivial_of_ne ⊥ ⊤ hne
  refine ⟨fun τ => ?_⟩
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.map σ.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩ }
  have hmap : τ'.toSubmodule = τ.toSubmodule.map σ.toSubmodule.subtype := rfl
  have hle : τ' ≤ σ := Submodule.map_subtype_le _ _
  rcases eq_or_ne τ' ⊥ with hτ | hτ
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊥ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_bot]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule hτ)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot.symm
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have heq : τ' = σ := (h.ne_bot_iff_eq hle).mp hτ


    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊤ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_subtype_top]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule heq)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top.symm
open scoped _root_.MonoidAlgebra in
theorem _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) :
    Function.Surjective ρ.asAlgebraHom := by
  have : ρ.IsIrreducible := hρ
  have : IsSimpleModule k[G] ρ.asModule := inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  have : Nontrivial V := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial hρ
  have : Module.Finite (Module.End k[G] ρ.asModule) ρ.asModule :=
    finite_end_of_smulCommClass (R := k[G]) (M := ρ.asModule) k
  intro T
  let T' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        change T (f x) = f (T x)
        rw [← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f x,
          ← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f (T x)]
        exact T.map_smul _ _ }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := k[G]) (M := ρ.asModule) T'
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  have hT' (y : ρ.asModule) : T' y = T y := rfl
  have hx := LinearMap.congr_fun ha (ρ.asModuleEquiv.symm x)
  rw [hT'] at hx
  have hx' := congrArg ρ.asModuleEquiv hx
  have hT_equiv : ρ.asModuleEquiv (T (ρ.asModuleEquiv.symm x)) = T x := rfl
  rw [hT_equiv] at hx'
  simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
    _root_.Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using hx'
section DivisionRing
variable {k G V : Type*} [DivisionRing k] [Monoid G] [AddCommGroup V] [Module k V]
private theorem exists_isAtom_le {ρ : Representation k G V} {σ : Subrepresentation ρ}
    [FiniteDimensional k σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ := by
  obtain ⟨τ, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT (fun τ : Subrepresentation ρ => τ ≠ ⊥ ∧ τ ≤ σ)
      (fun τ => Module.finrank k τ.toSubmodule) ⟨σ, hσ, le_rfl⟩
  obtain ⟨hτ, hτσ⟩ := hmin.1
  have : FiniteDimensional k τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  refine ⟨τ, hτσ, hτ, fun υ hυ => ?_⟩
  by_contra hυ0
  exact hmin.not_prop_of_lt
    (Submodule.finrank_lt_finrank_of_lt (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_lt_toSubmodule.mpr hυ))
    ⟨hυ0, hυ.le.trans hτσ⟩
theorem exists_isAtom [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, IsAtom σ := by
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := fun hc =>
    top_ne_bot (α := Submodule k V) (by
      rw [← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top (ρ := ρ), ← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot
        (ρ := ρ), hc])
  obtain ⟨σ, -, hσ⟩ := exists_isAtom_le htop
  exact ⟨σ, hσ⟩
end DivisionRing
end Representation
end TauCeti
end UpstreamSource0_9
section UpstreamSource1_1
namespace TauCeti
universe u v
namespace ClassFunction
variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
omit [Group G] in
private theorem card_inv_mul_sum_mul_smul (c : k) (f₁ f₂ : G → k) :
    (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * (c * f₂ g) =
      c * ((Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g) := by
  calc
    _ = (Nat.card G : k)⁻¹ * (c * ∑ g : G, f₁ g * f₂ g) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by ring
noncomputable def characterPairing :
    LinearMap.BilinForm k (ClassFunction k G) :=
  LinearMap.mk₂ k
    (fun f₁ f₂ => (Nat.card G : k)⁻¹ * ∑ g : G, f₁.1 g * f₂.1 g⁻¹)
    (by
      intro f₁ f₂ f₃
      simp [add_mul, Finset.sum_add_distrib, mul_add])
    (by
      intro c f₁ f₂
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        card_inv_mul_sum_mul_smul (G := G) c f₁.1 fun g => f₂.1 g⁻¹)
    (by
      intro f₁ f₂ f₃
      simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c f₁ f₂
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simpa using card_inv_mul_sum_mul_smul (G := G) c f₁.1 fun g => f₂.1 g⁻¹)
theorem characterPairing_apply (f₁ f₂ : ClassFunction k G) :
    characterPairing f₁ f₂ =
      (Nat.card G : k)⁻¹ * ∑ g : G, f₁.1 g * f₂.1 g⁻¹ :=
  (rfl)
theorem characterPairing_symm (f₁ f₂ : ClassFunction k G) :
    characterPairing f₁ f₂ = characterPairing f₂ f₁ := by
  rw [characterPairing_apply, characterPairing_apply]
  have hsum : (∑ g : G, f₁.1 g * f₂.1 g⁻¹) = ∑ g : G, f₂.1 g * f₁.1 g⁻¹ := by
    calc
      _ = ∑ g : G, f₁.1 g⁻¹ * f₂.1 (g⁻¹)⁻¹ := by
        apply Fintype.sum_equiv (Equiv.inv G)
        intro g
        simp
      _ = _ := by simp [mul_comm]
  rw [hsum]
private theorem characterPairing_ofFDRep (V W : FDRep k G) :
    characterPairing ((ClassFunction.ofCharacter (FDRep.ρ V))) ((ClassFunction.ofCharacter (FDRep.ρ W))) =
      (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ :=
  characterPairing_apply (ClassFunction.ofCharacter V.ρ) (ClassFunction.ofCharacter W.ρ)

theorem characterPairing_ofFDRep_eq_finrank [Invertible (Nat.card G : k)] (V W : FDRep k G) :
    characterPairing ((ClassFunction.ofCharacter (FDRep.ρ V))) ((ClassFunction.ofCharacter (FDRep.ρ W))) = Module.finrank k (W ⟶ V) := by
  rw [characterPairing_ofFDRep]
  exact FDRep.scalar_product_char_eq_finrank_equivariant W V
end ClassFunction
end TauCeti
end UpstreamSource1_1
end D5.S3.FiniteGroups.FiniteCharacterAlgebra
