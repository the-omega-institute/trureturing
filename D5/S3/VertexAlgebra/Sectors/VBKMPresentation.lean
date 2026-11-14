/- GID: D5/S3/VertexAlgebra/Sectors/VBKMPresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMPresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.VertexAlgebra.Sectors.VBKMPresentation.datum_enhanced
Direct frozen dependencies: none; all D5 prerequisites are in this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30339
Definitions are labelled bind-only as encodings, not as proofs of new propositions.
Declarations (consumer names are qualified by their owning module):
EnhancedCartanData: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.matrix, VBKMPresentation.EnhancedCartanData.simpleRoot, VBKMPresentation.EnhancedCartanData.GeneralizedCartan, VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.EnhancedCartanData.Symmetrizable, VBKMPresentation.EnhancedCartanData.Condition43, VBKMPresentation.EnhancedCartanData.deform, VBKMPresentation.EnhancedCartanData.heisenberg, VBKMPresentation.EnhancedCartanData.presentationRelations, VBKMPresentation.EnhancedCartanData.presentationIdeal, VBKMPresentation.EnhancedCartanData.Presented, VBKMPresentation.EnhancedCartanData.ph, VBKMPresentation.EnhancedCartanData.pe, VBKMPresentation.EnhancedCartanData.pf, VBKMPresentation.EnhancedCartanData.pL, VBKMPresentation.EnhancedCartanData.rankOne, VBKMPresentation.EnhancedCartanData.virasoro, VBKMPresentation.EnhancedCartanData.sideSeed, VBKMPresentation.EnhancedCartanData.localRelations, VBKMPresentation.EnhancedCartanData.localIdeal, VBKMPresentation.EnhancedCartanData.VBKM, VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.IdealRigidity, VBKMPresentation.claim, VBKMPresentation.datum, VBKMPresentation.datum_root_finite, VBKMPresentation.datum_simpleRoot_finite, VBKMPresentation.datum_no_positive, VBKMPresentation.datum_symmetrizable, VBKMPresentation.datum_condition43, VBKMPresentation.datum_coroot_span, VBKMPresentation.datum_enhanced, VBKMPresentation.EnhancedCartanData.presentationMap, VBKMPresentation.EnhancedCartanData.relation_vanishes, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, VBKMPresentation.EnhancedCartanData.presentation_generates, ZverykIdealRigidityRefutation.localH, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.freeRepresentation_relations.
matrix: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.GeneralizedCartan, VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.datum_no_positive, VBKMPresentation.datum_enhanced, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest.
PositiveReal: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.GeneralizedCartan, VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.datum_no_positive, VBKMPresentation.datum_enhanced.
NonpositiveInteger: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.GeneralizedCartan, VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.datum_enhanced.
FiniteDecompositions: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.GeneralizedCartan, VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.finite_decompositions_of_height, VBKMPresentation.datum_root_finite, VBKMPresentation.datum_simpleRoot_finite, VBKMPresentation.datum_enhanced.
simpleRoot: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.EnhancedCartanData.heisenberg, VBKMPresentation.datum_simpleRoot_finite, VBKMPresentation.datum_enhanced.
GeneralizedCartan: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.IsEnhanced, VBKMPresentation.datum_enhanced.
IsEnhanced: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, VBKMPresentation.datum_enhanced.
Symmetrizable: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, VBKMPresentation.datum_symmetrizable.
Condition43: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, VBKMPresentation.datum_condition43, ZverykIdealRigidityRefutation.result_of_survival.
deform: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, ZverykIdealRigidityRefutation.result_of_survival.
heisenberg: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, ZverykIdealRigidityRefutation.result_of_survival.
h: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.presentationRelations, VBKMPresentation.EnhancedCartanData.ph, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.freeRepresentation_h, ZverykIdealRigidityRefutation.freeRepresentation_relations.
e: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.presentationRelations, VBKMPresentation.EnhancedCartanData.pe, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.freeRepresentation_e, ZverykIdealRigidityRefutation.freeRepresentation_relations.
f: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.presentationRelations, VBKMPresentation.EnhancedCartanData.pf, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.freeRepresentation_f, ZverykIdealRigidityRefutation.freeRepresentation_relations.
L: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.presentationRelations, VBKMPresentation.EnhancedCartanData.pL, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.freeRepresentation_L, ZverykIdealRigidityRefutation.freeRepresentation_relations.
presentationRelations: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.presentationIdeal, VBKMPresentation.EnhancedCartanData.relation_vanishes, ZverykIdealRigidityRefutation.freeRepresentation_relations, ZverykIdealRigidityRefutation.presentationIdeal_le_representation_kernel.
presentationIdeal: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.Presented, VBKMPresentation.EnhancedCartanData.ph, VBKMPresentation.EnhancedCartanData.pe, VBKMPresentation.EnhancedCartanData.pf, VBKMPresentation.EnhancedCartanData.pL, VBKMPresentation.EnhancedCartanData.localRelations, VBKMPresentation.EnhancedCartanData.localIdeal, VBKMPresentation.EnhancedCartanData.VBKM, VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.IdealRigidity, VBKMPresentation.EnhancedCartanData.presentationMap, VBKMPresentation.EnhancedCartanData.relation_vanishes, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, VBKMPresentation.EnhancedCartanData.presentation_generates, ZverykIdealRigidityRefutation.localH, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.datum_localIdeal_zero, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.positive_singular, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.separating_cartan, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.localQuotientMap, ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival, ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.presentationIdeal_le_representation_kernel, ZverykIdealRigidityRefutation.representation, ZverykIdealRigidityRefutation.representation_pf, ZverykIdealRigidityRefutation.representation_pL, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
Presented: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.ph, VBKMPresentation.EnhancedCartanData.pe, VBKMPresentation.EnhancedCartanData.pf, VBKMPresentation.EnhancedCartanData.pL, VBKMPresentation.EnhancedCartanData.rankOne, VBKMPresentation.EnhancedCartanData.virasoro, VBKMPresentation.EnhancedCartanData.sideSeed, VBKMPresentation.EnhancedCartanData.localRelations, VBKMPresentation.EnhancedCartanData.localIdeal, VBKMPresentation.EnhancedCartanData.VBKM, VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.IdealRigidity, VBKMPresentation.EnhancedCartanData.presentationMap, VBKMPresentation.EnhancedCartanData.relation_vanishes, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, VBKMPresentation.EnhancedCartanData.presentation_generates, ZverykIdealRigidityRefutation.localH, ZverykIdealRigidityRefutation.localE, ZverykIdealRigidityRefutation.localF, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.datum_localIdeal_zero, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.negativeGenerator, ZverykIdealRigidityRefutation.positiveGenerator, ZverykIdealRigidityRefutation.cartanGenerators, ZverykIdealRigidityRefutation.allGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.positive_singular, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.separating_cartan, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.localQuotientMap, ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival, ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.representation, ZverykIdealRigidityRefutation.representation_pf, ZverykIdealRigidityRefutation.representation_pL, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
ph: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.rankOne, VBKMPresentation.EnhancedCartanData.virasoro, VBKMPresentation.EnhancedCartanData.localRelations, VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, ZverykIdealRigidityRefutation.localH, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.cartanGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.separating_cartan, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.cartan_map.
pe: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.rankOne, VBKMPresentation.EnhancedCartanData.sideSeed, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.pe_negative, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.positiveGenerator, ZverykIdealRigidityRefutation.mixed_positive_negative.
pf: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.rankOne, VBKMPresentation.EnhancedCartanData.sideSeed, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.negativeGenerator, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.representation_pf, ZverykIdealRigidityRefutation.representation_singular_vacuum.
pL: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.virasoro, VBKMPresentation.EnhancedCartanData.localRelations, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.negativeGenerator, ZverykIdealRigidityRefutation.positiveGenerator, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.representation_pL, ZverykIdealRigidityRefutation.representation_singular_vacuum.
cyclic: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.HighestProper, ZverykIdealRigidityRefutation.datum_no_rank_highest.
HighestProper: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localRelations, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty.
rankOne: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localRelations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty.
virasoro: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localRelations, ZverykIdealRigidityRefutation.datum_localRelations_empty.
sideSeed: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localRelations, ZverykIdealRigidityRefutation.localE, ZverykIdealRigidityRefutation.localF, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty.
modeSign: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localRelations, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty.
localRelations: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.localIdeal, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.datum_localIdeal_zero.
localIdeal: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.VBKM, VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.IdealRigidity, ZverykIdealRigidityRefutation.datum_localIdeal_zero, ZverykIdealRigidityRefutation.localQuotientMap, ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival.
VBKM: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.cartanSubspace, VBKMPresentation.EnhancedCartanData.IdealRigidity, ZverykIdealRigidityRefutation.localQuotientMap, ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival.
cartanSubspace: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.IdealRigidity, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival.
IdealRigidity: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.claim, ZverykIdealRigidityRefutation.not_rigid_of_survival, ZverykIdealRigidityRefutation.result_of_survival.
claim: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.result.
finite_nat_weight_fiber: proof_shape: content; frozen: none; escape_witness: VBKMPresentation.finite_nat_weight_fiber; consumers: VBKMPresentation.finite_decompositions_of_height.
finite_decompositions_of_height: proof_shape: content; frozen: none; escape_witness: VBKMPresentation.finite_nat_weight_fiber; consumers: VBKMPresentation.datum_root_finite, VBKMPresentation.datum_simpleRoot_finite.
datum: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_root_finite, VBKMPresentation.datum_simpleRoot_finite, VBKMPresentation.datum_no_positive, VBKMPresentation.datum_symmetrizable, VBKMPresentation.datum_condition43, VBKMPresentation.datum_coroot_span, VBKMPresentation.datum_enhanced, ZverykIdealRigidityRefutation.localH, ZverykIdealRigidityRefutation.localE, ZverykIdealRigidityRefutation.localF, ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.datum_localRelations_empty, ZverykIdealRigidityRefutation.datum_localIdeal_zero, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.negativeGenerator, ZverykIdealRigidityRefutation.positiveGenerator, ZverykIdealRigidityRefutation.cartanGenerators, ZverykIdealRigidityRefutation.allGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.positive_singular, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.separating_cartan, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.localQuotientMap, ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival, ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.freeRepresentation_relations, ZverykIdealRigidityRefutation.presentationIdeal_le_representation_kernel, ZverykIdealRigidityRefutation.representation, ZverykIdealRigidityRefutation.representation_pf, ZverykIdealRigidityRefutation.representation_pL, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
rootHeight: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_root_finite, VBKMPresentation.datum_simpleRoot_finite.
simpleWeight: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.simple_weight_nonzero, VBKMPresentation.simple_weight_sublevel_finite, VBKMPresentation.datum_simpleRoot_finite.
simple_weight_nonzero: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_simpleRoot_finite.
simple_weight_sublevel_finite: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_simpleRoot_finite.
datum_root_finite: proof_shape: content; frozen: none; escape_witness: VBKMPresentation.finite_nat_weight_fiber; consumers: VBKMPresentation.datum_enhanced.
datum_simpleRoot_finite: proof_shape: content; frozen: none; escape_witness: VBKMPresentation.finite_nat_weight_fiber; consumers: VBKMPresentation.datum_enhanced.
datum_no_positive: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_enhanced.
datum_symmetrizable: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.result_of_survival.
datum_condition43: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.result_of_survival.
datum_coroot_span: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.datum_enhanced.
datum_enhanced: proof_shape: content; frozen: none; escape_witness: VBKMPresentation.finite_nat_weight_fiber; consumers: ZverykIdealRigidityRefutation.result_of_survival.
presentationMap: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.relation_vanishes, VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive, VBKMPresentation.EnhancedCartanData.presentation_generates, ZverykIdealRigidityRefutation.allGenerators_generate.
relation_vanishes: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMPresentation.EnhancedCartanData.ph_commute, VBKMPresentation.EnhancedCartanData.ph_pe, VBKMPresentation.EnhancedCartanData.ph_pf, VBKMPresentation.EnhancedCartanData.pe_pf, VBKMPresentation.EnhancedCartanData.ph_pL, VBKMPresentation.EnhancedCartanData.pL_commute, VBKMPresentation.EnhancedCartanData.pL_zero, VBKMPresentation.EnhancedCartanData.pe_negative, VBKMPresentation.EnhancedCartanData.pf_positive.
ph_commute: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.separating_cartan.
ph_pe: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.datum_cross_no_highest.
ph_pf: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.presented_central_seed, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.separating_negative.
pe_pf: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.mixed_positive_negative.
ph_pL: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.presented_central_modes, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.separating_negative.
pL_commute: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.mixed_positive_negative.
pL_zero: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_seed_zero_weight, ZverykIdealRigidityRefutation.mode_mem_generators.
pe_negative: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.mixed_positive_negative.
pf_positive: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.datum_mode_no_highest, ZverykIdealRigidityRefutation.presented_positive_seed, ZverykIdealRigidityRefutation.mixed_positive_negative.
presentation_generates: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.allGenerators_generate.
-/


import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Lie.Free
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.Sl2

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMPresentation


attribute [local instance] Classical.propDecidable

structure EnhancedCartanData (I J H V : Type u)
    [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V] where
  pairing : H →ₗ[ℂ] V →ₗ[ℂ] ℂ
  coroot : I → H
  root : I → V
  degree : J → H
  central : J → H
  virRoot : J → V

namespace EnhancedCartanData

abbrev matrix {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (i k : I) : ℂ :=
  F.pairing (F.coroot i) (F.root k)

def PositiveReal (z : ℂ) : Prop := ∃ r : ℝ, 0 < r ∧ z = (r : ℂ)

def NonpositiveInteger (z : ℂ) : Prop := ∃ k : ℤ, k ≤ 0 ∧ z = (k : ℂ)

def FiniteDecompositions {A V : Type u} [AddCommGroup V] [Module ℂ V]
    (r : A → V) : Prop :=
  ∀ v : V, Set.Finite {m : A →₀ ℕ | (m.sum fun a n => (n : ℂ) • r a) = v}

def simpleRoot {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) :
    I ⊕ (J × ℕ+) → V
  | .inl i => F.root i
  | .inr (j, n) => (n.val : ℂ) • F.virRoot j

def GeneralizedCartan {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Prop :=
  Submodule.span ℂ (Set.range F.coroot) = ⊤ ∧
  (∀ i k : I, i ≠ k → PositiveReal (F.matrix i i) →
    NonpositiveInteger (2 * F.matrix i k / F.matrix i i)) ∧
  (∀ i k : I, F.matrix i k = 0 ↔ F.matrix k i = 0) ∧
  FiniteDecompositions F.root

def IsEnhanced {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Prop :=
  F.GeneralizedCartan ∧
  (∀ j : J, F.pairing (F.central j) (F.virRoot j) = 0 ∧
    F.pairing (F.degree j) (F.virRoot j) = -1) ∧
  (∀ (i : I) (j : J), PositiveReal (F.matrix i i) →
    NonpositiveInteger (F.pairing (F.coroot i) (F.virRoot j))) ∧
  FiniteDecompositions F.simpleRoot ∧
  (∀ (i : I) (j : J), F.pairing (F.central j) (F.root i) = 0 ↔
    F.pairing (F.coroot i) (F.virRoot j) = 0) ∧
  (∀ j k : J, F.pairing (F.central j) (F.virRoot k) = 0 ↔
    F.pairing (F.central k) (F.virRoot j) = 0) ∧
  (∀ (i : I) (j : J), F.pairing (F.central j) (F.root i) = 0 →
    F.pairing (F.degree j) (F.root i) = 0) ∧
  (∀ j k : J, k ≠ j → F.pairing (F.central j) (F.virRoot k) = 0 →
    F.pairing (F.degree j) (F.virRoot k) = 0)

def Symmetrizable {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Prop :=
  ∃ (T : H ≃ₗ[ℂ] H) (a : I → ℂ) (b c : J → ℂ),
    (∀ i : I, a i ≠ 0 ∧ T (F.coroot i) = a i • F.coroot i) ∧
    (∀ j : J, b j ≠ 0 ∧ T (F.degree j) = b j • F.degree j) ∧
    (∀ j : J, c j ≠ 0 ∧ T (F.central j) = c j • F.central j) ∧
    (∀ i k : I, F.pairing (T (F.coroot i)) (F.root k) =
      F.pairing (T (F.coroot k)) (F.root i)) ∧
    (∀ (i : I) (j : J), F.pairing (T (F.central j)) (F.root i) =
      F.pairing (T (F.coroot i)) (F.virRoot j)) ∧
    (∀ j k : J, F.pairing (T (F.central j)) (F.virRoot k) =
      F.pairing (T (F.central k)) (F.virRoot j))

def Condition43 {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Prop :=
  (∀ (i : I) (j : J), F.pairing (F.central j) (F.root i) = 0 ↔
    F.pairing (F.degree j) (F.root i) = 0) ∧
  (∀ j k : J, k ≠ j → (F.pairing (F.central j) (F.virRoot k) = 0 ↔
    F.pairing (F.degree j) (F.virRoot k) = 0))

noncomputable def deform {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (s t : ℂ) :
    EnhancedCartanData I J H V :=
  { F with degree := fun j => F.degree j + ((1 / 2 : ℂ) * (t / s)^2) • F.central j }

def heisenberg {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) :
    EnhancedCartanData (I ⊕ (J × ℕ+)) PEmpty H V where
  pairing := F.pairing
  coroot := fun z => match z with
    | .inl i => F.coroot i
    | .inr (j, n) => (n.val : ℂ) • F.central j
  root := F.simpleRoot
  degree := PEmpty.elim
  central := PEmpty.elim
  virRoot := PEmpty.elim

noncomputable def h {I J H : Type u} (z : H) : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) :=
  FreeLieAlgebra.of ℂ (.inl z)
noncomputable def e {I J H : Type u} (i : I) : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) :=
  FreeLieAlgebra.of ℂ (.inr (.inl i))
noncomputable def f {I J H : Type u} (i : I) : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) :=
  FreeLieAlgebra.of ℂ (.inr (.inr (.inl i)))
noncomputable def L {I J H : Type u} (j : J) (n : ℤ) : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) :=
  FreeLieAlgebra.of ℂ (.inr (.inr (.inr (j, n))))

noncomputable def presentationRelations {I J H V : Type u} [AddCommGroup H]
    [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (F : EnhancedCartanData I J H V) : Set ((FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))) :=
  {z | (∃ a b : H, z = h (a + b) - h a - h b) ∨
    (∃ (a : H) (c : ℂ), z = h (c • a) - c • h a) ∨
    (∃ a b : H, z = ⁅(h a : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), h b⁆) ∨
    (∃ (a : H) (i : I), z = ⁅(h a : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), e i⁆ - F.pairing a (F.root i) • e i) ∨
    (∃ (a : H) (i : I), z = ⁅(h a : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), f i⁆ + F.pairing a (F.root i) • f i) ∨
    (∃ i k : I, z = ⁅(e i : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), f k⁆ - (if i = k then h (F.coroot i) else 0)) ∨
    (∃ (a : H) (j : J) (n : ℤ),
      z = ⁅(h a : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), L j n⁆ - ((n : ℂ) * F.pairing a (F.virRoot j)) • L j n) ∨
    (∃ (j : J) (n m : ℤ), z = ⁅(L j n : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), L j m⁆ - ((n - m : ℤ) : ℂ) • L j (n + m) -
      (if n = -m then ((n^3 - n : ℤ) : ℂ) • h (F.central j) else 0)) ∨
    (∃ j : J, z = L j 0 - h (F.degree j)) ∨
    (∃ (j k : J) (n m : ℤ), j ≠ k ∧ n * m < 0 ∧ z = ⁅(L j n : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), L k m⁆) ∨
    (∃ (i : I) (j : J) (n : ℤ), n < 0 ∧ z = ⁅(e i : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), L j n⁆) ∨
    (∃ (i : I) (j : J) (n : ℤ), 0 < n ∧ z = ⁅(f i : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))), L j n⁆)}

noncomputable def presentationIdeal {I J H V : Type u} [AddCommGroup H]
    [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (F : EnhancedCartanData I J H V) : LieIdeal ℂ ((FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))) :=
  LieSubmodule.lieSpan ℂ ((FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))))) (presentationRelations F)

abbrev Presented {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) :=
  (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) ⧸ presentationIdeal F

noncomputable def ph {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (a : H) : Presented F :=
  Submodule.Quotient.mk (h a)
noncomputable def pe {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (i : I) : Presented F :=
  Submodule.Quotient.mk (e i)
noncomputable def pf {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (i : I) : Presented F :=
  Submodule.Quotient.mk (f i)
noncomputable def pL {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (j : J) (n : ℤ) : Presented F :=
  Submodule.Quotient.mk (L j n)

noncomputable def cyclic {A : Type u} [LieRing A] [LieAlgebra ℂ A]
    (S : Set A) (w : A) : Submodule ℂ A :=
  (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ A S) ({w} : Set A)).toSubmodule

def HighestProper {A : Type u} [LieRing A] [LieAlgebra ℂ A]
    (S T D : Set A) (w x : A) : Prop :=
  x ≠ 0 ∧ x ∈ cyclic S w ∧ (∀ y ∈ T, ⁅y, x⁆ = 0) ∧
    (∀ y ∈ D, ∃ a : ℂ, ⁅y, x⁆ = a • x) ∧ cyclic S x < cyclic S w

noncomputable def rankOne {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (i : I) : Set (Presented F) :=
  {pe F i, pf F i, ph F (F.coroot i)}
noncomputable def virasoro {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) (j : J) : Set (Presented F) :=
  Set.range (pL F j) ∪ {ph F (F.central j)}

noncomputable def sideSeed {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V)
    (side : Bool) (i : I) : Presented F := if side then pe F i else pf F i

noncomputable def modeSign (side : Bool) : ℤ := if side then 1 else -1

noncomputable def localRelations {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Set (Presented F) :=
  {x | ∃ side : Bool,
    (∃ i k : I, i ≠ k ∧ HighestProper (rankOne F i) {sideSeed F (!side) i} {ph F (F.coroot i)}
      (sideSeed F side k) x) ∨
    (∃ (i : I) (j : J) (n : ℤ), 0 < n ∧
      HighestProper (rankOne F i) {sideSeed F (!side) i} {ph F (F.coroot i)}
        (pL F j (modeSign side * n)) x) ∨
    (∃ (i : I) (j : J), F.pairing (F.central j) (F.root i) = 0 ∧
      F.pairing (F.degree j) (F.root i) = 0 ∧
      (HighestProper (virasoro F j) {y | ∃ n : ℤ, 0 < n ∧ y = pL F j (-modeSign side * n)}
        {ph F (F.degree j), ph F (F.central j)} (sideSeed F side i) x ∨
       ∃ m : ℤ, 0 < m ∧ x = ⁅pL F j (modeSign side * m), sideSeed F side i⁆)) ∨
    (∃ (j k : J) (n : ℤ), j ≠ k ∧ 0 < n ∧
      F.pairing (F.central j) (F.virRoot k) = 0 ∧
      F.pairing (F.degree j) (F.virRoot k) = 0 ∧
      (HighestProper (virasoro F j) {y | ∃ m : ℤ, 0 < m ∧ y = pL F j (-modeSign side * m)}
        {ph F (F.degree j), ph F (F.central j)} (pL F k (modeSign side * n)) x ∨
       ∃ m : ℤ, 0 < m ∧ x = ⁅pL F j (modeSign side * m), pL F k (modeSign side * n)⁆))}

noncomputable def localIdeal {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : LieIdeal ℂ (Presented F) :=
  LieSubmodule.lieSpan ℂ (Presented F) (localRelations F)

abbrev VBKM {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) :=
  Presented F ⧸ localIdeal F

noncomputable def cartanSubspace {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Submodule ℂ (VBKM F) :=
  Submodule.span ℂ (Set.range (fun a : H =>
    (Submodule.Quotient.mk (ph F a) : VBKM F)))

def IdealRigidity {I J H V : Type u} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V] (F : EnhancedCartanData I J H V) : Prop :=
  ∀ K : LieIdeal ℂ (VBKM F), K.toSubmodule ⊓ cartanSubspace F = ⊥ → K = ⊥

end EnhancedCartanData

/-- Universal ideal-rigidity assertion in Conjecture 4.8. Homogeneous nonzero
pairs cover exactly P¹. The s=0 fiber is the specified BKM presentation.
The explicit quotients define the algebras for every datum; no existence
predicate or triangular-decomposition premise is used. -/
def claim : Prop :=
  ∀ (I J H V : Type) [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (F : EnhancedCartanData I J H V),
    F.IsEnhanced → F.Symmetrizable →
    ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) →
      (if s = 0 then (F.heisenberg).IdealRigidity
       else (F.deform s t).Condition43 → (F.deform s t).IdealRigidity)

end D5.S3.VertexAlgebra.Sectors.VBKMPresentation
namespace D5.S3.VertexAlgebra.Sectors.VBKMPresentation
open EnhancedCartanData

private theorem finite_nat_weight_fiber {A : Type*} (w : A → ℕ)
    (hw : ∀ a, w a ≠ 0) (hs : ∀ n, Set.Finite {a | w a ≤ n}) (n : ℕ) :
    Set.Finite {m : A →₀ ℕ | Finsupp.weight w m = n} := by
  classical
  let S := (hs n).toFinset
  let bound : A →₀ ℕ := S.sum fun a => Finsupp.single a n
  apply (Set.finite_Iic bound).subset
  intro m hm
  change Finsupp.weight w m = n at hm
  intro a
  by_cases ha : a ∈ S
  · have hma := Finsupp.le_weight w (hw a) m
    have hb : bound a = n := by simp [bound, Finsupp.finsetSum_apply, Finsupp.single_apply, ha]
    simpa [hb, hm] using hma
  · have hma : m a = 0 := by
      by_contra hn
      have hh := Finsupp.le_weight_of_ne_zero' w hn
      have : a ∈ S := by simpa [S, hm] using hh
      exact ha this
    simp [hma]


private theorem finite_decompositions_of_height {A V : Type v}
    [AddCommGroup V] [Module ℂ V] (r : A → V) (height : V →ₗ[ℂ] ℂ)
    (w : A → ℕ) (hw : ∀ a, w a ≠ 0) (hs : ∀ n, Set.Finite {a | w a ≤ n})
    (hr : ∀ a, height (r a) = (w a : ℂ)) :
    FiniteDecompositions r := by
  have hsum (m : A →₀ ℕ) : height ((m.sum fun a n => (n : ℂ) • r a)) = (Finsupp.weight w m : ℂ) := by
    simp [Finsupp.weight_apply, Finsupp.sum, hr, nsmul_eq_mul]
  intro v
  by_cases hv : ∃ m : A →₀ ℕ, (m.sum fun a n => (n : ℂ) • r a) = v
  · obtain ⟨m0,hm0⟩ := hv
    apply (finite_nat_weight_fiber w hw hs (Finsupp.weight w m0)).subset
    intro m hm
    apply Nat.cast_injective (R := ℂ)
    rw [← hsum m, ← hsum m0, hm, hm0]
  · have he : {m : A →₀ ℕ | (m.sum fun a n => (n : ℂ) • r a) = v} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => hv ⟨m,hm⟩
    rw [he]
    exact Set.finite_empty

noncomputable def datum : EnhancedCartanData Bool Unit (ℂ × ℂ) (ℂ × ℂ) where
  pairing := {
    toFun := fun a => {
      toFun := fun v => a.1 * v.1 + a.2 * v.2
      map_add' := by intro v w; dsimp; ring
      map_smul' := by intro c v; dsimp; ring }
    map_add' := by intro a b; apply LinearMap.ext; intro v; dsimp; ring
    map_smul' := by intro c a; apply LinearMap.ext; intro v; dsimp; ring }
  coroot := fun i => if i then (1,0) else (0,1)
  root := fun i => if i then (-4/3,-1) else (-1,-2/3)
  degree := fun _ => (-81/8,105/8)
  central := fun _ => (1,-1)
  virRoot := fun _ => (-1/3,-1/3)


private noncomputable def rootHeight : (ℂ × ℂ) →ₗ[ℂ] ℂ :=
  (-3 : ℂ) • LinearMap.fst ℂ ℂ ℂ

private def simpleWeight : Bool ⊕ (Unit × ℕ+) → ℕ
  | .inl i => if i then 4 else 3
  | .inr (_,n) => n.val

private theorem simple_weight_nonzero (a : Bool ⊕ (Unit × ℕ+)) : simpleWeight a ≠ 0 := by
  rcases a with i | ⟨j,n⟩
  · cases i <;> decide
  · exact Nat.ne_of_gt n.pos

private theorem simple_weight_sublevel_finite (N : ℕ) :
    Set.Finite {a : Bool ⊕ (Unit × ℕ+) | simpleWeight a ≤ N} := by
  let liftMode (k : Fin N) : Bool ⊕ (Unit × ℕ+) := .inr ((),⟨k.val+1,Nat.succ_pos _⟩)
  apply ((Set.finite_range (Sum.inl : Bool → Bool ⊕ (Unit × ℕ+))).union
    (Set.finite_range liftMode)).subset
  intro a ha
  rcases a with i | ⟨j,n⟩
  · exact Or.inl ⟨i,rfl⟩
  · apply Or.inr
    have hn : n.val ≤ N := ha
    refine ⟨⟨n.val-1,by have := n.pos; omega⟩, ?_⟩
    cases j
    apply congrArg Sum.inr
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change n.val - 1 + 1 = n.val
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)

private theorem datum_root_finite : FiniteDecompositions datum.root := by
  apply finite_decompositions_of_height datum.root rootHeight (fun i => if i then 4 else 3)
  · intro i; cases i <;> decide
  · intro N; exact Set.toFinite _
  · intro i; cases i <;> norm_num [datum,rootHeight]

private theorem datum_simpleRoot_finite : FiniteDecompositions datum.simpleRoot := by
  apply finite_decompositions_of_height datum.simpleRoot rootHeight simpleWeight
    simple_weight_nonzero simple_weight_sublevel_finite
  intro a
  rcases a with i | ⟨j,n⟩
  · cases i <;> norm_num [datum,simpleRoot,rootHeight,simpleWeight]
  · simp [datum,simpleRoot,rootHeight,simpleWeight]
    ring

private theorem datum_no_positive (i : Bool) : ¬ PositiveReal (datum.matrix i i) := by
  rintro ⟨r,hr,he⟩
  have hh := congrArg Complex.re he
  cases i <;> norm_num [datum, matrix] at hh <;> linarith

theorem datum_symmetrizable : datum.Symmetrizable := by
  refine ⟨LinearEquiv.refl ℂ _, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp
  · intro j; simp
  · intro j; simp
  · intro i k; cases i <;> cases k <;> norm_num [datum]
  · intro i j; cases i <;> norm_num [datum]
  · intro j k; cases j; cases k; rfl

theorem datum_condition43 : datum.Condition43 := by
  constructor
  · intro i j; cases i <;> norm_num [datum]
  · intro j k h; exact (h (Subsingleton.elim _ _)).elim

private theorem datum_coroot_span : Submodule.span ℂ (Set.range datum.coroot) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro a
  have h1 : (1,0) ∈ Submodule.span ℂ (Set.range datum.coroot) :=
    Submodule.subset_span ⟨true,rfl⟩
  have h2 : (0,1) ∈ Submodule.span ℂ (Set.range datum.coroot) :=
    Submodule.subset_span ⟨false,rfl⟩
  have h := Submodule.add_mem _ (Submodule.smul_mem _ a.1 h1)
    (Submodule.smul_mem _ a.2 h2)
  simpa using h


theorem datum_enhanced : datum.IsEnhanced := by
  refine ⟨?_, ?_, ?_, datum_simpleRoot_finite, ?_, ?_, ?_, ?_⟩
  · refine ⟨datum_coroot_span, ?_, ?_, datum_root_finite⟩
    · intro i k hik hp; exact (datum_no_positive i hp).elim
    · intro i k; cases i <;> cases k <;> norm_num [datum,matrix]
  · intro j; norm_num [datum]
  · intro i j hp; exact (datum_no_positive i hp).elim
  · intro i j; cases i <;> norm_num [datum]
  · intro j k; cases j; cases k; rfl
  · intro i j hz; cases i <;> norm_num [datum] at hz
  · intro j k h; exact (h (Subsingleton.elim _ _)).elim


end D5.S3.VertexAlgebra.Sectors.VBKMPresentation
namespace D5.S3.VertexAlgebra.Sectors.VBKMPresentation.EnhancedCartanData

attribute [local instance] Classical.propDecidable

variable {I J H V : Type u} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]

noncomputable def presentationMap (F : EnhancedCartanData I J H V) :
    (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) →ₗ⁅ℂ⁆ Presented F :=
  { (presentationIdeal F).toSubmodule.mkQ with
    map_lie' := fun {a b} => LieSubmodule.Quotient.mk_bracket (presentationIdeal F) a b }

private theorem relation_vanishes (F : EnhancedCartanData I J H V) (z : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))))
    (hz : z ∈ presentationRelations F) : presentationMap F z = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan hz)

theorem ph_commute (F : EnhancedCartanData I J H V) (a b : H) :
    ⁅ph F a,ph F b⁆ = 0 := by
  have hz := relation_vanishes F ⁅h a,h b⁆ (by
    right; right; left; exact ⟨a,b,rfl⟩)
  change ⁅presentationMap F (h a), presentationMap F (h b)⁆ = 0
  simpa only [LieHom.map_lie] using hz

theorem ph_pe (F : EnhancedCartanData I J H V) (a : H) (i : I) :
    ⁅ph F a,pe F i⁆ = F.pairing a (F.root i) • pe F i := by
  apply sub_eq_zero.mp
  have hz := relation_vanishes F (⁅h a,e i⁆ - F.pairing a (F.root i) • e i) (by
    right; right; right; left; exact ⟨a,i,rfl⟩)
  change ⁅presentationMap F (h a), presentationMap F (e i)⁆ - F.pairing a (F.root i) • presentationMap F (e i) = 0
  simpa only [map_sub,map_smul,LieHom.map_lie] using hz

theorem ph_pf (F : EnhancedCartanData I J H V) (a : H) (i : I) :
    ⁅ph F a,pf F i⁆ = -(F.pairing a (F.root i) • pf F i) := by
  apply eq_neg_iff_add_eq_zero.mpr
  have hz := relation_vanishes F (⁅h a,f i⁆ + F.pairing a (F.root i) • f i) (by
    right; right; right; right; left; exact ⟨a,i,rfl⟩)
  change ⁅presentationMap F (h a), presentationMap F (f i)⁆ + F.pairing a (F.root i) • presentationMap F (f i) = 0
  simpa only [map_add,map_smul,LieHom.map_lie] using hz

theorem pe_pf (F : EnhancedCartanData I J H V) (i k : I) :
    ⁅pe F i,pf F k⁆ = if i=k then ph F (F.coroot i) else 0 := by
  classical
  apply sub_eq_zero.mp
  have hz := relation_vanishes F (⁅e i,f k⁆ - if i=k then h (F.coroot i) else 0) (by
    right; right; right; right; right; left; exact ⟨i,k,rfl⟩)
  classical
  change ⁅presentationMap F (e i), presentationMap F (f k)⁆ - (if i = k then presentationMap F (h (F.coroot i)) else 0) = 0
  simpa only [map_sub,apply_ite,map_zero,LieHom.map_lie] using hz

theorem ph_pL (F : EnhancedCartanData I J H V) (a : H) (j : J) (n : ℤ) :
    ⁅ph F a,pL F j n⁆ = ((n : ℂ) * F.pairing a (F.virRoot j)) • pL F j n := by
  apply sub_eq_zero.mp
  have hz := relation_vanishes F
    (⁅h a,L j n⁆ - ((n : ℂ)*F.pairing a (F.virRoot j)) • L j n) (by
    right; right; right; right; right; right; left; exact ⟨a,j,n,rfl⟩)
  change ⁅presentationMap F (h a), presentationMap F (L j n)⁆ - ((n : ℂ) * F.pairing a (F.virRoot j)) • presentationMap F (L j n) = 0
  simpa only [map_sub,map_smul,LieHom.map_lie] using hz

theorem pL_commute (F : EnhancedCartanData I J H V) (j : J) (n m : ℤ) :
    ⁅pL F j n,pL F j m⁆ = ((n-m : ℤ) : ℂ) • pL F j (n+m) +
      if n = -m then ((n^3-n : ℤ) : ℂ) • ph F (F.central j) else 0 := by
  have hz := relation_vanishes F
    (⁅L j n,L j m⁆ - ((n-m : ℤ) : ℂ) • L j (n+m) -
      if n = -m then ((n^3-n : ℤ) : ℂ) • h (F.central j) else 0) (by
    right; right; right; right; right; right; right; left; exact ⟨j,n,m,rfl⟩)
  have hh : (⁅pL F j n,pL F j m⁆ - ((n-m : ℤ) : ℂ) • pL F j (n+m)) -
      (if n = -m then ((n^3-n : ℤ) : ℂ) • ph F (F.central j) else 0) = 0 := by
    change (⁅presentationMap F (L j n), presentationMap F (L j m)⁆ - ((n-m : ℤ) : ℂ) • presentationMap F (L j (n+m))) - (if n = -m then ((n^3-n : ℤ) : ℂ) • presentationMap F (h (F.central j)) else 0) = 0
    simpa only [map_sub,map_smul,apply_ite,map_zero,LieHom.map_lie] using hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hh)).trans (add_comm _ _)

theorem pL_zero (F : EnhancedCartanData I J H V) (j : J) :
    pL F j 0 = ph F (F.degree j) := by
  apply sub_eq_zero.mp
  have hz := relation_vanishes F (L j 0 - h (F.degree j)) (by
    right; right; right; right; right; right; right; right; left; exact ⟨j,rfl⟩)
  change presentationMap F (L j 0) - presentationMap F (h (F.degree j)) = 0
  simpa only [map_sub] using hz

theorem pe_negative (F : EnhancedCartanData I J H V) (i : I) (j : J) (n : ℤ)
    (hn : n < 0) : ⁅pe F i,pL F j n⁆ = 0 := by
  have hz := relation_vanishes F ⁅e i,L j n⁆ (by
    right; right; right; right; right; right; right; right; right; right; left
    exact ⟨i,j,n,hn,rfl⟩)
  change ⁅presentationMap F (e i), presentationMap F (L j n)⁆ = 0
  simpa only [LieHom.map_lie] using hz

theorem pf_positive (F : EnhancedCartanData I J H V) (i : I) (j : J) (n : ℤ)
    (hn : 0 < n) : ⁅pf F i,pL F j n⁆ = 0 := by
  have hz := relation_vanishes F ⁅f i,L j n⁆ (by
    right; right; right; right; right; right; right; right; right; right; right
    exact ⟨i,j,n,hn,rfl⟩)
  change ⁅presentationMap F (f i), presentationMap F (L j n)⁆ = 0
  simpa only [LieHom.map_lie] using hz

theorem presentation_generates (F : EnhancedCartanData I J H V)
    (G : Set (Presented F))
    (hG : ∀ g : (H ⊕ (I ⊕ (I ⊕ (J × ℤ)))), presentationMap F (FreeLieAlgebra.of ℂ g) ∈
      LieSubalgebra.lieSpan ℂ (Presented F) G) :
    LieSubalgebra.lieSpan ℂ (Presented F) G = ⊤ := by
  let S := LieSubalgebra.lieSpan ℂ (Presented F) G
  let ψ : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) →ₗ⁅ℂ⁆ S := FreeLieAlgebra.lift ℂ (fun g => ⟨_,hG g⟩)
  have heq : S.incl.comp ψ = presentationMap F := by
    apply FreeLieAlgebra.hom_ext
    intro g
    simp [ψ,LieHom.comp_apply]
  apply top_unique
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hmem := (ψ y).property
    have hh := congrArg (fun f : (FreeLieAlgebra ℂ (H ⊕ (I ⊕ (I ⊕ (J × ℤ))))) →ₗ⁅ℂ⁆ Presented F => f y) heq
    change (ψ y : Presented F) = _ at hh
    change presentationMap F y ∈ S
    rwa [← hh]


end D5.S3.VertexAlgebra.Sectors.VBKMPresentation.EnhancedCartanData
