import D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover

/-!
# Faithful source reception for the neighborhood-cover owner

This mirror preserves the complete public theorem telescope by binding each
retained public theorem to its receiving declaration. It deliberately stops
before a four-slot registration: no enrolled template currently provides the
strict arbitrary-neighborhood-cover functor family together with the live
homotopy-invariant readout, whole-family variation, sensitivity and
observational-dependence evidence. These source bindings are therefore an
unfinished audit attempt, not a validated registration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover

abbrev lebesgue_scope.{u,v} := type_of% (@_root_.TauCeti.lebesgue_number_lemma_of_metric_of_mem_nhds.{u,v})
theorem lebesgue_source.{u,v} : lebesgue_scope.{u,v} := @_root_.TauCeti.lebesgue_number_lemma_of_metric_of_mem_nhds.{u,v}

abbrev cast_scope.{u} := type_of% (@_root_.Path.Homotopic.Quotient.cast_mem_arrows_iff.{u})
theorem cast_source.{u} : cast_scope.{u} := @_root_.Path.Homotopic.Quotient.cast_mem_arrows_iff.{u}

abbrev injective_scope.{u,v} := type_of% (@_root_.ContinuousMap.fundamentalGroupoid_map_obj_injective.{u,v})
theorem injective_source.{u,v} : injective_scope.{u,v} := @_root_.ContinuousMap.fundamentalGroupoid_map_obj_injective.{u,v}

abbrev index_singleton_scope.{u} := type_of% (@_root_.TauCeti.TopCat.CechIndex.coe_singleton.{u})
theorem index_singleton_source.{u} : index_singleton_scope.{u} := @_root_.TauCeti.TopCat.CechIndex.coe_singleton.{u}

abbrev index_order_scope.{u} := type_of% (@_root_.TauCeti.TopCat.CechIndex.le_iff.{u})
theorem index_order_source.{u} : index_order_scope.{u} := @_root_.TauCeti.TopCat.CechIndex.le_iff.{u}

abbrev intersection_mem_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.mem_cechIntersection.{u,v})
theorem intersection_mem_source.{u,v} : intersection_mem_scope.{u,v} := @_root_.TauCeti.TopCat.mem_cechIntersection.{u,v}

abbrev intersection_singleton_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechIntersection_singleton.{u,v})
theorem intersection_singleton_source.{u,v} : intersection_singleton_scope.{u,v} := @_root_.TauCeti.TopCat.cechIntersection_singleton.{u,v}

abbrev intersection_mono_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechIntersection_mono.{u,v})
theorem intersection_mono_source.{u,v} : intersection_mono_scope.{u,v} := @_root_.TauCeti.TopCat.cechIntersection_mono.{u,v}

abbrev open_obj_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechOpenDiagram_obj.{u,v})
theorem open_obj_source.{u,v} : open_obj_scope.{u,v} := @_root_.TauCeti.TopCat.cechOpenDiagram_obj.{u,v}

abbrev open_map_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechOpenDiagram_map.{u,v})
theorem open_map_source.{u,v} : open_map_scope.{u,v} := @_root_.TauCeti.TopCat.cechOpenDiagram_map.{u,v}

abbrev top_obj_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechTopDiagram_obj.{u,v})
theorem top_obj_source.{u,v} : top_obj_scope.{u,v} := @_root_.TauCeti.TopCat.cechTopDiagram_obj.{u,v}

abbrev top_map_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechTopDiagram_map_apply.{u,v})
theorem top_map_source.{u,v} : top_map_scope.{u,v} := @_root_.TauCeti.TopCat.cechTopDiagram_map_apply.{u,v}

abbrev inclusion_apply_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechInclusion_apply.{u,v})
theorem inclusion_apply_source.{u,v} : inclusion_apply_scope.{u,v} := @_root_.TauCeti.TopCat.cechInclusion_apply.{u,v}

abbrev inclusion_naturality_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechTopDiagram_map_comp_inclusion.{u,v})
theorem inclusion_naturality_source.{u,v} : inclusion_naturality_scope.{u,v} := @_root_.TauCeti.TopCat.cechTopDiagram_map_comp_inclusion.{u,v}

abbrev inclusion_app_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.cechInclusionNatTrans_app.{u,v})
theorem inclusion_app_source.{u,v} : inclusion_app_scope.{u,v} := @_root_.TauCeti.TopCat.cechInclusionNatTrans_app.{u,v}

abbrev singleton_cover_scope.{u,v} := type_of% (@_root_.TauCeti.TopCat.exists_mem_cechIntersection_singleton.{u,v})
theorem singleton_cover_source.{u,v} : singleton_cover_scope.{u,v} := @_root_.TauCeti.TopCat.exists_mem_cechIntersection_singleton.{u,v}

abbrev supremum_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top.{u,v})
theorem supremum_source.{u,v} : supremum_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top.{u,v}

abbrev functor_ext_scope.{u,v,w,z} := type_of% (@_root_.TauCeti.FundamentalGroupoid.functor_ext.{u,v,w,z})
theorem functor_ext_source.{u,v,w,z} : functor_ext_scope.{u,v,w,z} := @_root_.TauCeti.FundamentalGroupoid.functor_ext.{u,v,w,z}

abbrev glue_restriction_scope.{u,v,w,z} := type_of% (@_root_.TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue.{u,v,w,z})
theorem glue_restriction_source.{u,v,w,z} : glue_restriction_scope.{u,v,w,z} := @_root_.TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue.{u,v,w,z}

abbrev glue_unique_scope.{u,v,w,z} := type_of% (@_root_.TauCeti.FundamentalGroupoid.eq_glue.{u,v,w,z})
theorem glue_unique_source.{u,v,w,z} : glue_unique_scope.{u,v,w,z} := @_root_.TauCeti.FundamentalGroupoid.eq_glue.{u,v,w,z}

abbrev extension_scope.{u,v,w,z} := type_of% (@_root_.TauCeti.FundamentalGroupoid.existsUnique_extension.{u,v,w,z})
theorem extension_source.{u,v,w,z} : extension_scope.{u,v,w,z} := @_root_.TauCeti.FundamentalGroupoid.existsUnique_extension.{u,v,w,z}

abbrev cech_diagram_obj_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.cechDiagram_obj.{u,v})
theorem cech_diagram_obj_source.{u,v} : cech_diagram_obj_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.cechDiagram_obj.{u,v}

abbrev cech_diagram_map_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.cechDiagram_map.{u,v})
theorem cech_diagram_map_source.{u,v} : cech_diagram_map_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.cechDiagram_map.{u,v}

abbrev cech_pt_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.cechCocone_pt.{u,v})
theorem cech_pt_source.{u,v} : cech_pt_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.cechCocone_pt.{u,v}

abbrev cech_leg_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.cechCocone_ι_app.{u,v})
theorem cech_leg_source.{u,v} : cech_leg_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.cechCocone_ι_app.{u,v}

abbrev cech_subtype_scope.{u,v} := type_of% (@_root_.TauCeti.FundamentalGroupoid.map_subtypeVal_eq_cechCocone_ι_app.{u,v})
theorem cech_subtype_source.{u,v} : cech_subtype_scope.{u,v} := @_root_.TauCeti.FundamentalGroupoid.map_subtypeVal_eq_cechCocone_ι_app.{u,v}

end Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover
