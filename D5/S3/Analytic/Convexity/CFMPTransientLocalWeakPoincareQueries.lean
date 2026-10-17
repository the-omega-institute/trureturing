import D5.S3.Analytic.Convexity.CFMPTransientLocalWeakPoincare
import D5.S3.Analytic.Convexity.CFMPTransientLocalWeakPoincareSanity

/-! Future Mac-only query file. No output from these queries is supplied. -/

#print LocalWeakPoincare.exists_local_normalized_primitive
#check @LipschitzOnWith.extend_finite_dimension
#check @LocalWeakPoincare.mollify_lineDeriv
#check @LocalWeakPoincare.mollify_symmetric
#check @LocalWeakPoincare.segment_add_of_ae_symmetric
#check @LocalWeakPoincare.exists_local_normalized_primitive

#print axioms LipschitzOnWith.extend_finite_dimension
#print axioms LocalWeakPoincare.transfer_ae_actual_derivatives
#print axioms LocalWeakPoincare.mollify
#print axioms LocalWeakPoincare.contDiff_mollify
#print axioms LocalWeakPoincare.mollify_lineDeriv
#print axioms LocalWeakPoincare.mollify_symmetric
#print axioms LocalWeakPoincare.shrinkingBump
#print axioms LocalWeakPoincare.shrinkingBump_rOut_le
#print axioms LocalWeakPoincare.shrinkingBump_rOut_tendsto
#print axioms LocalWeakPoincare.sampling_support_subset_ball
#print axioms LocalWeakPoincare.norm_mollify_sub_le
#print axioms LocalWeakPoincare.curveIntegrable_segment_of_continuous
#print axioms LocalWeakPoincare.segment_integral_error
#print axioms LocalWeakPoincare.tendsto_segment_mollify
#print axioms LocalWeakPoincare.segment_add_of_ae_symmetric
#print axioms LocalWeakPoincare.exists_local_normalized_primitive

#print axioms LocalWeakPoincareSanity.real_clm_symmetric
#print axioms LocalWeakPoincareSanity.norm_field_at_zero
#print axioms LocalWeakPoincareSanity.zero_lipschitz_disconnected
#print axioms LocalWeakPoincareSanity.dimension_zero
