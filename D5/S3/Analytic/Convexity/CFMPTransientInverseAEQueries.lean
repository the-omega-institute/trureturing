import D5.S3.Analytic.Convexity.CFMPTransientInverseAE
import D5.S3.Analytic.Convexity.CFMPTransientInverseAESanity

/-!
UNEXECUTED parent-side supplier, telescope, instance, and axiom queries.
Do not interpret this source file as elaboration or axiom evidence.
Local candidate modules must be resolved from this attempt, without canonical installation.
-/

open MeasureTheory MeasureTheory.Measure

#check @ApproximatesLinearOn.norm_fderiv_sub_le
#check @measurableSet_of_differentiableAt
#check @LipschitzOnWith.ae_differentiableWithinAt
#check @DifferentiableWithinAt.differentiableAt
#check @DifferentiableAt.hasFDerivAt
#check @HasFDerivAt.hasFDerivWithinAt
#check @continuousOn_iff_isClosed
#check @ae_restrict_iff'
#check @ae_restrict_mem
#check @ae_restrict_of_ae
#check @MeasureTheory.Measure.restrict_congr_set
#check @Filter.eventually_all_finite
#check @HasFDerivAt.add
#check @HasFDerivAt.comp
#check @HasFDerivAt.congr_of_eventuallyEq
#check @HasFDerivAt.unique
#check @hasFDerivAt_id
#check @FiniteDimensional.proper_real
#check @complete_of_proper
#check @measureSpaceOfInnerProductSpace

section Instances
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
#synth CompleteSpace E
#synth MeasureSpace E
#synth IsAddHaarMeasure (volume : Measure E)
end Instances

#check @CFMPInverseAE.measurableSet_affine_fiber
#check @CFMPInverseAE.ae_hasFDerivAt_id_of_affineOn
#check @CFMPInverseAE.symmetric_of_symmetric_right_inverse
#check @CFMPInverseAE.ae_symmetric_derivative_of_finite_exceptional_values
#check @CFMPInverseAE.original_inverse_ae_symmetric_derivative
#check @CFMPInverseAE.sanity_all_good
#check @CFMPInverseAE.sanity_all_targets_exceptional
#check @CFMPInverseAE.sanity_empty_target
#check @CFMPInverseAE.sanity_zero_dimension_K_zero

#print axioms ApproximatesLinearOn.norm_fderiv_sub_le
#print axioms measurableSet_of_differentiableAt
#print axioms LipschitzOnWith.ae_differentiableWithinAt
#print axioms continuousOn_iff_isClosed
#print axioms MeasureTheory.Measure.restrict_congr_set
#print axioms HasFDerivAt.comp
#print axioms HasFDerivAt.unique
#print axioms CFMPInverseAE.measurableSet_affine_fiber
#print axioms CFMPInverseAE.ae_hasFDerivAt_id_of_affineOn
#print axioms CFMPInverseAE.symmetric_of_symmetric_right_inverse
#print axioms CFMPInverseAE.ae_symmetric_derivative_of_finite_exceptional_values
#print axioms CFMPInverseAE.original_inverse_ae_symmetric_derivative
#print axioms CFMPInverseAE.sanity_all_good
#print axioms CFMPInverseAE.sanity_all_targets_exceptional
#print axioms CFMPInverseAE.sanity_empty_target
#print axioms CFMPInverseAE.sanity_zero_dimension_K_zero
