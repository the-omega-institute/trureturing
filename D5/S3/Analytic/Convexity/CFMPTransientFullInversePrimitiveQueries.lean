import D5.S3.Analytic.Convexity.CFMPTransientFullInversePrimitive
import D5.S3.Analytic.Convexity.CFMPTransientFullInversePrimitiveSanity

/-!
UNEXECUTED query source for the parent-owned independent validation.
Target: Lean v4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Importing OpenImageAudit uses its original-owner lookup and guard. The owner's
private identities, import metadata, and source pins are queried there already.
Do not substitute a different owner or treat search-path candidates as loaded
artifact attestations. Record actual loaded artifacts independently.
-/

set_option pp.universes true
set_option pp.explicit true

-- The exact four supplier interfaces, with the B2 projection made literal.
#check @CFMP133_SourceOnly.bridge
#check (CFMP133_SourceOnly.bridge (E := ℝ)).2.2
#check @CFMPInverseAE.ae_symmetric_derivative_of_finite_exceptional_values
#check @LocalWeakPoincare.exists_local_normalized_primitive
#check @CFMP137Transient.exists_global_primitive_of_homeomorph

-- Actual source-read subtype, continuity, metric, and volume interfaces.
#check @ContinuousOn.domRestrict
#check @Continuous.congr
#check @Continuous.subtype_mk
#check @Subtype.coe_eta
#check @Homeomorph.mk
#check @Homeomorph.symm
#check @LipschitzWith.continuous
#check @LipschitzWith.dist_le_mul
#check @LipschitzOnWith.of_dist_le_mul
#check @Subtype.dist_eq
#check @lipschitzOnWith_iff_restrict
#check @measureSpaceOfInnerProductSpace

section CanonicalVolumeQuery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
#synth MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)
end CanonicalVolumeQuery

-- General telescopes and future axiom/acceptance review, not results of this attempt.
#check @CFMP144Transient.exists_full_inverse_primitive
#print CFMP144Transient.exists_full_inverse_primitive
#check @CFMP144Transient.original_homeomorph_primitive
#print CFMP144Transient.original_homeomorph_primitive
#check @CFMP144Transient.sanity_emptyD
#check @CFMP144Transient.sanity_dimension0
#check @CFMP144Transient.sanity_original_setting

#print axioms CFMP133_SourceOnly.bridge
#print axioms CFMPInverseAE.ae_symmetric_derivative_of_finite_exceptional_values
#print axioms LocalWeakPoincare.exists_local_normalized_primitive
#print axioms CFMP137Transient.exists_global_primitive_of_homeomorph
#print axioms CFMP144Transient.exists_full_inverse_primitive
#print axioms CFMP144Transient.original_homeomorph_primitive
#print axioms CFMP144Transient.sanity_emptyD
#print axioms CFMP144Transient.sanity_dimension0
#print axioms CFMP144Transient.sanity_original_setting
