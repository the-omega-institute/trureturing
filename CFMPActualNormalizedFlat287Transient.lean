import CFMPActualFlatVolume286Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualExtendedAngle268Transient
open CFMPActualPositivePrimitive279Transient
open CFMPActualPrimitiveCalibration267Transient (normalizedPrimitive)
open CFMPActualAnalyticDiscriminant280Transient
open CFMPActualLineAngleDerivative283Transient (positive_discriminant_flat_eventually)
open CFMPFiniteExceptionMonotone282Transient (monotoneOn_of_nonneg_derivative_off_finite)
open CFMPActualPositiveConvex284Transient (positive_C1_convex_actual_extension)
open CFMPActualPositiveVolume285Transient (lengthGram_continuous)
open CFMPActualFlatVolume286Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Sector)

namespace CFMPActualNormalizedFlat287Transient

theorem referenceCovolume_hasFDerivAt_off_discriminant
    (p : Lengths) (hp : p ∈ positiveLengths) (hd : discriminant p ≠ 0) :
    HasFDerivAt referenceCovolume (sourceDifferential p) p := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hg := (genuine_iff_discriminant_neg p hp).mpr hneg
    apply ((physicalCovolume_contDiffOn_genuine wholeFamily wholeFamily_realized).2 p hg).congr_of_eventuallyEq
    filter_upwards [genuine_open.mem_nhds hg] with a ha
    exact referenceCovolume_eq_actual wholeFamily wholeFamily_realized a ha
  · obtain ⟨k,hk⟩ := positive_discriminant_flat_eventually p hp hpos
    have hdet : 0 < (lengthGram p).det := by
      rwa [lengthGram_det_eq_discriminant p hp]
    have hnear := lengthGram_continuous.matrix_det.continuousAt.eventually (Ioi_mem_nhds hdet)
    have heq : referenceCovolume =ᶠ[𝓝 p] flatPrimitive k := by
      filter_upwards [positiveLengths_open.mem_nhds hp,hnear,hk] with a ha hd' hka
      have hδ : 0 ≤ discriminant a := by
        rw [← lengthGram_det_eq_discriminant a ha]
        exact hd'.le
      rw [referenceCovolume_eq_covector_at_nonnegative_discriminant a ha hδ,hka]
      simp [flatDifferential,flatPrimitive]
      ring
    rw [hk.self_of_nhds]
    exact (flatPrimitive_hasFDerivAt k p).congr_of_eventuallyEq heq

set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine starting point excludes the identically-zero line restriction.
Finite exceptional interfaces suffice to determine the whole positive-domain primitive. -/
theorem primitive_matches_reference
    (F : Lengths → ℝ)
    (hF : ∀ p ∈ positiveLengths, HasFDerivAt F (sourceDifferential p) p)
    (a0 : Lengths) (ha0 : genuine a0) (h0 : F a0 = referenceCovolume a0) :
    Set.EqOn F referenceCovolume positiveLengths := by
  intro a ha
  have hfinite : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ lineDiscriminant a0 a t = 0}.Finite := by
    rcases lineDiscriminant_zero_or_finite a0 a 0 1 with hz | hf
    · have hn := (genuine_iff_discriminant_neg a0 ha0.1).mp ha0
      have hzero : discriminant a0 = 0 := by
        simpa only [lineDiscriminant,AffineMap.lineMap_apply_zero] using hz 0
      exact False.elim ((ne_of_lt hn) hzero)
    · exact hf
  let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ lineDiscriminant a0 a t = 0}
  let f : ℝ → ℝ := fun t =>
    F (AffineMap.lineMap a0 a t) - referenceCovolume (AffineMap.lineMap a0 a t)
  have hpositive (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap a0 a t ∈ positiveLengths :=
    positiveLengths_convex.lineMap_mem ha0.1 ha ht
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro t ht
    have hp := hpositive t ht
    exact (((hF _ hp).continuousAt.comp AffineMap.lineMap_continuous.continuousAt).sub
      ((referenceCovolume_continuousAt _ hp).comp
        AffineMap.lineMap_continuous.continuousAt)).continuousWithinAt
  have hD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hts : t ∉ S) : HasDerivAt f 0 t := by
    have hp := hpositive t (Ioo_subset_Icc_self ht)
    have hne : discriminant (AffineMap.lineMap a0 a t) ≠ 0 := by
      intro hz
      exact hts ⟨Ioo_subset_Icc_self ht,hz⟩
    have hleft := (hF _ hp).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    have hright := (referenceCovolume_hasFDerivAt_off_discriminant _ hp hne).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
    simpa only [f,Function.comp_def,sub_self] using hleft.fun_sub hright
  have hmono : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_nonneg_derivative_off_finite S hfinite f 0 1 hc
      (fun t ht hts => ⟨0,hD t ht hts,le_rfl⟩)
  have hneg : MonotoneOn (fun t => -f t) (Icc (0 : ℝ) 1) :=
    monotoneOn_of_nonneg_derivative_off_finite S hfinite (fun t => -f t) 0 1 hc.neg
      (fun t ht hts => ⟨0,by
        simpa only [neg_zero] using (hD t ht hts).fun_neg,le_rfl⟩)
  have h01 : f 0 ≤ f 1 := hmono ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one
  have h10 : -f 0 ≤ -f 1 := hneg ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one
  have hz : f 0 = 0 := by simp only [f,AffineMap.lineMap_apply_zero,h0,sub_self]
  have he : f 1 = 0 := by linarith
  simpa only [f,AffineMap.lineMap_apply_one,sub_eq_zero] using he

theorem calibrated_primitive_eq_reference (a0 : Lengths) (ha0 : genuine a0) :
    Set.EqOn (normalizedPrimitive (positivePrimitive a0) a0)
      referenceCovolume positiveLengths := by
  have h := positive_C1_convex_actual_extension a0 ha0
  apply primitive_matches_reference _ h.2.2.1 a0 ha0
  exact (h.2.2.2 wholeFamily wholeFamily_realized ha0).trans
    (referenceCovolume_eq_actual wholeFamily wholeFamily_realized a0 ha0).symm

/-- This is the same physical covolume on genuine lengths and the exact native
flat affine value on every positive flat sector. -/
theorem actual_zero_flat_C1_convex_extension (a0 : Lengths) (ha0 : genuine a0) :
    ContDiffOn ℝ 1 referenceCovolume positiveLengths ∧
      ConvexOn ℝ positiveLengths referenceCovolume ∧
      (∀ a ∈ positiveLengths, HasFDerivAt referenceCovolume (sourceDifferential a) a) ∧
      (∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn referenceCovolume (physicalCovolume G) {a | genuine a}) ∧
      ∀ a ∈ positiveLengths, ∀ k : Fin 3,
        Sector (fun q => Real.cosh (a q)) k → referenceCovolume a = flatPrimitive k a := by
  have h := positive_C1_convex_actual_extension a0 ha0
  have heq := calibrated_primitive_eq_reference a0 ha0
  refine ⟨h.1.congr (fun a ha => (heq ha).symm),h.2.1.congr heq,?_,?_,?_⟩
  · intro a ha
    apply (h.2.2.1 a ha).congr_of_eventuallyEq
    filter_upwards [positiveLengths_open.mem_nhds ha] with b hb
    exact (heq hb).symm
  · intro G hG a ha
    exact referenceCovolume_eq_actual G hG a ha
  · exact fun a ha k hk => referenceCovolume_eq_flat a ha k hk

end CFMPActualNormalizedFlat287Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualNormalizedFlat287Transient.primitive_matches_reference,
      ``CFMPActualNormalizedFlat287Transient.calibrated_primitive_eq_reference,
      ``CFMPActualNormalizedFlat287Transient.actual_zero_flat_C1_convex_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP287 actual zero-flat C1 convex extension absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP287 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP287 CHECKED {name} axioms={axioms}"
