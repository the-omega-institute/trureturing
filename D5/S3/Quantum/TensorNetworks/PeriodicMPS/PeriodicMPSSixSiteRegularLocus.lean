/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteRegularLocus
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteRegularLocus
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteOrdinaryTrace,
     lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteRegularLocus]
   utility: none
   digest: Analytic continuation on compact six-site fibers avoiding boundary and critical values. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteOrdinaryTrace
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteRegularLocus
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSCompactAnalyticCharts

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteRegularLocus

open Set Filter Function PeriodicMPSSixSiteCompactSource PeriodicMPSSixSiteOrdinaryTrace
  PeriodicMPSSixSiteBoundaryCover PeriodicMPSProjectiveCoordinates PeriodicMPSImmersionPullback
  PeriodicMPSRegularComplement PeriodicMPSCompactAnalyticCharts PeriodicMPSAnalyticBranchSeparation
open PeriodicMPSSixSiteMarginal (flatten gram necklaceTable)
open PeriodicMPSFiveSitePhysicalObservation (Marginal entries)
open scoped Topology ComplexConjugate Matrix.Norms.Elementwise

open private Covered Covered.mono Covered.union Covered.image
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteRegularLocus
open private swapBits symmetricMarginals scale_mem symmetric_eq_of_entries trace_re_mem
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
open private complexCoordinates complexCoordinates_surjective differentiable_complexCoordinates
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover

noncomputable section

abbrev H := Fin 6 → ℝ
abbrev Readings := Fin 9 → ℝ

/-- A subset contained in countably many differentiable images of six real coordinates. -/
abbrev SmoothCover {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Set E) : Prop :=
  Covered A

/-- The nine normalized readings retain raw indices 1 through 9. -/
def readout : Marginal →L[ℝ] Readings :=
  let old (i : Fin 9) : Marginal →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp PeriodicMPSFiveSitePhysicalObservation.readout
  let corner : Marginal →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((ContinuousLinearMap.proj (3 : Fin 4) : (Fin 4 → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (3 : Fin 4) : Marginal →L[ℝ] (Fin 4 → ℂ)))
  ContinuousLinearMap.pi fun i => ![old 1, old 2, old 3, old 4, old 5, old 6,
    old 7, old 8, corner] i

theorem readout_apply (M : Marginal) (i : Fin 9) : readout M i = entries M i.succ := by
  have h (j : Fin 8) : readout M j.castSucc =
      PeriodicMPSFiveSitePhysicalObservation.readout M j.succ := by
    fin_cases j <;> rfl
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rfl
  · rw [h]
    exact PeriodicMPSFiveSitePhysicalObservation.readout_apply M j.succ

private def includeVacuum (v : Readings) : Readings :=
  ![1 - 2 * v 4 - v 8, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]

/-- Inversion on the trace-one Hermitian reflection subspace. -/
def readoutInverse (v : Readings) : Marginal :=
  PeriodicMPSFiveSitePhysicalObservation.readoutInverse (includeVacuum v)

theorem differentiable_readoutInverse : Differentiable ℝ readoutInverse := by
  have h : Differentiable ℝ includeVacuum := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [includeVacuum] <;> fun_prop
  exact PeriodicMPSFiveSitePhysicalObservation.differentiable_readoutInverse.comp h

private def reverseSuffixIndex : Fin 16 → Fin 16 :=
  ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]

private def reverseSuffix : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective reverseSuffixIndex (by decide)

private def reverseNecklace : Fin 14 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11, 12, 13]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem table_reflection (i : Fin 4) (k : Fin 16) :
    necklaceTable (swapBits i) (reverseSuffix k) = reverseNecklace (necklaceTable i k) := by
  change necklaceTable (swapBits i) (reverseSuffixIndex k) = reverseNecklace (necklaceTable i k)
  revert i k
  decide

private theorem gram_symmetric (p : Fin 14 → ℂ) (hp : p 6 = p 7) :
    gram p ∈ symmetricMarginals := by
  have hrev (r : Fin 14) : p (reverseNecklace r) = p r := by
    fin_cases r <;> first | rfl | exact hp | exact hp.symm
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_comm]
  · intro i j
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, flatten]
    rw [← Equiv.sum_comp reverseSuffix
      (fun k => p (necklaceTable (swapBits i) k) * conj (p (necklaceTable (swapBits j) k)))]
    simp only [table_reflection, hrev]

private theorem source_amplitude_rows_eq {x : Ambient} (hx : x ∈ source) (j : Fin 14) :
    x.2 6 j = x.2 7 j := by
  have hc (i : Fin 14) : Continuous (fun p : Ambient => p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  refine closure_minimal (s := range ordinary)
    (t := {z : Ambient | z.2 6 j = z.2 7 j}) ?_ (isClosed_eq (hc 6) (hc 7)) hx
  rintro _ ⟨u, rfl⟩
  have h : amplitude u.val 6 = amplitude u.val 7 := rfl
  change projector (amplitude u.val) 6 j = projector (amplitude u.val) 7 j
  simp only [projector, Matrix.smul_apply, outer, h]

private theorem observation_symmetric {x : Ambient} (hx : x ∈ source) :
    observation x ∈ symmetricMarginals := by
  obtain ⟨p, hmass, houter⟩ := source_amplitude_projective hx
  have hm : mass p = 1 := hmass
  have hp : p ≠ 0 := by
    intro h
    simp [mass, h] at hm
  obtain ⟨j, hj⟩ : ∃ j : Fin 14, p j ≠ 0 := by
    by_contra! h
    exact hp (funext h)
  have he := source_amplitude_rows_eq hx j
  rw [← houter] at he
  have h67 : p 6 = p 7 :=
    mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).2 hj) he
  have hproj : x.2 = projector p := by rw [← houter, projector, hm, inv_one, one_smul]
  rw [observation_of_projector hp hproj, normalizedGram]
  exact scale_mem (gram_symmetric p h67) _

private theorem entries_readoutInverse (v : Readings) :
    entries (readoutInverse v) = Fin.cases (1 - 2 * v 4 - v 8) v := by
  funext i
  fin_cases i <;>
    simp [entries, readoutInverse, PeriodicMPSFiveSitePhysicalObservation.readoutInverse,
      includeVacuum, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re,
      Complex.add_im] <;> try rfl
  change 1 - (1 - 2 * v 4 - v 8) - 2 * v 4 =
    Fin.cases (1 - 2 * v 4 - v 8) v (Fin.succ (8 : Fin 9))
  rw [Fin.cases_succ]
  ring

theorem readoutInverse_readout {x : Ambient} (hx : x ∈ source) :
    readoutInverse (readout (observation x)) = observation x := by
  let M := observation x
  let v := readout M
  have hM := observation_symmetric hx
  have ht : M.trace.re = 1 := by
    simpa only [Complex.one_re] using congrArg Complex.re (observation_trace hx)
  have ht' := trace_re_mem hM
  rw [ht] at ht'
  have hM' : readoutInverse v ∈ symmetricMarginals := by
    refine ⟨?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [readoutInverse, PeriodicMPSFiveSitePhysicalObservation.readoutInverse, map_ofNat]
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [readoutInverse, PeriodicMPSFiveSitePhysicalObservation.readoutInverse, swapBits,
          Equiv.swap_apply_def]
  refine symmetric_eq_of_entries hM' hM ?_
  rw [entries_readoutInverse]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cases_zero]
    change 1 - 2 * readout M 4 - readout M 8 = entries M 0
    rw [readout_apply, readout_apply]
    change 1 - 2 * (M 1 1).re - (M 3 3).re = (M 0 0).re
    linarith
  · exact readout_apply M j

/-- The normalized matrix in the first trace-square chart. -/
def normalizedObservation (q : Parameters) : Marginal := normalizedGram (chartAmplitude q)

/-- The normalized observation in the nine independent readings. -/
def observe (q : Parameters) : Readings := readout (normalizedObservation q)

def onSource (p : source) : Readings := readout (observation p.val)

theorem continuous_onSource : Continuous onSource :=
  readout.continuous.comp continuous_observation

theorem observe_encode (q : domain) : onSource (toSource q) = observe q.val := by
  unfold onSource observe normalizedObservation
  rw [observation_of_projector q.property (show (toSource q).val.2 =
    projector (chartAmplitude q.val) from rfl)]

theorem onSource_eq_iff {p q : source} :
    onSource p = onSource q ↔ observation p.val = observation q.val := by
  constructor
  · intro h
    exact (readoutInverse_readout p.property).symm.trans
      ((congrArg readoutInverse h).trans (readoutInverse_readout q.property))
  · exact congrArg readout

theorem analyticAt_normalizedObservation (q : Parameters) (hq : q ∈ domain) :
    AnalyticAt ℝ normalizedObservation q :=
  PeriodicMPSSixSiteCriticalRank.analyticAt_normalizedObservation q hq

theorem analyticAt_observe (q : Parameters) (hq : q ∈ domain) :
    AnalyticAt ℝ observe q :=
  (readout.analyticAt _).comp (analyticAt_normalizedObservation q hq)

def regular : Set Parameters := {q | q ∈ domain ∧ Injective (fderiv ℝ observe q)}

theorem isOpen_regular : IsOpen regular := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have h₁ : ∀ᶠ x in 𝓝 q, x ∈ domain := isOpen_domain.mem_nhds hq.1
  have h₂ : ∀ᶠ x in 𝓝 q, Injective (fderiv ℝ observe x) :=
    (analyticAt_observe q hq.1).fderiv.continuousAt
      (ContinuousLinearMap.isOpen_injective.mem_nhds hq.2)
  exact h₁.and h₂

theorem kernel_full {q : Parameters} (hq : q ∈ domain) {v : Parameters}
    (hv : fderiv ℝ observe q v = 0) : fderiv ℝ normalizedObservation q v = 0 := by
  have h : normalizedObservation =ᶠ[𝓝 q] readoutInverse ∘ observe := by
    filter_upwards [isOpen_domain.mem_nhds hq] with x hx
    have he := readoutInverse_readout (encode_mem_source hx)
    rw [observation_of_projector (x := encode x) hx rfl] at he
    exact he.symm
  have hd := differentiable_readoutInverse.differentiableAt.hasFDerivAt.comp q
    (analyticAt_observe q hq).differentiableAt.hasFDerivAt
  have hn : HasFDerivAt normalizedObservation
      (fderiv ℝ readoutInverse (observe q) ∘SL fderiv ℝ observe q) q :=
    hd.congr_of_eventuallyEq h
  rw [hn.fderiv, ContinuousLinearMap.comp_apply, hv, map_zero]

theorem regular_of_injective_normalizedObservation {q : Parameters} (hq : q ∈ domain)
    (h : Injective (fderiv ℝ normalizedObservation q)) : q ∈ regular := by
  refine ⟨hq, fun v w hvw => sub_eq_zero.mp (h ?_)⟩
  rw [map_zero]
  apply kernel_full hq
  rw [map_sub, hvw, sub_self]

/-- The critical suppliers must cover the nonimmersive points of the ordinary chart. -/
abbrev CriticalCover : Prop := SmoothCover (domain \ regular)

/-- A full-matrix rank certificate can supply the critical cover via its equation set. -/
theorem criticalCover_of_kernel {C : Set Parameters} (hC : SmoothCover C)
    (hrank : ∀ q ∈ domain, ∀ v : Parameters, v ≠ 0 →
      fderiv ℝ normalizedObservation q v = 0 → q ∈ C) :
    CriticalCover := by
  apply Covered.mono hC
  intro q hq
  have hn : ¬ Injective (fderiv ℝ observe q) := fun h => hq.2 ⟨hq.1, h⟩
  obtain ⟨v, hv, hv0⟩ : ∃ v : Parameters, v ≠ 0 ∧ fderiv ℝ observe q v = 0 := by
    by_contra! he
    exact hn (fun x y hxy => by
      apply sub_eq_zero.mp
      by_contra hne
      exact he (x - y) hne (by rw [map_sub, hxy, sub_self]))
  exact hrank q hq.1 v hv (kernel_full hq.1 hv0)

/-- Compact points represented by regular parameters in the first trace-square chart. -/
def regularSource : Set source := {p | p.val ∈ chartDomain ∧ decode p.val ∈ regular}

theorem isOpen_regularSource : IsOpen regularSource := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have h₁ := (isOpen_chartDomain.preimage continuous_subtype_val).mem_nhds hp.1
  have hc := (continuousAt_decode hp.1.1).comp continuous_subtype_val.continuousAt
  exact inter_mem h₁ (hc (isOpen_regular.mem_nhds hp.2))

/-- The values of all compact lifts outside the regular ordinary chart. -/
def excludedValues : Set Readings := onSource '' regularSourceᶜ

/-- Remove every fiber meeting the boundary or the ordinary critical locus. -/
def good : Set source := onSource ⁻¹' excludedValuesᶜ

theorem isOpen_good : IsOpen good := by
  haveI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  exact (continuous_onSource.isClosedMap _ isOpen_regularSource.isClosed_compl).isOpen_compl.preimage
    continuous_onSource

theorem good_subset_regular : good ⊆ regularSource := by
  intro p hp
  by_contra hn
  exact hp ⟨p, hn, rfl⟩

theorem mem_good_iff {p : source} :
    p ∈ good ↔ ∀ q : source, onSource q = onSource p → q ∈ regularSource := by
  constructor
  · intro hp q hq
    by_contra hn
    exact hp ⟨q, hn, hq⟩
  · rintro h ⟨q, hq, he⟩
    exact hq (h q he)

theorem sameFiber_good {p q : source} (hp : p ∈ good) (hq : onSource q = onSource p) :
    q ∈ good := by
  change onSource q ∉ excludedValues
  rw [hq]
  exact hp

private theorem excluded_covered (hcritical : CriticalCover) : SmoothCover excludedValues := by
  obtain ⟨D, g, hd, hc⟩ := real_boundary_observation_cover
  have hb : SmoothCover (onSource '' {x : source | x.val ∉ chartDomain}) := by
    refine ⟨BoundaryFamily, inferInstance, D, fun i => readout ∘ g i,
      fun i => readout.differentiable.differentiableOn.comp (hd i).2 (mapsTo_univ _ _), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have hboundary := (mem_boundary_iff p.property).mpr hp
    obtain ⟨i, u, hu, he⟩ := mem_iUnion.mp (hc ⟨p.val, hboundary, rfl⟩)
    exact mem_iUnion.mpr ⟨i, u, hu, congrArg readout he⟩
  have hcrit := Covered.image hcritical observe
    (fun q hq => (analyticAt_observe q hq.1).differentiableAt.differentiableWithinAt)
  apply Covered.mono (Covered.union hb hcrit)
  rintro _ ⟨p, hp, rfl⟩
  by_cases hD : p.val ∈ chartDomain
  · right
    let q : domain := ⟨decode p.val, hD.2⟩
    have he : toSource q = p := Subtype.ext (encode_decode p.property hD)
    exact ⟨q.val, ⟨q.property, fun h => hp ⟨hD, h⟩⟩,
      (observe_encode q).symm.trans (congrArg onSource he)⟩
  · exact Or.inl ⟨p, hD, rfl⟩

private theorem base_covered : SmoothCover (domainᶜ : Set Parameters) := by
  let g (p : Fin 3 → ℂ) : Parameters := ![p 0, p 1, p 1 * p 0 ^ 2, p 2]
  have hd : Differentiable ℝ g := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [g] <;> fun_prop
  refine ⟨Unit, inferInstance, fun _ => univ, fun _ => g ∘ complexCoordinates,
    fun _ => (hd.comp differentiable_complexCoordinates).differentiableOn, ?_⟩
  intro q hq
  have hzero : chartAmplitude q = 0 := not_not.mp hq
  rw [chartAmplitude_eq] at hzero
  have he := (PeriodicMPSSixSiteCoordinates.chart_eq_zero_iff.mp hzero).2.1
  obtain ⟨u, hu⟩ := complexCoordinates_surjective (![q 0, q 1, q 3] : Fin 3 → ℂ)
  refine mem_iUnion.mpr ⟨(), u, mem_univ _, ?_⟩
  change g (complexCoordinates u) = q
  rw [hu]
  funext i
  fin_cases i <;> simp [g, ← he]

/-- The good parameters expressed in the full ordinary coordinate space. -/
def goodParameters : Set Parameters := {q | q ∈ domain ∧ observe q ∉ excludedValues}

theorem isOpen_goodParameters : IsOpen goodParameters := by
  refine isOpen_iff_mem_nhds.mpr fun q hq => ?_
  haveI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  have hc : IsClosed excludedValues := continuous_onSource.isClosedMap _
    isOpen_regularSource.isClosed_compl
  exact inter_mem (isOpen_domain.mem_nhds hq.1)
    ((analyticAt_observe q hq.1).continuousAt (hc.isOpen_compl.mem_nhds hq.2))

private theorem goodParameters_compl_covered (hcritical : CriticalCover) :
    SmoothCover goodParametersᶜ := by
  let A := regular ∩ observe ⁻¹' excludedValues
  obtain ⟨ι, hι, D, g, hd, hcover⟩ := excluded_covered hcritical
  have hA : SmoothCover A := cover_regular_preimage A
    (fun q hq => ⟨analyticAt_observe q hq.1.1, hq.1.2⟩) D g hd (by
      rintro _ ⟨q, hq, rfl⟩
      exact hcover hq.2)
  apply Covered.mono (Covered.union (Covered.union base_covered hcritical) hA)
  intro q hq
  by_cases h₀ : q ∈ domain
  · by_cases hr : q ∈ regular
    · exact Or.inr ⟨hr, by
        by_contra hv
        exact hq ⟨h₀, hv⟩⟩
    · exact Or.inl (Or.inr ⟨h₀, hr⟩)
  · exact Or.inl (Or.inl h₀)

theorem pathConnected_and_dense_goodParameters (hcritical : CriticalCover) :
    IsPathConnected goodParameters ∧ Dense goodParameters := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := goodParameters_compl_covered hcritical
  have hcover : ∃ (U : ℕ → Set H) (u : ℕ → H → Parameters),
      (∀ i, DifferentiableOn ℝ (u i) (U i)) ∧ goodParametersᶜ ⊆ ⋃ i, u i '' U i := by
    by_cases hn : Nonempty ι
    · obtain ⟨f, hf⟩ := exists_surjective_nat ι
      refine ⟨D ∘ f, g ∘ f, fun i => hd (f i), ?_⟩
      intro q hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hq)
      obtain ⟨j, rfl⟩ := hf i
      exact mem_iUnion.mpr ⟨j, hi⟩
    · refine ⟨fun _ => ∅, fun _ _ => 0, fun _ => differentiableOn_const 0, ?_⟩
      intro q hq
      obtain ⟨i, _⟩ := mem_iUnion.mp (hc hq)
      exact (hn ⟨i⟩).elim
  obtain ⟨U, u, hu, hcov⟩ := hcover
  have hdim : Module.finrank ℝ Parameters = 8 := by
    simp [Parameters, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hH : Module.finrank ℝ H = 6 := by simp [H, Module.finrank_pi]
  have hp := isPathConnected_compl_of_smooth_cover _ U u hu hcov (by rw [hdim, hH]; decide)
  have hdim' : dimH goodParametersᶜ < Module.finrank ℝ Parameters := by
    apply (dimH_mono hcov).trans_lt
    rw [dimH_iUnion]
    refine (iSup_le fun i => (hu i).dimH_image_le.trans
      ((dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank H))).trans_lt ?_
    rw [hH, hdim]
    norm_num
  exact ⟨by simpa only [compl_compl] using hp,
    by simpa only [compl_compl] using dense_compl_of_dimH_lt_finrank hdim'⟩

private theorem good_image : good = toSource '' (Subtype.val ⁻¹' goodParameters) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hD, hreg⟩ := good_subset_regular hp
    let q : domain := ⟨decode p.val, hreg.1⟩
    have he : toSource q = p := Subtype.ext (encode_decode p.property hD)
    refine ⟨q, ⟨q.property, ?_⟩, he⟩
    rw [← observe_encode q, he]
    exact hp
  · rintro ⟨q, hq, rfl⟩
    change onSource (toSource q) ∉ excludedValues
    rw [observe_encode]
    exact hq.2

theorem isPathConnected_good (hcritical : CriticalCover) : IsPathConnected good := by
  rw [good_image]
  exact ((pathConnected_and_dense_goodParameters hcritical).1.preimage_coe
    (fun _ hq => hq.1)).image continuous_toSource

theorem dense_good (hcritical : CriticalCover) : Dense good := by
  have hd : Dense (Subtype.val ⁻¹' goodParameters : Set domain) :=
    (pathConnected_and_dense_goodParameters hcritical).2.preimage isOpen_domain.isOpenMap_subtype_val
  have hR : (Subtype.val ⁻¹' chartDomain : Set source) ⊆ closure good := by
    intro p hp
    let q : domain := ⟨decode p.val, hp.2⟩
    have he : toSource q = p := Subtype.ext (encode_decode p.property hp)
    rw [good_image]
    exact image_closure_subset_closure_image continuous_toSource ⟨q, hd q, he⟩
  exact fun p => closure_minimal hR isClosed_closure (dense_chartDomain p)

/-- The ordinary chart supplies the local analytic expression on the regular source. -/
theorem regularChart_at (p : source) (hp : p ∈ regularSource) :
    Nonempty (RegularChart (E := Parameters) onSource p) := by
  let V : Set source := Subtype.val ⁻¹' chartDomain
  let hV : IsOpen V := isOpen_chartDomain.preimage continuous_subtype_val
  let h : domain ≃ₜ V := ordinaryHomeomorph.trans
    (interSubtypeHomeomorph source chartDomain).symm
  let hn : Nonempty domain := ⟨⟨decode p.val, hp.2.1⟩⟩
  let c := openSubsetChart isOpen_domain hV hn h
  have hp' : p ∈ c.target := by
    rw [show c.target = V from openSubsetChart_target _ _ _ _]
    exact hp.1
  have hs : c.symm p = decode p.val :=
    openSubsetChart_symm_apply isOpen_domain hV hn h ⟨p, hp.1⟩
  refine ⟨⟨c, hp', observe, ?_, ?_, ?_⟩⟩
  · intro q hq
    have hq' : q ∈ domain := by
      rwa [show c.source = domain from openSubsetChart_source _ _ _ _] at hq
    change observe q = onSource (c q)
    rw [show c q = toSource ⟨q, hq'⟩ from
      openSubsetChart_apply isOpen_domain hV hn h ⟨q, hq'⟩]
    exact (observe_encode ⟨q, hq'⟩).symm
  · rw [hs]
    exact analyticAt_observe _ hp.2.1
  · rw [hs]
    exact hp.2.2

/-- Compactness gives finitely many analytic graphs over a common local projection. -/
theorem fiberGraphs (p : good) :
    Nonempty (FiberGraphs (E := Parameters) onSource (onSource p.val) good) := by
  haveI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  apply exists_fiber_graphs continuous_onSource (mem_range_self p.val) isOpen_good
  · intro q hq
    exact sameFiber_good p.property hq
  · norm_num [Readings, Parameters, Module.finrank_pi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
  · intro q hq
    exact regularChart_at q (good_subset_regular (sameFiber_good p.property hq))

private def chosenFamily (p : good) :
    FiberGraphs (E := Parameters) onSource (onSource p.val) good :=
  Classical.choice (fiberGraphs p)

private def chosenChart (p : good) :
    AnalyticAmbiguityChart Parameters (Subtype.val ⁻¹' ambiguous onSource) p :=
  (chosenFamily p).ambiguityChart isOpen_good ⟨p.val, rfl⟩

/-- A selected branch is separated from the other branches of its compact fiber. -/
def HasSeparatedFiber (p : good) : Prop :=
  ∀ q : source, onSource q = onSource p.val → q ≠ p.val →
    ∃ V ∈ 𝓝 q, ¬ (∀ᶠ z in 𝓝 p.val, onSource z ∈ onSource '' V)

/-- The local separation condition can also be supplied in matrix coordinates. -/
theorem hasSeparatedFiber_of_observation (p : good)
    (h : ∀ q : source, observation q.val = observation p.val.val → q ≠ p.val →
      ∃ V ∈ 𝓝 q, ¬ (∀ᶠ z in 𝓝 p.val,
        observation z.val ∈ (fun w : source => observation w.val) '' V)) :
    HasSeparatedFiber p := by
  intro q hq hne
  obtain ⟨V, hV, hsep⟩ := h q (onSource_eq_iff.mp hq) hne
  refine ⟨V, hV, fun ht => hsep ?_⟩
  filter_upwards [ht] with z hz
  obtain ⟨w, hw, he⟩ := hz
  exact ⟨w, hw, onSource_eq_iff.mp he⟩

/-- Separation at one good fiber continues to an open dense singleton-fiber locus. -/
theorem compact_generic_recovery_of_separated_fiber (hcritical : CriticalCover)
    (hsep : ∃ p : good, HasSeparatedFiber p) :
    ∃ G : Set source, IsOpen G ∧ Dense G ∧
      ∀ x ∈ G, ∀ y : source, observation y.val = observation x.val → y = x := by
  letI : PathConnectedSpace good := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_good hcritical)
  let A : Set good := Subtype.val ⁻¹' ambiguous onSource
  have hs : ∃ p : good, ∀ k, ¬ EqOn (chosenChart p).graph ((chosenChart p).competitor k)
      (chosenChart p).domain := by
    obtain ⟨p, hp⟩ := hsep
    refine ⟨p, ?_⟩
    apply (chosenFamily p).ambiguityChart_distinct isOpen_good ⟨p.val, rfl⟩
    intro q hq
    exact hp q.val q.property (fun h => hq (Subtype.ext h))
  obtain ⟨hA, hdA⟩ := open_dense_compl_of_analytic_fiber_charts (A := A) chosenChart hs
  let G : Set source := Subtype.val '' Aᶜ
  have hG : IsOpen G := isOpen_good.isOpenMap_subtype_val _ hA
  have hg : Dense G := by
    have h : good ⊆ closure G := by
      intro p hp
      exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨p, hp⟩, hdA _, rfl⟩
    exact fun p => closure_minimal h isClosed_closure (dense_good hcritical p)
  refine ⟨G, hG, hg, ?_⟩
  rintro x ⟨z, hz, rfl⟩ y he
  by_contra hne
  exact hz ⟨y, hne, onSource_eq_iff.mpr he⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteRegularLocus
