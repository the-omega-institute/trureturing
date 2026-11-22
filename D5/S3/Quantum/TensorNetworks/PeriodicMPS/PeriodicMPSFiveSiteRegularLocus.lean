/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteRegularLocus
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteRegularLocus
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalCover]
   utility: none
   digest: The ordinary source away from critical and boundary values is open dense and path connected. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalCover
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSImmersionPullback
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularComplement

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteRegularLocus

open Set Filter Function PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteOrdinaryTrace
  PeriodicMPSFiveSiteCriticalRank PeriodicMPSFiveSiteCriticalCover
  PeriodicMPSFiveSitePhysicalObservation PeriodicMPSFiveSiteBoundaryCover
  PeriodicMPSImmersionPullback PeriodicMPSRegularComplement
  PeriodicMPSFiveSiteCriticalDivisors
open scoped Topology Matrix.Norms.Elementwise

open private continuousAt_decode from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace

noncomputable section

abbrev H := Fin 6 → ℝ
abbrev Readings := Fin 9 → ℝ

private def Covered {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Set E) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (D : ι → Set H) (g : ι → H → E),
    (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧ A ⊆ ⋃ i, g i '' D i

private theorem Covered.mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E} (h : Covered B) (hAB : A ⊆ B) : Covered A := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := h
  exact ⟨ι, hι, D, g, hd, hAB.trans hc⟩

private theorem Covered.union {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E} (hA : Covered A) (hB : Covered B) : Covered (A ∪ B) := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := hA
  obtain ⟨κ, hκ, U, u, hu, hcov⟩ := hB
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim D U, Sum.elim g u, ?_, ?_⟩
  · rintro (i | j)
    · exact hd i
    · exact hu j
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hx)
      exact mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hx)
      exact mem_iUnion.mpr ⟨Sum.inr j, hj⟩

private theorem Covered.image {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Set E} (hA : Covered A)
    (f : E → F) (hf : DifferentiableOn ℝ f A) : Covered (f '' A) := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := hA
  refine ⟨ι, hι, fun j => D j ∩ g j ⁻¹' A, fun j => f ∘ g j,
    fun j => hf.comp ((hd j).mono inter_subset_left) inter_subset_right, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, y, hy, he⟩ := mem_iUnion.mp (hc hx)
  exact mem_iUnion.mpr ⟨j, y, ⟨hy, by change g j y ∈ A; rwa [he]⟩, congrArg f he⟩

/-- Observation in the ordinary parameters with the trace constraint eliminated. -/
def observe (q : Parameters) : Readings := readout (normalizedObservation q)

/-- Observation in the nine trace-one readouts on the compact source. -/
def onSource (p : source) : Readings := measured p.val

theorem continuous_onSource : Continuous onSource := by
  have h := continuousOn_iff_continuous_restrict.mp continuousOn_observation
  have he : onSource = readout ∘ (source.restrict observation) := by
    funext p
    exact measured_eq_readout p.val
  rw [he]
  exact readout.continuous.comp h

theorem observe_encode (q : domain) :
    onSource ⟨encode q.val, encode_mem_source q.property⟩ = observe q.val := by
  unfold onSource observe
  rw [measured_eq_readout, observation_of_projector q.property rfl]
  rfl

theorem analyticAt_observe (q : Parameters) (hq : q ∈ domain) :
    AnalyticAt ℝ observe q :=
  (readout.analyticAt _).comp (analyticAt_normalizedObservation q hq)

/-- Parameters in the ordinary chart where the normalized map immerses. -/
def regular : Set Parameters := {q | q ∈ domain ∧ Injective (fderiv ℝ observe q)}

theorem isOpen_regular : IsOpen regular := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have ha := analyticAt_observe q hq.1
  have h₁ : ∀ᶠ x in 𝓝 q, x ∈ domain := isOpen_domain.mem_nhds hq.1
  have h₂ : ∀ᶠ x in 𝓝 q, Injective (fderiv ℝ observe x) :=
    ha.fderiv.continuousAt (ContinuousLinearMap.isOpen_injective.mem_nhds hq.2)
  exact h₁.and h₂

private theorem kernel_full {q : Parameters} (hq : q ∈ domain) {v : Parameters}
    (hv : fderiv ℝ observe q v = 0) : fderiv ℝ normalizedObservation q v = 0 := by
  have h : normalizedObservation =ᶠ[𝓝 q] readoutInverse ∘ observe := by
    filter_upwards [isOpen_domain.mem_nhds hq] with x hx
    have he := readoutInverse_readout (encode_mem_source hx)
    rw [observation_of_projector hx rfl] at he
    exact he.symm
  have hd := differentiable_readoutInverse.differentiableAt.hasFDerivAt.comp q
    (analyticAt_observe q hq).differentiableAt.hasFDerivAt
  have hn : HasFDerivAt normalizedObservation
      (fderiv ℝ readoutInverse (observe q) ∘SL fderiv ℝ observe q) q :=
    hd.congr_of_eventuallyEq h
  rw [hn.fderiv, ContinuousLinearMap.comp_apply, hv, map_zero]

private theorem critical_covered : Covered (domain \ regular) := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := cover_critical_equations
  let reorder : Parameters → Parameters := fun p => ![p 0, p 1, p 0 - p 3, p 2]
  let invariants : Parameters → Parameters := fun q => ![q 0, q 1, q 3, q 0 - q 2]
  have hdiff : Differentiable ℝ reorder := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [reorder] <;> fun_prop
  have hl (q : Parameters) : reorder (invariants q) = q := by
    funext i
    fin_cases i <;> simp [reorder, invariants]
  refine ⟨ι, hι, D, fun i => reorder ∘ g i,
    fun i => hdiff.differentiableOn.comp (hd i) (mapsTo_univ _ _), ?_⟩
  intro q hq
  have hn : ¬ Injective (fderiv ℝ observe q) := fun h => hq.2 ⟨hq.1, h⟩
  obtain ⟨v, hv, hv0⟩ : ∃ v : Parameters, v ≠ 0 ∧ fderiv ℝ observe q v = 0 := by
    by_contra! he
    exact hn (fun x y hxy => by
      apply sub_eq_zero.mp
      by_contra hne
      exact he (x - y) hne (by rw [map_sub, hxy, sub_self]))
  have hminor (k : Fin 10) :
      MvPolynomial.eval (lift (invariants q)) (minorOver k) = 0 := by
    have hh : lift (invariants q) = conjugatedTuple q := by
      funext i
      fin_cases i <;> simp [lift, invariants, conjugatedTuple, Complex.star_def]
    rw [hh, minorOver, MvPolynomial.eval_map]
    exact evaluated_minor_eq_zero_of_kernel q hq.1 v hv (kernel_full hq.1 hv0) k
  obtain ⟨i, u, hu, he⟩ := mem_iUnion.mp (hc ⟨hminor 0, hminor 1⟩)
  exact mem_iUnion.mpr ⟨i, u, hu, (congrArg reorder he).trans (hl q)⟩

/-- Compact source points represented by regular ordinary parameters. -/
def regularSource : Set source :=
  {p | p.val ∈ chartDomain ∧ decode p.val ∈ regular}

theorem isOpen_regularSource : IsOpen regularSource := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have h₁ := (isOpen_chartDomain.preimage continuous_subtype_val).mem_nhds hp.1
  have hC := (continuousAt_decode hp.1.1 hp.1.2.1).comp
    continuous_subtype_val.continuousAt
  exact Filter.inter_mem h₁ (hC (isOpen_regular.mem_nhds hp.2))

private def excludedValues : Set Readings := onSource '' regularSourceᶜ

/-- Remove the entire fiber of each observation attained on the boundary
or at a nonimmersive ordinary point. -/
def good : Set source := onSource ⁻¹' excludedValuesᶜ

theorem isOpen_good : IsOpen good := by
  haveI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  exact (continuous_onSource.isClosedMap _ isOpen_regularSource.isClosed_compl).isOpen_compl.preimage
    continuous_onSource

theorem good_subset_regular : good ⊆ regularSource := by
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

private theorem excluded_covered : Covered excludedValues := by
  obtain ⟨D, g, hd, hc⟩ := real_boundary_observation_cover
  have h₁ : Covered ((onSource : source → Readings) '' {x | x.val ∉ chartDomain}) := by
    refine ⟨BoundaryFamily, inferInstance, D, fun i => readout ∘ g i,
      fun i => readout.differentiable.differentiableOn.comp (hd i) (mapsTo_univ _ _), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, u, hu, he⟩ := mem_iUnion.mp (hc ⟨p.val, ⟨p.property, hp⟩, rfl⟩)
    exact mem_iUnion.mpr ⟨i, u, hu, (congrArg readout he).trans (measured_eq_readout p.val).symm⟩
  have h₂ := critical_covered.image observe
    (fun q hq => (analyticAt_observe q hq.1).differentiableAt.differentiableWithinAt)
  apply (h₁.union h₂).mono
  rintro _ ⟨p, hp, rfl⟩
  by_cases hp' : p.val ∈ chartDomain
  · right
    have hq : decode p.val ∈ domain := hp'.2.2
    refine ⟨decode p.val, ⟨hq, fun h => hp ⟨hp', h⟩⟩, ?_⟩
    rw [← observe_encode ⟨decode p.val, hq⟩]
    exact congrArg onSource (Subtype.ext (encode_decode p.property hp'))
  · exact Or.inl ⟨p, hp', rfl⟩

private theorem base_covered : Covered (domainᶜ : Set Parameters) := by
  let unpack (u : H) : Fin 3 → ℂ := fun i =>
    Complex.equivRealProdCLM.symm
      (u (finSumFinEquiv (m := 3) (n := 3) (Sum.inl i)),
       u (finSumFinEquiv (m := 3) (n := 3) (Sum.inr i)))
  let g (u : H) : Parameters :=
    let p := unpack u
    ![p 0, p 1, 2 * p 0 * p 1, p 2]
  have hdiff : Differentiable ℝ unpack := by
    apply differentiable_pi.mpr
    intro i
    exact Complex.equivRealProdCLM.symm.differentiable.comp
      ((differentiable_apply _).prodMk (differentiable_apply _))
  have hg : Differentiable ℝ g := by
    apply differentiable_pi.mpr
    intro i
    have hu (k : Fin 3) : Differentiable ℝ (fun r => unpack r k) :=
      (differentiable_pi.mp hdiff) k
    fin_cases i <;> simp [g] <;> fun_prop
  refine ⟨Unit, inferInstance, fun _ => univ, fun _ => g, fun _ => hg.differentiableOn, ?_⟩
  intro q hq
  let z := q 2 - 2 * q 0 * q 1
  let w := q 3 - q 0 * z - q 0 ^ 2 * q 1
  have h : amplitude q = 0 := not_not.mp hq
  have hm : z + 2 * q 0 * q 1 = q 2 := by dsimp [z]; ring
  have he : w + q 0 * z + q 0 ^ 2 * q 1 = q 3 := by dsimp [w]; ring
  have hframe := PeriodicMPSFiveSiteTraceChart.frame_first_chart (q 0) 1 (q 1) z w
  rw [hm, he] at hframe
  unfold amplitude at h
  rw [hframe, PeriodicMPSFiveSiteTraceChart.chart] at h
  have hz := congrArg (PeriodicMPSFiveSiteTraceChart.shear (-(q 0))) h
  rw [PeriodicMPSFiveSiteTraceChart.shear_add, neg_add_cancel,
    PeriodicMPSFiveSiteTraceChart.shear_zero] at hz
  have hs : PeriodicMPSFiveSiteTraceChart.shear (-(q 0)) (0 : Fin 8 → ℂ) = 0 := by
    funext i
    fin_cases i <;> simp [PeriodicMPSFiveSiteTraceChart.shear]
  rw [hs] at hz
  have hzero := (PeriodicMPSFiveSiteCoordinates.aligned_eq_zero_iff _ _ _ _).mp hz
  have hZ : q 2 = 2 * q 0 * q 1 := sub_eq_zero.mp hzero.2.1
  let v : Fin 3 → ℂ := ![q 0, q 1, q 3]
  let u : H := (Sum.elim (fun i => (v i).re) (fun i => (v i).im)) ∘
    (finSumFinEquiv (m := 3) (n := 3)).symm
  have hu : unpack u = v := by
    funext i
    simp [unpack, u, Function.comp_def, Complex.equivRealProdCLM_symm_apply, Complex.re_add_im]
  refine mem_iUnion.mpr ⟨(), u, mem_univ _, ?_⟩
  change g u = q
  change ![unpack u 0, unpack u 1, 2 * unpack u 0 * unpack u 1, unpack u 2] = q
  rw [hu]
  funext i
  fin_cases i <;> simp [v, hZ]

/-- The good values expressed on the full ordinary parameter space. -/
def goodParameters : Set Parameters := {q | q ∈ domain ∧ observe q ∉ excludedValues}

private theorem goodParameters_compl_covered : Covered goodParametersᶜ := by
  let A := regular ∩ observe ⁻¹' excludedValues
  obtain ⟨ι, hι, D, g, hd, hcover⟩ := excluded_covered
  have hA : Covered A := cover_regular_preimage A
    (fun q hq => ⟨analyticAt_observe q hq.1.1, hq.1.2⟩) D g hd (by
      rintro _ ⟨q, hq, rfl⟩
      exact hcover hq.2)
  apply ((base_covered.union critical_covered).union hA).mono
  intro q hq
  by_cases h₀ : q ∈ domain
  · by_cases hr : q ∈ regular
    · exact Or.inr ⟨hr, by
        by_contra hv
        exact hq ⟨h₀, hv⟩⟩
    · exact Or.inl (Or.inr ⟨h₀, hr⟩)
  · exact Or.inl (Or.inl h₀)

private theorem pathConnected_and_dense_goodParameters :
    IsPathConnected goodParameters ∧ Dense goodParameters := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := goodParameters_compl_covered
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

private theorem good_image :
    good = (fun q : domain => (⟨encode q.val, encode_mem_source q.property⟩ : source)) ''
      (Subtype.val ⁻¹' goodParameters) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hC, hreg⟩ := good_subset_regular hp
    let q : domain := ⟨decode p.val, hreg.1⟩
    have he : (⟨encode q.val, encode_mem_source q.property⟩ : source) = p :=
      Subtype.ext (encode_decode p.property hC)
    refine ⟨q, ⟨q.property, ?_⟩, he⟩
    rw [← observe_encode q, he]
    exact hp
  · rintro ⟨q, hq, rfl⟩
    change onSource _ ∉ excludedValues
    rw [observe_encode]
    exact hq.2

theorem isPathConnected_good : IsPathConnected good := by
  have h : Continuous (fun q : domain =>
      (⟨encode q.val, encode_mem_source q.property⟩ : source)) :=
    (continuous_subtype_val.comp ordinaryHomeomorph.continuous).subtype_mk _
  rw [good_image]
  exact (pathConnected_and_dense_goodParameters.1.preimage_coe
    (fun _ hq => hq.1)).image h

theorem dense_good : Dense good := by
  have h₁ : Dense (Subtype.val ⁻¹' goodParameters : Set domain) :=
    pathConnected_and_dense_goodParameters.2.preimage isOpen_domain.isOpenMap_subtype_val
  let f (q : domain) : source := ⟨encode q.val, encode_mem_source q.property⟩
  have hf : Continuous f := (continuous_subtype_val.comp ordinaryHomeomorph.continuous).subtype_mk _
  have hR : Subtype.val ⁻¹' chartDomain ⊆ closure good := by
    intro p hp
    let q : domain := ⟨decode p.val, hp.2.2⟩
    have he : f q = p := Subtype.ext (encode_decode p.property hp)
    rw [good_image]
    exact image_closure_subset_closure_image hf ⟨q, h₁ q, he⟩
  exact fun p => closure_minimal hR isClosed_closure (dense_chartDomain p)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteRegularLocus
