/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteOrdinaryTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteOrdinaryTrace
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteBoundaryCover]
   utility: none
   digest: The first trace-square chart is open and dense in the compact six-site source. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteBoundaryCover

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteOrdinaryTrace

open Set Filter PeriodicMPSProjectiveCoordinates PeriodicMPSSixSiteCompactSource
  PeriodicMPSSixSiteCompactExceptional
open PeriodicMPSSixSiteBoundaryCover (boundary)
open scoped Topology

open private exists_traces continuous_amplitude amplitude_zero
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
open private continuous_invariant_entry continuousAt_firstTraceChart_entry
  firstTraceChart_of_projector
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional

noncomputable section

abbrev Parameters := Fin 4 → ℂ

/-- The weight-two invariant tuple with first trace-square equal to one. -/
def invariantParameter (q : Parameters) : Fin 6 → ℂ :=
  ![1, q 0, (q 0) ^ 2, q 1, q 2, q 3]

/-- The six-site amplitude in the first trace-square chart. -/
def chartAmplitude (q : Parameters) : Fin 14 → ℂ :=
  amplitude (invariantParameter q)

/-- Parameters on which the cubic defines an amplitude ray. -/
def domain : Set Parameters := {q | chartAmplitude q ≠ 0}

def encode (q : Parameters) : Ambient := graphPoint (invariantParameter q)

def decode (p : Ambient) : Parameters :=
  ![firstTraceChart p 1, firstTraceChart p 3, firstTraceChart p 4, firstTraceChart p 5]

/-- The portion of the first trace-square chart away from the cubic base locus. -/
def chartDomain : Set Ambient := {p | p.1 0 0 ≠ 0 ∧ decode p ∈ domain}

theorem chartAmplitude_eq (q : Parameters) :
    chartAmplitude q = PeriodicMPSSixSiteCoordinates.coordinates 1 (q 0) (q 0 ^ 2)
      (q 1) (q 2) (q 3) := rfl

private theorem invariantParameter_quadric (q : Parameters) :
    invariantParameter q 1 ^ 2 = invariantParameter q 0 * invariantParameter q 2 := by
  change q 0 ^ 2 = 1 * q 0 ^ 2
  rw [one_mul]

private theorem continuous_invariantParameter : Continuous invariantParameter := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [invariantParameter] <;> fun_prop

theorem isOpen_domain : IsOpen domain :=
  isOpen_ne_fun (continuous_amplitude.comp continuous_invariantParameter) continuous_const

theorem continuousAt_decode {p : Ambient} (hp : p.1 0 0 ≠ 0) :
    ContinuousAt decode p := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> exact continuousAt_firstTraceChart_entry hp _

theorem isOpen_chartDomain : IsOpen chartDomain := by
  refine isOpen_iff_mem_nhds.mpr fun p hp => ?_
  have h₁ := (continuous_invariant_entry 0 0).continuousAt (isOpen_ne.mem_nhds hp.1)
  have h₂ := continuousAt_decode hp.1 (isOpen_domain.mem_nhds hp.2)
  exact inter_mem h₁ h₂

private theorem continuousAt_graphPoint {q : Fin 6 → ℂ} (ha : amplitude q ≠ 0) :
    ContinuousAt graphPoint q := by
  have hq : q ≠ 0 := by
    intro h
    apply ha
    rw [h]
    exact amplitude_zero
  exact (continuousAt_projector hq).prodMk
    ((continuousAt_projector ha).comp continuous_amplitude.continuousAt)

private theorem continuousAt_encode {q : Parameters} (hq : q ∈ domain) :
    ContinuousAt encode q :=
  (continuousAt_graphPoint hq).comp continuous_invariantParameter.continuousAt

theorem decode_encode (q : Parameters) : decode (encode q) = q := by
  have h₀ : invariantParameter q 0 ≠ 0 := one_ne_zero
  have h (i : Fin 6) : firstTraceChart (encode q) i = invariantParameter q i := by
    change projector (invariantParameter q) i 0 / projector (invariantParameter q) 0 0 = _
    rw [projector_ratio _ _ _ h₀]
    exact div_one _
  funext i
  fin_cases i <;> simp [decode, h, invariantParameter]

theorem encode_mem_source {q : Parameters} (hq : q ∈ domain) : encode q ∈ source :=
  ordinary_mem_source ⟨invariantParameter q, invariantParameter_quadric q, hq⟩

theorem encode_mem_chartDomain {q : Parameters} (hq : q ∈ domain) :
    encode q ∈ chartDomain := by
  refine ⟨(projector_diag_ne_zero_iff (invariantParameter q) 0).2 one_ne_zero, ?_⟩
  rwa [decode_encode]

private theorem invariantParameter_decode {p : Ambient} (hp : p ∈ source)
    (ht : p.1 0 0 ≠ 0) : invariantParameter (decode p) = firstTraceChart p := by
  have h₀ : firstTraceChart p 0 = 1 := div_self ht
  have h₂ : firstTraceChart p 2 = firstTraceChart p 1 ^ 2 := by
    change p.1 2 0 / p.1 0 0 = (p.1 1 0 / p.1 0 0) ^ 2
    rw [div_pow, source_quadric_column hp 0, pow_two, mul_div_mul_left _ _ ht]
  funext i
  fin_cases i <;> simp [invariantParameter, decode, h₀, h₂]

private theorem exists_projector {p : Ambient} (hp : p ∈ source) :
    ∃ q : Fin 6 → ℂ, p.1 = projector q := by
  obtain ⟨q, hq, he⟩ := source_invariant_projective hp
  have hm : mass q = 1 := hq
  exact ⟨q, by rw [← he, projector, hm, inv_one, one_smul]⟩

private theorem chartAmplitude_decode_of_projector {p : Ambient} {q : Fin 6 → ℂ}
    (hp : p ∈ source) (hproj : p.1 = projector q) (ht : q 0 ≠ 0) :
    chartAmplitude (decode p) = (q 0)⁻¹ ^ 3 • amplitude q := by
  have hdiag : p.1 0 0 ≠ 0 := hproj.symm ▸ (projector_diag_ne_zero_iff q 0).mpr ht
  rw [chartAmplitude, invariantParameter_decode hp hdiag, firstTraceChart_of_projector hproj ht,
    amplitude_scale]

/-- A point in the ordinary part of the compact source is the graph of its decoded input. -/
theorem encode_decode {p : Ambient} (hp : p ∈ source) (hD : p ∈ chartDomain) :
    encode (decode p) = p := by
  obtain ⟨q, hq⟩ := exists_projector hp
  have ht : q 0 ≠ 0 := (projector_diag_ne_zero_iff q 0).mp (by rw [← hq]; exact hD.1)
  have hproj : p.1 = projector (invariantParameter (decode p)) := by
    rw [invariantParameter_decode hp hD.1, firstTraceChart_of_projector hq ht,
      projector_scale _ (inv_ne_zero ht)]
    exact hq
  exact (eq_graphPoint_of_amplitude_ne_zero hp hproj hD.2).symm

/-- The boundary cover applies to precisely the compact points outside this chart. -/
theorem mem_boundary_iff {p : Ambient} (hp : p ∈ source) :
    p ∈ boundary ↔ p ∉ chartDomain := by
  constructor
  · rintro ⟨_, q, hq, hzero⟩ hD
    have ht : q 0 ≠ 0 := (projector_diag_ne_zero_iff q 0).mp (by rw [← hq]; exact hD.1)
    have ha := hzero.resolve_left ht
    exact hD.2 (by rw [chartAmplitude_decode_of_projector hp hq ht, ha, smul_zero])
  · intro hD
    obtain ⟨q, hq⟩ := exists_projector hp
    refine ⟨hp, q, hq, ?_⟩
    by_cases ht : q 0 = 0
    · exact Or.inl ht
    · right
      by_contra ha
      apply hD
      refine ⟨hq.symm ▸ (projector_diag_ne_zero_iff q 0).mpr ht, ?_⟩
      change chartAmplitude (decode p) ≠ 0
      rw [chartAmplitude_decode_of_projector hp hq ht]
      exact smul_ne_zero (pow_ne_zero 3 (inv_ne_zero ht)) ha

def toSource (q : domain) : source := ⟨encode q, encode_mem_source q.property⟩

theorem continuous_toSource : Continuous toSource :=
  (continuous_iff_continuousAt.mpr
    fun q : domain => (continuousAt_encode q.property).comp continuous_subtype_val.continuousAt
    ).subtype_mk _

/-- The ordinary chart identifies the parameter topology with the compact source topology. -/
def ordinaryHomeomorph : domain ≃ₜ {p : Ambient // p ∈ source ∩ chartDomain} where
  toFun q := ⟨encode q, encode_mem_source q.property, encode_mem_chartDomain q.property⟩
  invFun p := ⟨decode p, p.property.2.2⟩
  left_inv q := Subtype.ext (decode_encode q)
  right_inv p := Subtype.ext (encode_decode p.property.1 p.property.2)
  continuous_toFun := (continuous_subtype_val.comp continuous_toSource).subtype_mk _
  continuous_invFun := (continuous_iff_continuousAt.mpr
    fun p : {p : Ambient // p ∈ source ∩ chartDomain} =>
      (continuousAt_decode p.property.2.1).comp continuous_subtype_val.continuousAt
    ).subtype_mk _

private theorem ordinary_mem_chartDomain (u : Inputs) (ht : u.val 0 ≠ 0) :
    ordinary u ∈ chartDomain := by
  refine ⟨(projector_diag_ne_zero_iff u.val 0).mpr ht, ?_⟩
  change chartAmplitude (decode (ordinary u)) ≠ 0
  rw [chartAmplitude_decode_of_projector (ordinary_mem_source u) rfl ht]
  exact smul_ne_zero (pow_ne_zero 3 (inv_ne_zero ht)) u.property.2

/-- The first ordinary trace-square chart is dense in the compact source. -/
theorem dense_chartDomain : Dense (Subtype.val ⁻¹' chartDomain : Set source) := by
  have hfull : source ⊆ closure (source ∩ chartDomain) := by
    apply closure_minimal _ isClosed_closure
    rintro _ ⟨u, rfl⟩
    obtain ⟨t, s, ht, hts, hs⟩ := exists_traces u.val u.property.1
    let v (r : ℂ) : Fin 6 → ℂ := ![r ^ 2, r * s, s ^ 2, u.val 3, u.val 4, u.val 5]
    have hv : v t = u.val := by
      funext i
      fin_cases i <;> simp [v, ht, hts, hs]
    have hc : Continuous v := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp [v] <;> fun_prop
    have hat : amplitude (v t) ≠ 0 := by rw [hv]; exact u.property.2
    have ha : ∀ᶠ r in 𝓝 t, amplitude (v r) ≠ 0 :=
      (continuous_amplitude.comp hc).continuousAt (isOpen_ne.mem_nhds hat)
    have htn : ∀ᶠ r in 𝓝[≠] t, r ≠ 0 := by
      by_cases h : t = 0
      · subst t
        exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)
    haveI : NeBot (𝓝[≠] t) := mem_closure_iff_nhdsWithin_neBot.mp (dense_compl_singleton t t)
    have hgv : Tendsto (graphPoint ∘ v) (𝓝[≠] t) (𝓝 (ordinary u)) := by
      have hg : ContinuousAt (graphPoint ∘ v) t :=
        (continuousAt_graphPoint hat).comp hc.continuousAt
      change Tendsto (graphPoint ∘ v) (𝓝 t) (𝓝 (graphPoint (v t))) at hg
      rw [hv] at hg
      exact hg.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hgv
    filter_upwards [nhdsWithin_le_nhds ha, htn] with r hr hr₀
    have hquad : v r 1 ^ 2 = v r 0 * v r 2 := mul_pow _ _ _
    let w : Inputs := ⟨v r, hquad, hr⟩
    exact ⟨ordinary_mem_source w, ordinary_mem_chartDomain w (pow_ne_zero 2 hr₀)⟩
  intro p
  rw [closure_subtype]
  apply closure_mono _ (hfull p.property)
  rintro x ⟨hx, hD⟩
  exact ⟨⟨x, hx⟩, hD, rfl⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteOrdinaryTrace
