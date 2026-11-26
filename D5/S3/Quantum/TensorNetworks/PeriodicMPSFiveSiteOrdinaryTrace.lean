/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteOrdinaryTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteOrdinaryTrace
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart]
   utility: none
   digest: The first nonzero trace determines a large ordinary chart of the compact source. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart

/-! Fixing the first trace to one identifies ordinary points with four
complex polynomial coordinates on an open subset. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace

open Set Filter PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCoordinates
  PeriodicMPSFiveSiteTraceChart PeriodicMPSProjectiveCoordinates
open scoped Topology

open private traceDirection pencil traceDirection_ne_zero pencil_ne_zero
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

noncomputable section

abbrev Parameters := Fin 4 → ℂ

/-- Amplitude in the frame whose first trace is one. -/
def amplitude (q : Parameters) : Fin 8 → ℂ := frame 1 (q 0) 1 (q 1) (q 2) (q 3)

/-- The three projectors of an ordinary point in the first trace chart. -/
def encode (q : Parameters) : Ambient :=
  ((projector ![1, q 0], projector ![1, q 0, (q 0) ^ 2, q 1, q 2, q 3]),
    projector (amplitude q))

/-- The trace and pencil ratios recover the four ordinary parameters. -/
def decode (p : Ambient) : Parameters :=
  ![p.1.1 1 0 / p.1.1 0 0, p.1.2 3 0 / p.1.2 0 0, p.1.2 4 0 / p.1.2 0 0,
    p.1.2 5 0 / p.1.2 0 0]

/-- Parameters whose amplitude is a ray. -/
def domain : Set Parameters := {q | amplitude q ≠ 0}

/-- The first ordinary trace chart inside the compact source. -/
def chartDomain : Set Ambient :=
  {p | p.1.1 0 0 ≠ 0 ∧ p.1.2 0 0 ≠ 0 ∧ decode p ∈ domain}

theorem amplitude_eq (q : Parameters) :
    amplitude q = coordinates 1 (q 0) (q 1) (q 3) (q 0 - q 2) := by
  simpa [amplitude, smul_eq_mul] using
    (frame_trace_coordinates (1 : ℂ) 1 (q 0) (q 1) (q 2) (q 3)).symm

private lemma continuous_amplitude : Continuous amplitude := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [amplitude, frame] <;> fun_prop

theorem isOpen_domain : IsOpen domain :=
  isOpen_ne_fun continuous_amplitude continuous_const

private lemma continuousAt_decode {p : Ambient} (hT : p.1.1 0 0 ≠ 0)
    (hD : p.1.2 0 0 ≠ 0) : ContinuousAt decode p := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> simp only [decode, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hT
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hD
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hD
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hD

theorem isOpen_chartDomain : IsOpen chartDomain := by
  refine isOpen_iff_mem_nhds.mpr fun p hp => ?_
  have hT : ∀ᶠ x in 𝓝 p, x.1.1 0 0 ≠ 0 :=
    (show ContinuousAt (fun x : Ambient => x.1.1 0 0) p by fun_prop)
      (isOpen_ne.mem_nhds hp.1)
  have hD : ∀ᶠ x in 𝓝 p, x.1.2 0 0 ≠ 0 :=
    (show ContinuousAt (fun x : Ambient => x.1.2 0 0) p by fun_prop)
      (isOpen_ne.mem_nhds hp.2.1)
  have hq : ∀ᶠ x in 𝓝 p, decode x ∈ domain :=
    continuousAt_decode hp.1 hp.2.1 (isOpen_domain.mem_nhds hp.2.2)
  exact hT.and (hD.and hq)

private theorem continuousAt_encode {q : Parameters} (hq : q ∈ domain) :
    ContinuousAt encode q := by
  let t : Parameters → Fin 2 → ℂ := fun v => ![1, v 0]
  let d : Parameters → Fin 6 → ℂ := fun v => ![1, v 0, (v 0) ^ 2, v 1, v 2, v 3]
  have ht : Continuous t := by
    apply continuous_pi; intro i
    fin_cases i <;> simp [t] <;> fun_prop
  have hd : Continuous d := by
    apply continuous_pi; intro i
    fin_cases i <;> simp [d] <;> fun_prop
  have htn : t q ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hdn : d q ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  exact (((continuousAt_projector htn).comp ht.continuousAt).prodMk
    ((continuousAt_projector hdn).comp hd.continuousAt)).prodMk
    ((continuousAt_projector hq).comp continuous_amplitude.continuousAt)

theorem decode_encode (q : Parameters) : decode (encode q) = q := by
  have hT : (![1, q 0] : Fin 2 → ℂ) 0 ≠ 0 := one_ne_zero
  have hD : (![1, q 0, (q 0) ^ 2, q 1, q 2, q 3] : Fin 6 → ℂ) 0 ≠ 0 := one_ne_zero
  funext j
  fin_cases j <;> simp [decode, encode, projector_ratio _ _ _ hT, projector_ratio _ _ _ hD]

theorem encode_mem_source {q : Parameters} (hq : q ∈ domain) : encode q ∈ source := by
  have ha : coordinates 1 (q 0) (q 1) (q 3) (q 0 - q 2) ≠ 0 := amplitude_eq q ▸ hq
  let u : Inputs := ⟨![1, q 0, q 1, q 3, q 0 - q 2], ha⟩
  have h : ordinary u = encode q := by
    have hm : q 0 - (q 0 - q 2) = q 2 := by ring
    simp [ordinary, encode, u, traceDirection, pencil, amplitude_eq, hm]
  exact h ▸ ordinary_mem_source u

theorem encode_mem_chartDomain {q : Parameters} (hq : q ∈ domain) :
    encode q ∈ chartDomain := by
  refine ⟨?_, ?_, ?_⟩
  · exact (projector_diag_ne_zero_iff _ 0).2 one_ne_zero
  · exact (projector_diag_ne_zero_iff _ 0).2 one_ne_zero
  · rwa [decode_encode]

set_option maxHeartbeats 1000000 in
-- Recover the two projector columns and expand the weighted scaling.
private theorem ordinary_round_trip (u : Inputs) (ht : (ordinary u).1.1 0 0 ≠ 0) :
    encode (decode (ordinary u)) = ordinary u := by
  let t := u.val 0
  let s := u.val 1 / t
  let d := u.val 2 / t ^ 2
  let m := (t * u.val 1 - u.val 4) / t ^ 2
  let e := u.val 3 / t ^ 2
  let q : Parameters := ![s, d, m, e]
  have ht' : t ≠ 0 := (projector_diag_ne_zero_iff (traceDirection u.val) 0).mp ht
  have ht₂ := pow_ne_zero 2 ht'
  have hs : t * s = u.val 1 := mul_div_cancel₀ _ ht'
  have hd : t ^ 2 * d = u.val 2 := mul_div_cancel₀ _ ht₂
  have hm : t ^ 2 * m = t * u.val 1 - u.val 4 := mul_div_cancel₀ _ ht₂
  have he : t ^ 2 * e = u.val 3 := mul_div_cancel₀ _ ht₂
  have hk : t ^ 2 * (s - m) = u.val 4 := by
    rw [mul_sub, hm, pow_two, mul_assoc, hs]
    ring
  have hq : decode (ordinary u) = q := by
    have h (i : Fin 6) :
        projector (pencil u.val) i 0 / projector (pencil u.val) 0 0 =
          pencil u.val i / (t ^ 2) :=
      projector_ratio (pencil u.val) i 0 ht₂
    have h' := projector_ratio (traceDirection u.val) 1 0 ht'
    change projector (traceDirection u.val) 1 0 / projector (traceDirection u.val) 0 0 = s at h'
    funext i
    fin_cases i <;> simp only [decode, ordinary, q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, h', h] <;> rfl
  have htrace : traceDirection u.val = t • ![1, s] := by
    funext i
    fin_cases i <;> simp [traceDirection, Pi.smul_apply, smul_eq_mul, hs, t]
  have hpencil : pencil u.val = t ^ 2 • ![1, s, s ^ 2, d, m, e] := by
    have hts : t ^ 2 * s = t * u.val 1 := by rw [pow_two, mul_assoc, hs]
    have hss : t ^ 2 * s ^ 2 = u.val 1 ^ 2 := by rw [← mul_pow, hs]
    funext i
    fin_cases i <;> simp [pencil, Pi.smul_apply, smul_eq_mul, hts, hss, hd, hm, he, t]
  have hA : coordinates (u.val 0) (u.val 1) (u.val 2) (u.val 3) (u.val 4) =
      t ^ 5 • amplitude q := by
    rw [amplitude_eq]
    have h := coordinates_scale t 1 s d e (s - m)
    rw [mul_one, hs, hd, he, hk] at h
    exact h
  rw [hq, ordinary, htrace, hpencil, hA, projector_scale _ ht', projector_scale _ ht₂,
    projector_scale _ (pow_ne_zero _ ht')]
  rfl

/-- A compact point in this chart is represented by the decoded ordinary parameters. -/
theorem encode_decode {p : Ambient} (hp : p ∈ source) (hD : p ∈ chartDomain) :
    encode (decode p) = p := by
  haveI : NeBot (𝓝[range ordinary] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have h := ((continuousAt_encode hD.2.2).comp
    (continuousAt_decode hD.1 hD.2.1)).continuousWithinAt (s := range ordinary)
  have he : (fun q => encode (decode q)) =ᶠ[𝓝[range ordinary] p] fun q => q := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_chartDomain.mem_nhds hD)]
      with q hq hqd
    obtain ⟨u, rfl⟩ := hq
    exact ordinary_round_trip u hqd.1
  exact tendsto_nhds_unique h
    ((show Tendsto (fun q : Ambient => q) (𝓝[range ordinary] p) (𝓝 p) from
      nhdsWithin_le_nhds).congr' he.symm)

/-- The ordinary chart identifies parameter and compact-source topologies. -/
def ordinaryHomeomorph : domain ≃ₜ {p : Ambient // p ∈ source ∩ chartDomain} where
  toFun q := ⟨encode q, encode_mem_source q.property, encode_mem_chartDomain q.property⟩
  invFun p := ⟨decode p, p.property.2.2.2⟩
  left_inv q := Subtype.ext (decode_encode q)
  right_inv p := Subtype.ext (encode_decode p.property.1 p.property.2)
  continuous_toFun := (continuous_iff_continuousAt.mpr
    fun q : domain => (continuousAt_encode q.property).comp continuous_subtype_val.continuousAt
    ).subtype_mk _
  continuous_invFun := (continuous_iff_continuousAt.mpr
    fun p : {p : Ambient // p ∈ source ∩ chartDomain} =>
      (continuousAt_decode p.property.2.1 p.property.2.2.1).comp
        continuous_subtype_val.continuousAt).subtype_mk _

private theorem ordinary_mem_chartDomain (u : Inputs) (ht : u.val 0 ≠ 0) :
    ordinary u ∈ chartDomain := by
  have ht' : (ordinary u).1.1 0 0 ≠ 0 :=
    (projector_diag_ne_zero_iff (traceDirection u.val) 0).mpr ht
  have hp : (ordinary u).1.2 0 0 ≠ 0 :=
    (projector_diag_ne_zero_iff (pencil u.val) 0).mpr (pow_ne_zero _ ht)
  set a := coordinates (u.val 0) (u.val 1) (u.val 2) (u.val 3) (u.val 4)
  have ha : a ≠ 0 := u.property
  have hj : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  obtain ⟨j, hj⟩ := hj
  have hq : projector (amplitude (decode (ordinary u))) = projector a :=
    congrArg Prod.snd (ordinary_round_trip u ht')
  refine ⟨ht', hp, fun h => ?_⟩
  rw [h] at hq
  have hz : projector (0 : Fin 8 → ℂ) j j ≠ 0 :=
    hq.symm ▸ (projector_diag_ne_zero_iff a j).mpr hj
  exact (projector_diag_ne_zero_iff (0 : Fin 8 → ℂ) j).mp hz rfl

private theorem continuous_ordinary : Continuous ordinary := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hT : Continuous traceDirection := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [traceDirection] <;> fun_prop
  have hP : Continuous pencil := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [pencil] <;> fun_prop
  have hA : Continuous (fun a : Fin 5 → ℂ =>
      coordinates (a 0) (a 1) (a 2) (a 3) (a 4)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [coordinates] <;> fun_prop
  have cT := (continuousAt_projector (traceDirection_ne_zero u)).comp hT.continuousAt
  have cP := (continuousAt_projector (pencil_ne_zero u)).comp hP.continuousAt
  have cA : ContinuousAt (fun a : Fin 5 → ℂ =>
      projector (coordinates (a 0) (a 1) (a 2) (a 3) (a 4))) u.val :=
    ContinuousAt.comp_of_eq
      (f := fun a : Fin 5 → ℂ => coordinates (a 0) (a 1) (a 2) (a 3) (a 4))
      (x := u.val) (continuousAt_projector u.property) hA.continuousAt rfl
  exact ((cT.prodMk cP).prodMk cA).comp (continuous_subtype_val.continuousAt (x := u))

/-- The first ordinary trace chart is dense in the compact source. -/
theorem dense_chartDomain :
    Dense (Subtype.val ⁻¹' chartDomain : Set source) := by
  let B : Set Inputs := {u | u.val 0 ≠ 0}
  have he : IsOpenQuotientMap (Function.eval 0 : (Fin 5 → ℂ) → ℂ) :=
    ⟨fun c => ⟨fun _ => c, rfl⟩, continuous_apply 0, isOpenMap_eval 0⟩
  have hD : Dense {u : Fin 5 → ℂ | u 0 ≠ 0} :=
    he.dense_preimage_iff.mpr (dense_compl_singleton 0)
  have hOpen : IsOpen {a : Fin 5 → ℂ | coordinates (a 0) (a 1) (a 2) (a 3) (a 4) ≠ 0} := by
    apply isOpen_ne_fun _ continuous_const
    apply continuous_pi
    intro i
    fin_cases i <;> simp [coordinates] <;> fun_prop
  have hB : Dense B := hD.preimage hOpen.isOpenMap_subtype_val
  have hfull : source ⊆ closure (ordinary '' B) := by
    apply closure_minimal _ isClosed_closure
    rintro _ ⟨u, rfl⟩
    exact image_closure_subset_closure_image continuous_ordinary ⟨u, hB u, rfl⟩
  intro p
  rw [closure_subtype]
  apply closure_mono _ (hfull p.property)
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨⟨ordinary u, ordinary_mem_source u⟩, ordinary_mem_chartDomain u hu, rfl⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace
