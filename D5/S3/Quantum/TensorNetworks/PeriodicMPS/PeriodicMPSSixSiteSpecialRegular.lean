/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialRegular
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialRegular
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms]
   utility: none
   digest: The two certified six-site lifts have injective normalized observation differentials. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialRegular

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialRegular

open Filter Function Set
open PeriodicMPSSixSiteSpecialGerms PeriodicMPSSixSiteLocalGraphs
  PeriodicMPSSixSiteCompactSource PeriodicMPSSixSiteCriticalRank
  PeriodicMPSSixSiteJetCoordinates PeriodicMPSSixSiteMarginal
open PeriodicMPSSixSitePhysicalObservation (traceParameter rayAmplitude raw_trace_eq raw_eq_entries)
open PeriodicMPSFiveSitePhysicalObservation (complexParameter entries rawTrace)
open PeriodicMPSProjectiveCoordinates (projector projector_scale)
open scoped Topology Matrix.Norms.Elementwise

open private pack unpack_pack pack_unpack from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms
open private gram_trace from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
open private entries_smul from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
open private differentiable_complexParameter from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialRegular
open private tangent_invertible from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLocalGraphs
open private mixedTuple rawMass special_coordinates rebuild_center_of_valid
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialGerms

noncomputable section

private def toMixed (q : Parameters) : Q := ![(q 3)⁻¹, q 1 / q 3, q 0, q 2 / q 3]

/-- The normalized first-trace chart coordinates of a mixed-trace chart point. -/
def toFirst (a : Q) : Parameters := ![a 2, a 1 / a 0, a 3 / a 0, (a 0)⁻¹]

private theorem toMixed_toFirst {a : Q} (ha : a 0 ≠ 0) : toMixed (toFirst a) = a := by
  funext j
  fin_cases j <;> simp [toMixed, toFirst, div_inv_eq_mul, div_mul_cancel₀ _ ha]

private theorem toFirst_toMixed {q : Parameters} (hq : q 3 ≠ 0) : toFirst (toMixed q) = q := by
  funext j
  fin_cases j <;> simp [toMixed, toFirst, div_inv_eq_mul, div_mul_cancel₀ _ hq]

private theorem mixedTuple_toMixed {q : Parameters} (hq : q 3 ≠ 0) :
    mixedTuple (toMixed q) = (q 3)⁻¹ • invariantTuple q := by
  funext j
  fin_cases j <;>
    simp [mixedTuple, toMixed, invariantTuple, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hq] <;> ring

private theorem differentiableAt_toFirst {a : Q} (ha : a 0 ≠ 0) :
    DifferentiableAt ℝ toFirst a := by
  have hd : DifferentiableAt ℝ (fun x : Q => x 0) a :=
    (differentiable_apply _).differentiableAt
  have hi := hd.fun_inv ha
  refine differentiableAt_pi.mpr fun j => ?_
  fin_cases j <;> simp [toFirst, div_eq_mul_inv] <;> first
  | exact hi
  | exact (differentiable_apply _).differentiableAt.mul hi
  | exact (differentiable_apply _).differentiableAt

private theorem differentiableAt_toMixed {q : Parameters} (hq : q 3 ≠ 0) :
    DifferentiableAt ℝ toMixed q := by
  have hd : DifferentiableAt ℝ (fun x : Parameters => x 3) q :=
    (differentiable_apply _).differentiableAt
  have hi := hd.fun_inv hq
  refine differentiableAt_pi.mpr fun j => ?_
  fin_cases j <;> simp [toMixed, div_eq_mul_inv] <;> first
  | exact hi
  | exact (differentiable_apply _).differentiableAt.mul hi
  | exact (differentiable_apply _).differentiableAt

private theorem differentiable_rawMass : Differentiable ℝ rawMass := by
  have hm : rawMass = rawTrace ∘ raw ∘ (fun a : Q => pack a 1) := by
    funext a
    change rawMass a = rawTrace (raw (pack a 1))
    rw [raw_trace_eq, show pack a 1 8 = 1 from rfl, one_mul]
    simp [rayAmplitude, traceParameter, unpack_pack, rawMass, mixedTuple]
  rw [hm]
  have hpack : Differentiable ℝ (fun a : Q => pack a 1) := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [pack] <;> fun_prop
  have hraw : Differentiable ℝ (raw (R := ℝ)) :=
    fun x => (analyticAt_pi_iff.mpr
      (fun i => PeriodicMPSSixSiteAnalyticDerivative.analytic_raw x i)).differentiableAt
  have htrace : Differentiable ℝ rawTrace := by unfold rawTrace; fun_prop
  exact htrace.comp (hraw.comp hpack)

private theorem mass_nonzero {q : Parameters} (h : q ∈ domain) (hk : q 3 ≠ 0) :
    rawMass (toMixed q) ≠ 0 := by
  have he : amplitude (mixedTuple (toMixed q)) ≠ 0 := by
    rw [mixedTuple_toMixed hk, amplitude_scale]
    exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero hk)) h
  exact (gram_mass_pos _ he).ne'

private theorem packed_tangent {q : Parameters} (h : q ∈ domain) (hk : q 3 ≠ 0) (τ : ℝ) :
    tangent (pack (toMixed q) (τ / rawMass (toMixed q))) =
      fun j => τ * entries (normalizedObservation q) j.castSucc := by
  let a := toMixed q
  let u := pack a (τ / rawMass a)
  have hu : rayAmplitude u = amplitude (mixedTuple a) := by
    simp [rayAmplitude, traceParameter, u, unpack_pack, mixedTuple]
  have hproj : (graphPoint (mixedTuple a)).2 = projector (chartAmplitude q) := by
    change projector (amplitude (mixedTuple (toMixed q))) = _
    rw [mixedTuple_toMixed hk, amplitude_scale, projector_scale _ (pow_ne_zero _ (inv_ne_zero hk))]
    rfl
  have hm : rawMass a ≠ 0 := mass_nonzero h hk
  have he : normalizedGram (rayAmplitude u) = normalizedObservation q := by
    rw [hu, ← observation_of_projector (x := graphPoint (mixedTuple a))
      (p := amplitude (mixedTuple a)) (fun hz => hm (by simp [rawMass, hz, gram_trace, flatten])) rfl,
      observation_of_projector h hproj]
    rfl
  funext j
  change raw u j.castSucc = _
  rw [raw_eq_entries, entries_smul, ← he, normalizedGram, entries_smul]
  change τ / rawMass a * entries (gram (rayAmplitude u)) j.castSucc =
    τ * (((gram (rayAmplitude u)).trace.re)⁻¹ * entries (gram (rayAmplitude u)) j.castSucc)
  rw [hu]
  simp [rawMass, div_eq_mul_inv, mul_assoc]

/-- Invertibility of the raw tangent implies injectivity in the trace-one chart. -/
theorem injective_normalizedObservation_special (i : Fin 2) :
    let a := complexParameter (center i)
    let q := toFirst a
    q ∈ domain ∧ Injective (fderiv ℝ normalizedObservation q) := by
  let a := complexParameter (center i)
  let q := toFirst a
  let τ := rawTrace (raw (center i))
  let ψ := fun x : Parameters => pack (toMixed x) (τ / rawMass (toMixed x))
  let inverse := toFirst ∘ complexParameter
  obtain ⟨ham, ha, _⟩ := special_coordinates i
  have hk : q 3 ≠ 0 := inv_ne_zero ha
  have hto : toMixed q = a := toMixed_toFirst ha
  have hD : q ∈ domain := by
    intro hzero
    have he : amplitude (mixedTuple a) = 0 := by
      rw [← hto, mixedTuple_toMixed hk, amplitude_scale]
      rw [show amplitude (invariantTuple q) = 0 from hzero, smul_zero]
    exact ham he
  have hΨ : ψ q = center i := by
    change pack (toMixed q) (τ / rawMass (toMixed q)) = _
    rw [hto]
    dsimp only [τ]
    rw [raw_trace_eq]
    change pack a (center i 8 * rawMass a / rawMass a) = _
    have hm : rawMass a ≠ 0 := (gram_mass_pos _ ham).ne'
    rw [mul_div_cancel_right₀ _ hm, pack_unpack]
  have hmix := differentiableAt_toMixed hk
  have hmass := differentiable_rawMass.differentiableAt.comp q hmix
  have hdψ : DifferentiableAt ℝ ψ q := by
    apply differentiableAt_pi.mpr
    intro j
    have hx (k : Fin 4) := differentiableAt_pi.mp hmix k
    have hr (k : Fin 4) :=
      Complex.reCLM.differentiableAt.comp q (hx k)
    have hi (k : Fin 4) :=
      Complex.imCLM.differentiableAt.comp q (hx k)
    fin_cases j
    · exact hr 0
    · exact hi 0
    · exact hr 1
    · exact hi 1
    · exact hr 2
    · exact hi 2
    · exact hr 3
    · exact hi 3
    · change DifferentiableAt ℝ (fun x : Parameters => τ / rawMass (toMixed x)) q
      have hconst : DifferentiableAt ℝ (fun _ : Parameters => τ) q :=
        differentiableAt_const _
      have hdenom : DifferentiableAt ℝ (fun x : Parameters => rawMass (toMixed x)) q := hmass
      simp only [div_eq_mul_inv]
      exact hconst.fun_mul (hdenom.fun_inv (mass_nonzero hD hk))
  have hk' : ∀ᶠ x : Parameters in 𝓝 q, x 3 ≠ 0 :=
    (continuous_apply _).continuousAt.eventually_ne hk
  have hleft : inverse ∘ ψ =ᶠ[𝓝 q] id := by
    filter_upwards [hk'] with x hx
    change toFirst (complexParameter (pack (toMixed x) _)) = x
    rw [unpack_pack, toFirst_toMixed hx]
  let P : Matrix (Fin 4) (Fin 4) ℂ → Fin 9 → ℝ :=
    fun M => τ • PeriodicMPSFiveSitePhysicalObservation.readout M
  have hP : Differentiable ℝ P :=
    PeriodicMPSFiveSitePhysicalObservation.readout.differentiable.const_smul τ
  have heq : tangent ∘ ψ =ᶠ[𝓝 q] P ∘ normalizedObservation := by
    filter_upwards [hk', isOpen_domain.mem_nhds hD] with x hx hxd
    change tangent (pack (toMixed x) (τ / rawMass (toMixed x))) = P (normalizedObservation x)
    rw [packed_tangent hxd hx τ]
    exact funext fun j => by
      change τ * entries (normalizedObservation x) j.castSucc = _
      simp [P, PeriodicMPSFiveSitePhysicalObservation.readout_apply, smul_eq_mul]
  have hinv : DifferentiableAt ℝ inverse (ψ q) := by
    rw [hΨ]
    exact (differentiableAt_toFirst ha).comp _ differentiable_complexParameter.differentiableAt
  obtain ⟨L, hL⟩ := tangent_invertible i
  have hdT : DifferentiableAt ℝ tangent (ψ q) := hΨ.symm ▸ hL.differentiableAt
  have hdobs := (analyticAt_normalizedObservation q hD).differentiableAt
  refine ⟨hD, fun x y hxy => sub_eq_zero.mp ?_⟩
  let v := x - y
  change v = 0
  have hv : fderiv ℝ normalizedObservation q v = 0 := by
    rw [show v = x - y from rfl, map_sub, hxy, sub_self]
  have he : fderiv ℝ (tangent ∘ ψ) q v = 0 := by
    rw [heq.fderiv_eq (𝕜 := ℝ), fderiv_comp q hP.differentiableAt hdobs,
      ContinuousLinearMap.comp_apply]
    exact (congrArg (fderiv ℝ P (normalizedObservation q)) hv).trans (map_zero _)
  have hvψ : fderiv ℝ ψ q v = 0 := by
    rw [fderiv_comp q hdT hdψ, ContinuousLinearMap.comp_apply, hΨ, hL.fderiv] at he
    exact L.injective (he.trans L.map_zero.symm)
  have h := congrArg (fun d : Parameters →L[ℝ] Parameters => d v) (hleft.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_comp q hinv hdψ, ContinuousLinearMap.comp_apply, hvψ, map_zero, fderiv_id] at h
  exact h.symm

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialRegular
