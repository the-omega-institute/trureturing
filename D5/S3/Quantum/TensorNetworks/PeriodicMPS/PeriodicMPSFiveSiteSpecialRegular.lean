/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialRegular
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialRegular
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms]
   utility: none
   digest: The four special lifts have injective normalized differentials. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteRegularLocus

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialRegular

open Set hiding center
open Filter Function PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCompactChart
  PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteOrdinaryTrace PeriodicMPSFiveSiteTraceChart
  PeriodicMPSFiveSiteSpecialGerms PeriodicMPSFiveSiteLocalGraphs PeriodicMPSFiveSiteRegularLocus
  PeriodicMPSFiveSitePhysicalObservation PeriodicMPSFiveSiteNormalization
  PeriodicMPSFiveSiteJetCoordinates
open scoped Topology

open private tangent_invertible from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteLocalGraphs
open private fromFour
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
open private traceDirection pencil from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
open private pack unpack_pack squareTrace mixed special_coordinates amp massOf massOf_pos
  rebuild rebuild_center raw_rebuild affineDomain
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialGerms
open private rayAmplitude from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
open PeriodicMPSProjectiveCoordinates (projector projector_ratio)

noncomputable section

private def determinant (a : Q) : ℂ := a 0 - a 1

private def lastPencil (a : Q) : ℂ := a 2 + a 3 + a 3 ^ 2 * determinant a

private def ordinaryCoordinates (a : Q) : Parameters :=
  ![a 3, determinant a / squareTrace a, mixed a / squareTrace a, lastPencil a / squareTrace a]

private def alignedMixed (q : Parameters) : ℂ := q 2 - 2 * q 0 * q 1

private def affineCoordinates (q : Parameters) : Q :=
  let z := alignedMixed q
  ![(3 * q 1 - 1) / z, (2 * q 1 - 1) / z, (q 3 - q 0 * z - q 0 ^ 2 * q 1) / z, q 0]

private theorem decode_fromFour {a : Q} (ha : squareTrace a ≠ 0) :
    decode (fromFour a) = ordinaryCoordinates a := by
  let t : Fin 2 → ℂ := ![1, a 3]
  let p : Fin 6 → ℂ := ![squareTrace a, squareTrace a * a 3,
    squareTrace a * a 3 ^ 2, determinant a, mixed a, lastPencil a]
  have ht := projector_ratio t 1 0 one_ne_zero
  have hp (i : Fin 6) := projector_ratio p i 0 (show p 0 ≠ 0 from ha)
  funext i
  fin_cases i
  · change projector t 1 0 / projector t 0 0 = a 3
    exact ht.trans (div_one _)
  · exact hp 3
  · exact hp 4
  · exact hp 5

private theorem alignedMixed_ordinaryCoordinates {a : Q} (ha : squareTrace a ≠ 0) :
    alignedMixed (ordinaryCoordinates a) = (squareTrace a)⁻¹ := by
  change mixed a / squareTrace a - 2 * a 3 * (determinant a / squareTrace a) = _
  unfold mixed determinant
  field_simp [ha]
  ring

private theorem affineCoordinates_ordinaryCoordinates {a : Q} (ha : squareTrace a ≠ 0) :
    affineCoordinates (ordinaryCoordinates a) = a := by
  let b := squareTrace a
  let d := determinant a
  have hb : b ≠ 0 := ha
  have hdec := alignedMixed_ordinaryCoordinates ha
  have hx : 3 * d - b = a 0 := by dsimp [b, d, determinant, squareTrace]; ring
  have hy : 2 * d - b = a 1 := by dsimp [b, d, determinant, squareTrace]; ring
  have hw : lastPencil a - a 3 - a 3 ^ 2 * d = a 2 := by dsimp [lastPencil, d]; ring
  funext i
  fin_cases i
  · change (3 * (d / b) - 1) / alignedMixed (ordinaryCoordinates a) = a 0
    rw [hdec, div_inv_eq_mul]
    change (3 * (d / b) - 1) * b = _
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hb, one_mul, hx]
  · change (2 * (d / b) - 1) / alignedMixed (ordinaryCoordinates a) = a 1
    rw [hdec, div_inv_eq_mul]
    change (2 * (d / b) - 1) * b = _
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hb, one_mul, hy]
  · change (lastPencil a / b - a 3 * alignedMixed (ordinaryCoordinates a) -
        a 3 ^ 2 * (d / b)) / alignedMixed (ordinaryCoordinates a) = a 2
    rw [hdec, div_inv_eq_mul]
    change (lastPencil a / b - a 3 * b⁻¹ - a 3 ^ 2 * (d / b)) * b = _
    calc
      _ = lastPencil a - a 3 - a 3 ^ 2 * d := by field_simp [hb] <;> ring
      _ = a 2 := hw
  · rfl

private theorem encode_toAffine {q : Parameters} (hq : q ∈ domain) (hz : alignedMixed q ≠ 0) :
    encode q = fromFour (affineCoordinates q) := by
  have hu : coordinates 1 (q 0) (q 1) (q 3) (q 0 - q 2) ≠ 0 := by
    rw [← amplitude_eq q]
    exact hq
  let u : Inputs := ⟨![1, q 0, q 1, q 3, q 0 - q 2], hu⟩
  have he : ordinary u = encode q := by
    have hm : q 0 - (q 0 - q 2) = q 2 := by ring
    simp [ordinary, encode, u, traceDirection, pencil, amplitude_eq, hm]
  have hs : u.val 1 = u.val 0 * q 0 := by simp [u]
  have hz' : alignedMixed q = u.val 0 * u.val 1 - u.val 4 - 2 * q 0 * u.val 2 := by
    simp [u, alignedMixed] <;> ring
  have h := ordinary_eq_affine u one_ne_zero (q 0) hs (alignedMixed q) hz' hz
  simpa [he, fromFour, affineCoordinates, u] using h

private theorem squareTrace_affineCoordinates {q : Parameters} (hz : alignedMixed q ≠ 0) :
    squareTrace (affineCoordinates q) = (alignedMixed q)⁻¹ := by
  change 2 * ((3 * q 1 - 1) / alignedMixed q) - 3 * ((2 * q 1 - 1) / alignedMixed q) = _
  field_simp [hz]
  ring

private theorem differentiableAt_affineCoordinates {q : Parameters} (hz : alignedMixed q ≠ 0) :
    DifferentiableAt ℝ affineCoordinates q := by
  apply differentiableAt_pi.mpr
  intro i
  have hz' : DifferentiableAt ℝ alignedMixed q := by unfold alignedMixed; fun_prop
  have hzi : DifferentiableAt ℝ (fun x => (alignedMixed x)⁻¹) q := hz'.fun_inv hz
  fin_cases i <;> simp [affineCoordinates, div_eq_mul_inv]
  · exact (show DifferentiableAt ℝ (fun x : Parameters => 3 * x 1 - 1) q by fun_prop).fun_mul hzi
  · exact (show DifferentiableAt ℝ (fun x : Parameters => 2 * x 1 - 1) q by fun_prop).fun_mul hzi
  · have hn : DifferentiableAt ℝ
        (fun x : Parameters => x 3 - x 0 * alignedMixed x - x 0 ^ 2 * x 1) q := by
      fun_prop
    exact hn.fun_mul hzi
  · fun_prop

private theorem differentiableAt_ordinaryCoordinates {a : Q} (ha : squareTrace a ≠ 0) :
    DifferentiableAt ℝ ordinaryCoordinates a := by
  apply differentiableAt_pi.mpr
  intro i
  have ha' : DifferentiableAt ℝ squareTrace a := by unfold squareTrace; fun_prop
  have hai : DifferentiableAt ℝ (fun x => (squareTrace x)⁻¹) a := ha'.fun_inv ha
  fin_cases i <;> simp [ordinaryCoordinates, div_eq_mul_inv]
  · fun_prop
  · exact (show DifferentiableAt ℝ determinant a by unfold determinant; fun_prop).fun_mul hai
  · exact (show DifferentiableAt ℝ mixed a by unfold mixed; fun_prop).fun_mul hai
  · exact (show DifferentiableAt ℝ lastPencil a by unfold lastPencil determinant; fun_prop
    ).fun_mul hai

private theorem differentiable_complexParameter : Differentiable ℝ complexParameter := by
  have h (a b : Fin 9) : Differentiable ℝ (fun u : E => (⟨u a, u b⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.differentiable.comp
      ((differentiable_apply a).prodMk (differentiable_apply b))
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> exact h _ _

private theorem differentiable_massOf : Differentiable ℝ massOf := by
  let rawUnit (a : Q) : E := pack a 1
  have hp : Differentiable ℝ rawUnit := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [rawUnit, pack] <;> fun_prop
  have hr : Differentiable ℝ (raw (R := ℝ)) :=
    fun x => (analyticAt_pi_iff.mpr
      (fun i => PeriodicMPSFiveSiteAnalyticDerivative.analytic_raw x i)).differentiableAt
  have h : massOf = rawTrace ∘ raw ∘ rawUnit := by
    funext a
    change massOf a = rawTrace (raw (pack a 1))
    rw [raw_trace_eq]
    have he : rayAmplitude (pack a 1) = amp a := by unfold rayAmplitude amp; rw [unpack_pack]
    change massOf a = (1 : ℝ) * mass (rayAmplitude (pack a 1))
    rw [one_mul, he]
    rfl
  rw [h]
  have ht : Differentiable ℝ rawTrace := by unfold rawTrace; fun_prop
  exact ht.comp (hr.comp hp)

private theorem differentiableAt_packedAffine {q : Parameters} (hz : alignedMixed q ≠ 0)
    (τ : ℝ) :
    DifferentiableAt ℝ (fun x => pack (affineCoordinates x) (τ / massOf (affineCoordinates x))) q := by
  apply differentiableAt_pi.mpr
  intro i
  have h := differentiableAt_affineCoordinates hz
  have hx (j : Fin 4) : DifferentiableAt ℝ (fun a => affineCoordinates a j) q :=
    differentiableAt_pi.mp h j
  have hm : DifferentiableAt ℝ (fun a => massOf (affineCoordinates a)) q :=
    differentiable_massOf.differentiableAt.comp q h
  fin_cases i <;> simp [pack, div_eq_mul_inv] <;> try fun_prop
  exact (differentiableAt_const τ).fun_mul (hm.fun_inv (massOf_pos _).ne')

/-- Injectivity of the raw tangential derivative implies injectivity at fixed trace. -/
theorem specialPoint_regular (i : Fin 4) : decode (specialPoint i).val ∈ regular := by
  let a := complexParameter (center i)
  let q := decode (specialPoint i).val
  let τ := rawTrace (raw (center i))
  let ψ := fun x : Parameters => pack (affineCoordinates x) (τ / massOf (affineCoordinates x))
  let inverse := ordinaryCoordinates ∘ complexParameter
  have ha := (special_coordinates i).1
  have hm : mixed a ≠ 0 := by
    change mixed (complexParameter (center i)) ≠ 0
    rw [(special_coordinates i).2.1]
    exact one_ne_zero
  have hq : q = ordinaryCoordinates a := decode_fromFour ha
  have hD : q ∈ domain := (specialPoint_in_ordinary i).2.2
  have hz : alignedMixed q ≠ 0 := by rw [hq, alignedMixed_ordinaryCoordinates ha]; exact inv_ne_zero ha
  have haff : affineCoordinates q = a := by rw [hq, affineCoordinates_ordinaryCoordinates ha]
  have hτ : τ ≠ 0 := by
    unfold τ
    rw [raw_trace_eq, (special_coordinates i).2.2, one_mul]
    exact (massOf_pos a).ne'
  have hdψ : DifferentiableAt ℝ ψ q := differentiableAt_packedAffine hz τ
  have hΨ : ψ q = center i := by
    have hInv : affineInverse (specialPoint i).val = a := affineInverse_affine _ _ _ _ hm
    change pack (affineCoordinates q) (τ / massOf (affineCoordinates q)) = _
    rw [haff, ← hInv]
    exact rebuild_center i
  have hne : ∀ᶠ x in 𝓝 q, alignedMixed x ≠ 0 ∧ mixed (affineCoordinates x) ≠ 0 := by
    have h₁ : ContinuousAt alignedMixed q := by unfold alignedMixed; fun_prop
    have h₂ : ContinuousAt (mixed ∘ affineCoordinates) q := by
      have hh : Continuous mixed := by unfold mixed; fun_prop
      exact hh.continuousAt.comp (differentiableAt_affineCoordinates hz).continuousAt
    exact (h₁.eventually_ne hz).and (h₂.eventually_ne (by simpa only [Function.comp_apply, haff]))
  have hleft : inverse ∘ ψ =ᶠ[𝓝 q] id := by
    filter_upwards [hne, isOpen_domain.mem_nhds hD] with x hx hxd
    change ordinaryCoordinates (complexParameter (pack (affineCoordinates x) _)) = x
    rw [unpack_pack, ← decode_fromFour (by
      rw [squareTrace_affineCoordinates hx.1]
      exact inv_ne_zero hx.1), ← encode_toAffine hxd hx.1, decode_encode]
  have heq : tangent ∘ ψ =ᶠ[𝓝 q] fun x => τ • observe x := by
    filter_upwards [hne, isOpen_domain.mem_nhds hD] with x hx hxd
    have henc := encode_toAffine hxd hx.1
    have hC := affineDomain (show squareTrace (affineCoordinates x) ≠ 0 by
      rw [squareTrace_affineCoordinates hx.1]
      exact inv_ne_zero hx.1) hx.2
    have hencC := henc.symm ▸ hC
    have hInv : affineInverse (encode x) = affineCoordinates x := by
      rw [henc]
      exact affineInverse_affine _ _ _ _ hx.2
    have hψ : ψ x = rebuild (encode x) τ := by simp only [ψ, rebuild, hInv]
    have hraw := raw_rebuild (encode_mem_source hxd) hencC hτ
    have he : measured (encode x) = observe x := observe_encode ⟨x, hxd⟩
    rw [he, ← hψ] at hraw
    funext j
    simp [Function.comp_apply, tangent, hraw, restoreEntries, Pi.smul_apply, smul_eq_mul]
  have hinv : DifferentiableAt ℝ inverse (ψ q) := by
    rw [hΨ]
    exact (differentiableAt_ordinaryCoordinates ha).comp _ differentiable_complexParameter.differentiableAt
  obtain ⟨L, hL⟩ := tangent_invertible i
  have hdT : DifferentiableAt ℝ tangent (ψ q) := hΨ.symm ▸ hL.differentiableAt
  have hdobs := (analyticAt_observe q hD).differentiableAt
  let scale : Readings → Readings := fun x => τ • x
  have hdscale : DifferentiableAt ℝ scale (observe q) :=
    (differentiableAt_id (𝕜 := ℝ) (x := observe q)).const_smul τ
  refine ⟨hD, fun x y hxy => sub_eq_zero.mp ?_⟩
  let v := x - y
  change v = 0
  have hv : fderiv ℝ observe q v = 0 := by rw [show v = x - y from rfl, map_sub, hxy, sub_self]
  have he : fderiv ℝ (tangent ∘ ψ) q v = 0 := by
    have h := heq.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (tangent ∘ ψ) q = fderiv ℝ (scale ∘ observe) q at h
    rw [h, fderiv_comp q hdscale hdobs, ContinuousLinearMap.comp_apply, hv, map_zero]
  have hvψ : fderiv ℝ ψ q v = 0 := by
    rw [fderiv_comp q hdT hdψ, ContinuousLinearMap.comp_apply, hΨ, hL.fderiv] at he
    exact L.injective (he.trans L.map_zero.symm)
  have h := congrArg (fun d : Parameters →L[ℝ] Parameters => d v) (hleft.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_comp q hinv hdψ, ContinuousLinearMap.comp_apply, hvψ, map_zero, fderiv_id] at h
  exact h.symm

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialRegular
