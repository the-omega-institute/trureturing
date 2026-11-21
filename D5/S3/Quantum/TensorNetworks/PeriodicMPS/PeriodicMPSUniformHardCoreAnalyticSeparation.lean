/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetGerm, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticChart]
   utility: none
   digest: Matching normalized regular values and coherence at the opposite slope gives a nonzero quartic difference in the actual 11,11 population. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetGerm
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticChart
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Transfer of the certified normalized quartic to actual paired chart paths. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticSeparation

open PeriodicMPSUniformHardCoreJetElimination (Path original)
open PeriodicMPSUniformHardCoreNormalizedJet
open PeriodicMPSUniformHardCoreFirstJet (Coord witness cores entry component regularReadout)
open PeriodicMPSUniformHardCoreFoldCurvature
  (nullDirection nullSlope regular_kernel_iff)
open PeriodicMPSUniformHardCoreQuarticSign (quartic quartic_ne_zero)
open PeriodicMPSUniformHardCoreHigherJet (pathCoordinate pathTerms)
open PeriodicMPSUniformHardCoreAnalyticChart
  (HasSeparatedPairs hasSeparatedPairs_of_quartic_expansion exists_generic_actual_reconstruction
    analyticAt_straighten)
open PeriodicMPSTwoSiteAmbiguity (rawTwo flattening_entry)
open PeriodicMPSParentIntersection (Word Bond twoFlattening)
open PeriodicMPSUniformHardCoreTransferRecurrence (hardCoreChart)
open PeriodicMPSUniformHardCoreLocalization
open Filter Asymptotics Polynomial
open scoped Topology

open private twoMass normalizedTwo from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
open private mass_pos_witness cores_path path from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature
open private analyticAt_flattening analyticAt_twoMass from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticChart

noncomputable section

private theorem strict_difference {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Coord → F} (hf : ContDiffAt ℝ 1 f witness)
    {z p : ℝ → Coord} (hz : Tendsto z (𝓝 0) (𝓝 witness))
    (hp : Tendsto p (𝓝 0) (𝓝 witness)) {d : ℕ} {u : Coord}
    (h : (fun ε => z ε - p ε - ε ^ d • u) =o[𝓝 0] (fun ε => ε ^ d))
    (hu : fderiv ℝ f witness u = 0) :
    (fun ε => f (z ε) - f (p ε)) =o[𝓝 0] (fun ε => ε ^ d) := by
  let L := fderiv ℝ f witness
  have hlinear : (fun ε => L (z ε - p ε)) =o[𝓝 0] (fun ε => ε ^ d) := by
    refine ((L.isBigO_comp _ _).trans_isLittleO h).congr_left fun ε => ?_
    simp [L, hu]
  have hdiff : (fun ε => z ε - p ε) =O[𝓝 0] (fun ε => ε ^ d) := by
    have hscalar : (fun ε : ℝ => ε ^ d • u) =O[𝓝 0] (fun ε => ε ^ d) :=
      IsBigO.of_bound ‖u‖ (Eventually.of_forall fun ε => by rw [norm_smul, mul_comm])
    exact (h.isBigO.add hscalar).congr_left fun ε => sub_add_cancel _ _
  have hstrict := (hf.hasStrictFDerivAt (by decide)).isLittleO.comp_tendsto (hz.prodMk_nhds hp)
  exact ((hstrict.trans_isBigO hdiff).add hlinear).congr_left fun ε => sub_add_cancel _ _

private def normalizedAmplitude (imag : Bool) (r : ℕ) (w : Word (r + 2)) (x : Coord) : ℝ :=
  (if imag then (twoFlattening (cores x) r (1, 1) w).im
    else (twoFlattening (cores x) r (1, 1) w).re) / Real.sqrt (twoMass (cores x) r)

private theorem normalizedAmplitude_smooth (imag : Bool) (r : ℕ) (hr : 3 ≤ r)
    (w : Word (r + 2)) : ContDiffAt ℝ 1 (normalizedAmplitude imag r w) witness := by
  have hA := analyticAt_flattening r (1, 1) w witness
  have hZ := analyticAt_twoMass r witness
  have hpos := mass_pos_witness r hr
  have hS : ContDiffAt ℝ 1 (fun x : Coord => Real.sqrt (twoMass (cores x) r)) witness :=
    (Real.contDiffAt_sqrt hpos.ne').comp witness hZ.contDiffAt
  have hne := (Real.sqrt_pos.2 hpos).ne'
  cases imag
  · exact ((Complex.reCLM.analyticAt _).comp hA).contDiffAt.div hS hne
  · exact ((Complex.imCLM.analyticAt _).comp hA).contDiffAt.div hS hne

private theorem normalizedAmplitude_nullLine (imag : Bool) (r : ℕ) (w : Word (r + 2))
    (t : ℝ) : normalizedAmplitude imag r w (witness + t • nullDirection (r + 4)) = 0 := by
  have he : twoFlattening (cores (witness + t • nullDirection (r + 4))) r (1, 1) w = 0 := by
    change twoFlattening (cores (path r t)) r (1, 1) w = 0
    rw [cores_path, flattening_entry]
    have hB (a b : ℂ) :
        (hardCoreChart a b 0 0 1 : Bond) * hardCoreChart a b 0 0 1 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hardCoreChart, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hB]
  cases imag <;> simp [normalizedAmplitude, he]

private theorem normalizedAmplitude_kills_null (imag : Bool) (r : ℕ) (hr : 3 ≤ r)
    (w : Word (r + 2)) :
    fderiv ℝ (normalizedAmplitude imag r w) witness (nullDirection (r + 4)) = 0 := by
  have hline : HasDerivAt (fun t : ℝ => witness + t • nullDirection (r + 4))
      (nullDirection (r + 4)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (nullDirection (r + 4))).const_add witness
  have hf := (normalizedAmplitude_smooth imag r hr w).differentiableAt (by decide)
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  simp only [Function.comp_def, normalizedAmplitude_nullLine] at h
  exact h.unique (hasDerivAt_const 0 (0 : ℝ))

private theorem forbidden_eq_sum (r : ℕ) (x : Coord) (h : 0 < twoMass (cores x) r) :
    component false r 6 x =
      ∑ w : Word (r + 2), (normalizedAmplitude false r w x ^ 2 +
        normalizedAmplitude true r w x ^ 2) := by
  change (((twoMass (cores x) r)⁻¹ • rawTwo (cores x) r) (1, 1) (1, 1)).re = _
  simp only [Matrix.smul_apply, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, normalizedAmplitude, Bool.false_eq_true, ite_false, ite_true, div_pow,
    Real.sq_sqrt h.le, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

private theorem composed_isBigO {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Coord → F} (hf : DifferentiableAt ℝ f witness)
    {z : ℝ → Coord} (hz : Tendsto z (𝓝 0) (𝓝 witness))
    (h : (fun ε => z ε - witness) =O[𝓝 0] (fun ε => ε)) :
    (fun ε => f (z ε) - f witness) =O[𝓝 0] (fun ε => ε) := by
  have h₁ := (hf.hasFDerivAt.isLittleO.comp_tendsto hz).trans_isBigO h
  have h₂ := ((fderiv ℝ f witness).isBigO_comp (fun ε => z ε - witness) _).trans h
  exact (h₁.isBigO.add h₂).congr_left fun _ => sub_add_cancel _ _

private theorem forbidden_difference (r : ℕ) (hr : 3 ≤ r) {z p : ℝ → Coord}
    (hz : Tendsto z (𝓝 0) (𝓝 witness)) (hp : Tendsto p (𝓝 0) (𝓝 witness))
    (hz₁ : (fun ε => z ε - witness) =O[𝓝 0] (fun ε => ε))
    (hp₁ : (fun ε => p ε - witness) =O[𝓝 0] (fun ε => ε))
    {a₃ : ℝ} (hc : (fun ε => z ε - p ε - ε^3 • (a₃ • nullDirection (r + 4)))
      =o[𝓝 0] (fun ε => ε^3)) :
    (fun ε => component false r 6 (z ε) - component false r 6 (p ε))
      =o[𝓝 0] (fun ε => ε^4) := by
  have hs (imag : Bool) (w : Word (r + 2)) :
      (fun ε => normalizedAmplitude imag r w (z ε) ^ 2 -
        normalizedAmplitude imag r w (p ε) ^ 2) =o[𝓝 0] (fun ε => ε^4) := by
    let f := normalizedAmplitude imag r w
    have hf := normalizedAmplitude_smooth imag r hr w
    have hnull : fderiv ℝ f witness (a₃ • nullDirection (r + 4)) = 0 := by
      rw [map_smul, normalizedAmplitude_kills_null imag r hr w, smul_zero]
    have h₀ : f witness = 0 := by simpa [f] using normalizedAmplitude_nullLine imag r w 0
    have hz' := composed_isBigO (hf.differentiableAt (by decide)) hz hz₁
    have hp' := composed_isBigO (hf.differentiableAt (by decide)) hp hp₁
    rw [show normalizedAmplitude imag r w witness = 0 from h₀] at hz' hp'
    simp only [sub_zero] at hz' hp'
    exact ((strict_difference hf hz hp hc hnull).mul_isBigO (hz'.add hp')).congr
      (fun ε => by change (f (z ε) - f (p ε)) * (f (z ε) + f (p ε)) = _; ring)
      (fun ε => (pow_succ ε 3).symm)
  have hsum := IsLittleO.sum (s := Finset.univ)
    (fun w (_ : w ∈ Finset.univ) => (hs false w).add (hs true w))
  refine hsum.congr' ?_ EventuallyEq.rfl
  have hpos := (analyticAt_twoMass r witness).continuousAt.eventually
    (Ioi_mem_nhds (mass_pos_witness r hr))
  filter_upwards [hz hpos, hp hpos] with ε hzε hpε
  rw [forbidden_eq_sum r (z ε) hzε, forbidden_eq_sum r (p ε) hpε, ← Finset.sum_sub_distrib]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem eventually_parameter_ne_zero : ∀ᶠ ε : ℝ in 𝓝[≠] (0 : ℝ), ε ≠ 0 :=
  eventually_mem_nhdsWithin (s := {0}ᶜ)

/-- Uniqueness of the Taylor coefficients of a real polynomial up to the
order of a little-o bound on its evaluation. -/
private theorem coefficients_zero_of_littleO (p : Polynomial ℝ) (d : ℕ)
    (h : (fun ε => p.eval ε) =o[𝓝[≠] (0 : ℝ)] (fun ε => ε ^ d)) :
    ∀ k ≤ d, p.coeff k = 0 := by
  have eval_zero (q : Polynomial ℝ) (j : ℕ)
      (hq : (fun ε => q.eval ε) =o[𝓝[≠] (0 : ℝ)] (fun ε => ε ^ j)) : q.coeff 0 = 0 := by
    have hb : (fun ε : ℝ => ε ^ j) =O[𝓝[≠] 0] (fun _ => (1 : ℝ)) :=
      (isBigO_one_iff (F := ℝ)).mpr (((continuous_id.pow j).continuousAt.tendsto (x := (0 : ℝ))).mono_left
        nhdsWithin_le_nhds).norm.isBoundedUnder_le
    have h₀ := (isLittleO_one_iff ℝ).mp (hq.trans_isBigO hb)
    rw [coeff_zero_eq_eval_zero]
    exact tendsto_nhds_unique (q.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h₀
  induction d generalizing p with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    exact eval_zero p 0 h
  | succ d ih =>
    have hz := eval_zero p (d+1) h
    have hdecomp (ε : ℝ) : p.eval ε = ε * p.divX.eval ε := by
      have he := congrArg (Polynomial.eval ε) (X_mul_divX_add p)
      simpa only [hz, map_zero, add_zero, eval_mul, eval_X] using he.symm
    have hq : (fun ε => p.divX.eval ε) =o[𝓝[≠] (0 : ℝ)] (fun ε => ε ^ d) := by
      apply isLittleO_of_tendsto' (eventually_parameter_ne_zero.mono fun ε hε hpow =>
        (pow_ne_zero d hε hpow).elim)
      apply h.tendsto_div_nhds_zero.congr'
      filter_upwards [eventually_parameter_ne_zero] with ε hε
      rw [hdecomp, pow_succ]
      field_simp
    intro k hk
    cases k with
    | zero => exact hz
    | succ k =>
      rw [← coeff_divX]
      exact ih p.divX hq k (by omega)

private theorem readout_sub_trunc_littleO (imag : Bool) (r : ℕ) (hr : 3 ≤ r)
    (x : Path) (row : Fin 8) :
    (fun ε => component imag r row (coordinates (r+4) x ε) -
      (truncatedReadout 4 imag (r+4) x row).eval ε)
      =o[𝓝 (0 : ℝ)] (fun ε => ε ^ 3) := by
  obtain ⟨g, hg, he⟩ := polynomial_readout_remainder 4 imag r hr x row
  have hsmall : (fun ε : ℝ => ε * g ε) =o[𝓝 0] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by
      have hc : ContinuousAt (fun ε : ℝ => ε * g ε) 0 :=
        continuous_id.continuousAt.mul hg
      simpa only [zero_mul] using hc.tendsto)
  refine ((hsmall.mul_isBigO (isBigO_refl (fun ε : ℝ => ε^3) (𝓝 0))).congr
    (fun ε => ?_) (fun ε => one_mul _)).congr' (he.mono fun _ h => h.symm) EventuallyEq.rfl
  ring

private theorem coefficient_eq_of_readout_littleO (imag : Bool) (r : ℕ) (hr : 3 ≤ r)
    (x : Path) (row : Fin 8)
    (h : (fun ε => component imag r row (coordinates (r+4) x ε) -
      component imag r row (coordinates (r+4) original ε))
      =o[𝓝 (0 : ℝ)] (fun ε => ε^3)) :
    ∀ k ≤ 3, normalizedCoeff imag (r+4) x row k = normalizedCoeff imag (r+4) original row k := by
  have hx := readout_sub_trunc_littleO imag r hr x row
  have hx₀ := readout_sub_trunc_littleO imag r hr original row
  let p := truncatedReadout 4 imag (r+4) x row - truncatedReadout 4 imag (r+4) original row
  have hp : (fun ε => p.eval ε) =o[𝓝 (0 : ℝ)] (fun ε => ε^3) :=
    ((h.sub hx).add hx₀).congr_left fun ε => by
      simp only [p, eval_sub]
      ring
  intro k hk
  have hcoeff := coefficients_zero_of_littleO p 3 (hp.mono nhdsWithin_le_nhds) k hk
  simpa [p, truncatedReadout, coeff_sub, PowerSeries.coeff_trunc, PowerSeries.coeff_mk,
    show k < 4 by omega, sub_eq_zero] using hcoeff

private theorem regular_coeff_eq (r : ℕ) (hr : 3 ≤ r) (x : Path)
    (h : (fun ε => regularReadout r (coordinates (r+4) x ε) -
      regularReadout r (coordinates (r+4) original ε)) =o[𝓝 (0 : ℝ)] (fun ε => ε^3)) :
    ∀ k ≤ 3, regularCoeff (r+4) x k = regularCoeff (r+4) original k := by
  have he (i : Fin 4) := isLittleO_pi.mp (isBigO_fst_prod'.trans_isLittleO h) i
  have hi (i : Fin 3) := isLittleO_pi.mp (isBigO_snd_prod'.trans_isLittleO h) i
  intro k hk
  have hp := coefficient_eq_of_readout_littleO false r hr x 1 (he 0) k hk
  have hq := coefficient_eq_of_readout_littleO false r hr x 2 (he 1) k hk
  have hw := coefficient_eq_of_readout_littleO false r hr x 4 (he 2) k hk
  have hv := coefficient_eq_of_readout_littleO false r hr x 5 (he 3) k hk
  have hz := coefficient_eq_of_readout_littleO true r hr x 3 (hi 0) k hk
  have hw' := coefficient_eq_of_readout_littleO true r hr x 4 (hi 1) k hk
  have hv' := coefficient_eq_of_readout_littleO true r hr x 5 (hi 2) k hk
  unfold regularCoeff
  rw [hp, hq, hw, hv, hz, hw', hv']

private def imagVector (v : Fin 4 → ℝ) : Coord := fun i => (v i : ℂ) * Complex.I
private def realVector (v : Fin 4 → ℝ) : Coord := fun i => (v i : ℂ)

private theorem coordinates_formula (n : ℕ) (x : Path) (ε : ℝ) :
    coordinates n x ε = witness +
      ε • imagVector ![x.t, (3 - 2 * ratio n) * x.t, 1, 0] +
      ε^2 • realVector ![x.a₂, x.b₂, x.c₂, x.d₂] +
      ε^3 • imagVector ![0, x.b₃, x.c₃, x.d₃] +
      ε^4 • realVector ![x.a₄, x.b₄, x.c₄, x.d₄] := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply]
  fin_cases i <;>
    simp [coordinates, parameters, pathCoordinate, pathTerms, Fin.sum_univ_succ,
      witness, imagVector, realVector, Complex.real_smul,
      pow_succ] <;> ring

@[simp] theorem coordinates_zero (n : ℕ) (x : Path) : coordinates n x 0 = witness := by
  simp [coordinates_formula]

private theorem coordinates_hasDerivAt (n : ℕ) (x : Path) :
    HasDerivAt (coordinates n x) (imagVector ![x.t, (3 - 2 * ratio n) * x.t, 1, 0]) 0 := by
  have he := funext (coordinates_formula n x)
  rw [he]
  have h₁ := (hasDerivAt_id (0 : ℝ)).smul_const
    (imagVector ![x.t, (3 - 2 * ratio n) * x.t, 1, 0])
  have h₂ := ((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (realVector ![x.a₂, x.b₂, x.c₂, x.d₂])
  have h₃ := ((hasDerivAt_id (0 : ℝ)).pow 3).smul_const (imagVector ![0, x.b₃, x.c₃, x.d₃])
  have h₄ := ((hasDerivAt_id (0 : ℝ)).pow 4).smul_const (realVector ![x.a₄, x.b₄, x.c₄, x.d₄])
  have h := (((h₁.const_add witness).add h₂).add h₃).add h₄
  convert h using 1 <;> first | rfl | norm_num [id]

private theorem coordinates_isBigO (n : ℕ) (x : Path) :
    (fun ε => coordinates n x ε - witness) =O[𝓝 (0 : ℝ)] (fun ε => ε) := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp (coordinates_hasDerivAt n x)).isBigO
  have hlinear :
      (fun ε : ℝ => ε • imagVector ![x.t, (3 - 2 * ratio n) * x.t, 1, 0])
        =O[𝓝 0] (fun ε => ε) := IsBigO.of_bound _ (Eventually.of_forall fun ε => by rw [norm_smul, mul_comm])
  simpa only [zero_add, coordinates_zero, sub_add_cancel, ← Pi.add_apply] using h.add hlinear

/-- Exact matching on the regular outputs and the fold coherence transfers the
certified quartic to a fourth-order chart germ with a free cubic null term.
The coordinate error is little-o through order three. -/
theorem forbidden_expansion_of_matched_taylor (r : ℕ) (hr : 3 ≤ r)
    {z : ℝ → Coord} (x : Path) (a₃ : ℝ) (ht : x.t = oppositeSlope (r+4))
    (hjet : (fun ε => z ε - coordinates (r+4) x ε -
      ε^3 • (a₃ • nullDirection (r+4))) =o[𝓝 (0 : ℝ)] (fun ε => ε^3))
    (hpair : ∀ᶠ ε in 𝓝 (0 : ℝ),
      regularReadout r (z ε) = regularReadout r (coordinates (r+4) original ε) ∧
      component false r 3 (z ε) = component false r 3 (coordinates (r+4) original ε)) :
    Tendsto z (𝓝 (0 : ℝ)) (𝓝 witness) ∧
    (fun ε => component false r 6 (z ε) -
      component false r 6 (coordinates (r+4) original ε) - quartic (r+4) * ε^4)
      =o[𝓝 (0 : ℝ)] (fun ε => ε^4) := by
  let p := coordinates (r+4) x
  have hp : Tendsto p (𝓝 (0 : ℝ)) (𝓝 witness) := by
    simpa [p, ContinuousAt] using (coordinates_hasDerivAt (r+4) x).continuousAt
  have hp₁ := coordinates_isBigO (r+4) x
  have hscalar : (fun ε : ℝ => ε^3 • (a₃ • nullDirection (r+4)))
      =O[𝓝 0] (fun ε => ε^3) := IsBigO.of_bound _ (Eventually.of_forall fun ε => by rw [norm_smul, mul_comm])
  have hdiff : (fun ε => z ε - p ε) =O[𝓝 (0 : ℝ)] (fun ε => ε) := by
    have h := (hjet.isBigO.add hscalar).congr_left fun ε => sub_add_cancel _ _
    exact h.trans ((isLittleO_pow_id (𝕜 := ℝ) (by decide : 1 < 3)).isBigO)
  have hz₁ : (fun ε => z ε - witness) =O[𝓝 (0 : ℝ)] (fun ε => ε) :=
    (hdiff.add hp₁).congr_left fun ε => sub_add_sub_cancel _ _ _
  have hz : Tendsto z (𝓝 (0 : ℝ)) (𝓝 witness) := by
    have h := hz₁.trans_tendsto (continuous_id.continuousAt.tendsto (x := (0 : ℝ)))
    simpa using h.add (tendsto_const_nhds (x := witness))
  have hRsmooth : ContDiffAt ℝ 1 (regularReadout r) witness :=
    (analyticAt_straighten r hr).contDiffAt.fst
  have hnull : fderiv ℝ (regularReadout r) witness (a₃ • nullDirection (r+4)) = 0 :=
    (regular_kernel_iff r hr _).mpr ⟨a₃, rfl⟩
  have hR := (strict_difference hRsmooth hz hp hjet hnull).neg_left
  have hR' : (fun ε => regularReadout r (p ε) -
      regularReadout r (coordinates (r+4) original ε)) =o[𝓝 (0 : ℝ)] (fun ε => ε^3) :=
    hR.congr' (hpair.mono fun ε hε => by change -(regularReadout r (z ε) - regularReadout r (p ε)) = _; rw [neg_sub, hε.1]) EventuallyEq.rfl
  have hP := opposite_polynomial_forbidden_expansion r hr x ht (regular_coeff_eq r hr x hR')
  refine ⟨hz, ((forbidden_difference r hr hz hp hz₁ hp₁ hjet).add hP).congr_left ?_⟩
  intro ε
  dsimp [p]
  ring

/-- The analytic partner and the fixed reference path supply separated pairs
at every chain length `r + 4 ≥ 7`. -/
theorem hasSeparatedPairs_of_matched_taylor (r : ℕ) (hr : 3 ≤ r)
    {z : ℝ → Coord} (x : Path) (a₃ : ℝ) (ht : x.t = oppositeSlope (r+4))
    (hjet : (fun ε => z ε - coordinates (r+4) x ε -
      ε^3 • (a₃ • nullDirection (r+4))) =o[𝓝 (0 : ℝ)] (fun ε => ε^3))
    (hpair : ∀ᶠ ε in 𝓝 (0 : ℝ),
      regularReadout r (z ε) = regularReadout r (coordinates (r+4) original ε) ∧
      component false r 3 (z ε) = component false r 3 (coordinates (r+4) original ε)) :
    HasSeparatedPairs r := by
  obtain ⟨hz, hquartic⟩ := forbidden_expansion_of_matched_taylor r hr x a₃ ht hjet hpair
  have hx : Tendsto (coordinates (r+4) original) (𝓝 (0 : ℝ)) (𝓝 witness) := by
    simpa [ContinuousAt] using (coordinates_hasDerivAt (r+4) original).continuousAt
  exact hasSeparatedPairs_of_quartic_expansion (hz.mono_left nhdsWithin_le_nhds)
    (hx.mono_left nhdsWithin_le_nhds)
    ((hpair.mono fun _ he => Prod.ext he.1 he.2).filter_mono nhdsWithin_le_nhds)
    (hquartic.mono nhdsWithin_le_nhds) (quartic_ne_zero (by omega : 7 ≤ r+4))

private theorem nullSlope_eq (n : ℕ) : -nullSlope n = 3 - 2 * ratio n := by
  simp only [nullSlope, ratio]
  ring

/-- The fixed reference in the normalized certificate is the literal
hard-core chart path with slopes `(1, -nullSlope n, 1, 0)`. -/
theorem reference_coordinates (n : ℕ) (ε : ℝ) :
    coordinates n original ε =
      ![(ε : ℂ) * Complex.I, 1 + ((-nullSlope n * ε : ℝ) : ℂ) * Complex.I,
        (ε : ℂ) * Complex.I, 0] := by
  rw [coordinates_formula, nullSlope_eq]
  funext i
  simp only [original, Pi.add_apply, Pi.smul_apply]
  fin_cases i <;> simp [imagVector, realVector, witness, Complex.real_smul]
  ring

/-- The partner supplies parity-preserving Taylor data through cubic order.
The real quadratic and imaginary linear and cubic coefficients can be read
directly from the constant and quadratic coefficients of its even parameters. -/
def HasParityTaylor (z : ℝ → Coord) (linear quadratic cubic : Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 4,
    (fun ε => (z ε i).im - (linear i * ε + cubic i * ε^3))
      =o[𝓝 (0 : ℝ)] (fun ε => ε^3) ∧
    (fun ε => (z ε i).re - ((witness i).re + quadratic i * ε^2))
      =o[𝓝 (0 : ℝ)] (fun ε => ε^3)

/-- The remainder orders supplied by the even-parameter analytic inverse
imply the cubic Taylor hypothesis used by the separation proof. -/
theorem hasParityTaylor_of_fourth_order {z : ℝ → Coord}
    {linear quadratic cubic quarticReal : Fin 4 → ℝ}
    (h : ∀ i : Fin 4,
      (fun ε => (z ε i).im - (linear i * ε + cubic i * ε^3))
        =O[𝓝 (0 : ℝ)] (fun ε => ε^5) ∧
      (fun ε => (z ε i).re - ((witness i).re + quadratic i * ε^2 + quarticReal i * ε^4))
        =O[𝓝 (0 : ℝ)] (fun ε => ε^6)) :
    HasParityTaylor z linear quadratic cubic := by
  intro i
  obtain ⟨hi, hr⟩ := h i
  have hq := (isLittleO_pow_pow (𝕜 := ℝ) (by decide : 3 < 4)).const_mul_left (quarticReal i)
  refine ⟨hi.trans_isLittleO (isLittleO_pow_pow (by decide : 3 < 5)), ?_⟩
  exact ((hr.trans_isLittleO (isLittleO_pow_pow (by decide : 3 < 6))).add hq).congr_left
    (fun ε => by ring)

private theorem vector_taylor {z : ℝ → Coord} {linear quadratic cubic : Fin 4 → ℝ}
    (h : HasParityTaylor z linear quadratic cubic) :
    (fun ε => z ε - (witness + ε • imagVector linear +
      ε^2 • realVector quadratic + ε^3 • imagVector cubic)) =o[𝓝 (0 : ℝ)] (fun ε => ε^3) := by
  apply isLittleO_pi.mpr
  intro i
  let E := fun ε => (z ε - (witness + ε • imagVector linear +
    ε^2 • realVector quadratic + ε^3 • imagVector cubic)) i
  have hr (ε : ℝ) : (E ε).re = (z ε i).re - ((witness i).re + quadratic i * ε^2) := by
    simp [E, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
      imagVector, realVector, Complex.add_re, Complex.sub_re, Complex.mul_re,
      -Complex.ofReal_pow, mul_comm]
  have hi (ε : ℝ) : (E ε).im = (z ε i).im - (linear i * ε + cubic i * ε^3) := by
    have hw : (witness i).im = 0 := by fin_cases i <;> simp [witness]
    simp [E, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
      imagVector, realVector, Complex.add_im, Complex.sub_im, Complex.mul_im,
      -Complex.ofReal_pow, hw, mul_comm]
  obtain ⟨hI, hR⟩ := h i
  have hR' := hR.congr_left fun ε => (hr ε).symm
  have hI' := hI.congr_left fun ε => (hi ε).symm
  have hN : E =O[𝓝 (0 : ℝ)] (fun ε => ‖(E ε).re‖ + ‖(E ε).im‖) :=
    isBigO_of_le _ fun ε => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [Real.norm_eq_abs] using Complex.norm_le_abs_re_add_abs_im (E ε)
  exact hN.trans_isLittleO (hR'.norm_left.add hI'.norm_left)

private theorem parityTaylor_hasDerivAt {z : ℝ → Coord}
    {linear quadratic cubic : Fin 4 → ℝ} (h : HasParityTaylor z linear quadratic cubic) :
    z 0 = witness ∧ HasDerivAt z (imagVector linear) 0 := by
  have hT := vector_taylor h
  have hz : z 0 = witness := by
    obtain ⟨C, _, hC⟩ := hT.isBigO.exists_nonneg
    have h₀ := mem_of_mem_nhds hC.bound
    exact sub_eq_zero.mp (by simpa using h₀)
  have hs (k : ℕ) (hk : 1 < k) (u : Coord) :
      (fun ε : ℝ => ε^k • u) =o[𝓝 0] (fun ε => ε) := by
    have hO : (fun ε : ℝ => ε^k • u) =O[𝓝 0] (fun ε => ε^k) :=
      IsBigO.of_bound ‖u‖ (Eventually.of_forall fun ε => by rw [norm_smul, mul_comm])
    exact hO.trans_isLittleO (isLittleO_pow_id hk)
  refine ⟨hz, hasDerivAt_iff_isLittleO_nhds_zero.mpr ?_⟩
  simp only [zero_add, hz]
  refine (((hT.trans (isLittleO_pow_id (by decide : 1 < 3))).add
    (hs 2 (by decide) (realVector quadratic))).add (hs 3 (by decide) (imagVector cubic))).congr_left ?_
  intro ε
  abel

private theorem leading_slopes_of_matching (r : ℕ) (hr : 3 ≤ r) {z : ℝ → Coord}
    {linear quadratic cubic : Fin 4 → ℝ} (h : HasParityTaylor z linear quadratic cubic)
    (hmatch : (fun ε => regularReadout r (z ε)) =ᶠ[𝓝 (0 : ℝ)]
      fun ε => regularReadout r (coordinates (r+4) original ε)) :
    linear = ![linear 0, (3 - 2 * ratio (r+4)) * linear 0, 1, 0] := by
  obtain ⟨hz, hd⟩ := parityTaylor_hasDerivAt h
  let R := regularReadout r
  let v : Fin 4 → ℝ := ![1, (3 - 2 * ratio (r+4)) * 1, 1, 0]
  have hR : HasFDerivAt R (fderiv ℝ R witness) witness :=
    (analyticAt_straighten r hr).differentiableAt.fst.hasFDerivAt
  have hp := coordinates_hasDerivAt (r+4) original
  have hd' := hR.comp_hasDerivAt_of_eq 0 hd hz.symm
  have hp' := hR.comp_hasDerivAt_of_eq 0 hp (coordinates_zero _ _).symm
  have he : fderiv ℝ R witness (imagVector linear) = fderiv ℝ R witness (imagVector v) :=
    (hd'.congr_of_eventuallyEq hmatch.symm).unique hp'
  obtain ⟨t, ht⟩ := (regular_kernel_iff r hr (imagVector linear - imagVector v)).mp (by
    change fderiv ℝ R witness (imagVector linear - imagVector v) = 0
    rw [map_sub, he, sub_self])
  have hi (i : Fin 4) := congrArg (fun u : Coord => (u i).im) ht
  have ht₀ : t = linear 0 - 1 := by
    simpa [imagVector, v, nullDirection, Pi.sub_apply, Pi.smul_apply, Complex.real_smul,
      Complex.sub_im, Complex.mul_im] using (hi 0).symm
  funext i
  fin_cases i
  · rfl
  · have hrow := hi 1
    simp [ht₀, Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.sub_im,
      imagVector, v, nullDirection, Complex.mul_im] at hrow
    have hs : nullSlope (r+4) = -(3 - 2 * ratio (r+4)) := by
      linarith only [nullSlope_eq (r+4)]
    rw [hs] at hrow
    change linear 1 = (3 - 2 * ratio (r+4)) * linear 0
    linear_combination hrow
  · have hrow := hi 2
    simpa [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.sub_im,
      imagVector, v, nullDirection, Complex.mul_im, sub_eq_zero] using hrow
  · have hrow := hi 3
    simpa [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.sub_im,
      imagVector, v, nullDirection, Complex.mul_im] using hrow

/-- Convert the partner's componentwise Taylor data to the certified path and
its cubic null correction. Exact regular matching fixes the three other
imaginary slopes once the slope of `Im a` is supplied. -/
theorem exists_certified_path_of_parity_taylor (r : ℕ) (hr : 3 ≤ r)
    {z : ℝ → Coord} {linear quadratic cubic : Fin 4 → ℝ}
    (h : HasParityTaylor z linear quadratic cubic) (ht : linear 0 = oppositeSlope (r+4))
    (hmatch : (fun ε => regularReadout r (z ε)) =ᶠ[𝓝 (0 : ℝ)]
      fun ε => regularReadout r (coordinates (r+4) original ε)) :
    ∃ x : Path, x.t = oppositeSlope (r+4) ∧
      (fun ε => z ε - coordinates (r+4) x ε -
        ε^3 • (cubic 0 • nullDirection (r+4))) =o[𝓝 (0 : ℝ)] (fun ε => ε^3) := by
  let x : Path :=
    { t := linear 0
      a₂ := quadratic 0
      b₂ := quadratic 1
      c₂ := quadratic 2
      d₂ := quadratic 3
      b₃ := cubic 1 + nullSlope (r+4) * cubic 0
      c₃ := cubic 2
      d₃ := cubic 3 }
  have hlinear := leading_slopes_of_matching r hr h hmatch
  have hQ : realVector ![x.a₂, x.b₂, x.c₂, x.d₂] = realVector quadratic := by
    funext i
    fin_cases i <;> rfl
  have hC : imagVector ![0, x.b₃, x.c₃, x.d₃] + cubic 0 • nullDirection (r+4) =
      imagVector cubic := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    fin_cases i <;> simp [x, imagVector, nullDirection, Complex.real_smul]
    ring
  refine ⟨x, ht, (vector_taylor h).congr_left fun ε => ?_⟩
  have he : coordinates (r+4) x ε + ε^3 • (cubic 0 • nullDirection (r+4)) =
      witness + ε • imagVector linear + ε^2 • realVector quadratic + ε^3 • imagVector cubic := by
    rw [coordinates_formula, hQ]
    have h₀ : realVector ![x.a₄, x.b₄, x.c₄, x.d₄] = 0 := by
      funext i
      fin_cases i <;> rfl
    rw [h₀, smul_zero, add_zero, add_assoc _ (ε^3 • _) _, ← smul_add, hC]
    have hv : ![x.t, (3 - 2 * ratio (r+4)) * x.t, 1, 0] = linear := hlinear.symm
    rw [hv]
  rw [← sub_add_eq_sub_sub, he]

/-- Matched analytic Taylor data at the opposite slope imply generic actual
projector reconstruction, with competitors ranging over the whole actual
bond-two periodic MPS space. The chain length is `r + 4`. -/
theorem exists_generic_actual_reconstruction_of_matched_taylor (r : ℕ) (hr : 3 ≤ r)
    {z : ℝ → Coord} {linear quadratic cubic : Fin 4 → ℝ}
    (h : HasParityTaylor z linear quadratic cubic) (ht : linear 0 = oppositeSlope (r+4))
    (hpair : ∀ᶠ ε in 𝓝 (0 : ℝ),
      regularReadout r (z ε) = regularReadout r (coordinates (r+4) original ε) ∧
      component false r 3 (z ε) = component false r 3 (coordinates (r+4) original ε)) :
    ∃ N : Set (actualProjectors (r + 2)), IsOpen N ∧
      (⟨witnessProjector (r + 2), witnessProjector_mem_actualProjectors (by omega)⟩ :
        actualProjectors (r + 2)) ∈ N ∧
      ∃ G : Set N, IsOpen G ∧ Dense G ∧
        ∀ P ∈ G, ∀ Q : actualProjectors (r + 2),
          twoSiteObservation (r + 2) Q.val = twoSiteObservation (r + 2) P.val.val →
          Q.val = P.val.val := by
  obtain ⟨x, hxt, hjet⟩ := exists_certified_path_of_parity_taylor r hr h ht (hpair.mono fun _ he => he.1)
  exact exists_generic_actual_reconstruction r hr
    (hasSeparatedPairs_of_matched_taylor r hr x (cubic 0) hxt hjet hpair)

end

#print axioms forbidden_expansion_of_matched_taylor
#print axioms hasSeparatedPairs_of_matched_taylor
#print axioms reference_coordinates
#print axioms hasParityTaylor_of_fourth_order
#print axioms exists_certified_path_of_parity_taylor
#print axioms exists_generic_actual_reconstruction_of_matched_taylor

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticSeparation
