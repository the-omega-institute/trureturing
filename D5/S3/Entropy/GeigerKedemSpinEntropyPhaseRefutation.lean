/- GID: D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim; result=D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result; claim=D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim
   digest: The spin-1 entropy changes by 1/891 between two relative phases. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

open Complex MeasureTheory Set Metric
open scoped Topology ComplexConjugate

namespace D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation

noncomputable def density
    (thetaAlpha thetaBeta phaseX phaseZ phi : ℝ) : ℝ :=
  Complex.normSq
    (((Real.sin thetaAlpha * Real.cos thetaBeta : ℝ) : ℂ) *
        Complex.exp
          (((phaseX + 2 * phi : ℝ) : ℂ) * Complex.I) +
      (Real.cos thetaAlpha : ℂ) *
        Complex.exp ((phi : ℂ) * Complex.I) +
      ((Real.sin thetaAlpha * Real.sin thetaBeta : ℝ) : ℂ) *
        Complex.exp
          (((phaseZ - 2 * phi : ℝ) : ℂ) * Complex.I)) /
    (2 * Real.pi)

noncomputable def spinEntropy
    (thetaAlpha thetaBeta phaseX phaseZ : ℝ) : ℝ :=
  -(∫ phi in (0 : ℝ)..(2 * Real.pi),
      density thetaAlpha thetaBeta phaseX phaseZ phi *
        Real.log
          (density thetaAlpha thetaBeta phaseX phaseZ phi)) +
    Real.binEntropy (Real.cos thetaAlpha ^ 2) +
    Real.sin thetaAlpha ^ 2 *
      Real.binEntropy (Real.cos thetaBeta ^ 2)

def claim : Prop :=
  ∀ thetaAlpha thetaBeta phaseX phaseZ : ℝ,
    thetaAlpha ∈ Set.Icc 0 (Real.pi / 2) →
    thetaBeta ∈ Set.Icc 0 (Real.pi / 2) →
    phaseX ∈ Set.Ico 0 (2 * Real.pi) →
    phaseZ ∈ Set.Ico 0 (2 * Real.pi) →
    spinEntropy thetaAlpha thetaBeta phaseX phaseZ =
      spinEntropy thetaAlpha thetaBeta 0 0

private theorem density_continuous (a b x z : ℝ) : Continuous (density a b x z) := by
  unfold density
  fun_prop

private theorem density_mul_log_intervalIntegrable (a b x z : ℝ) :
    IntervalIntegrable (fun t => density a b x z t * Real.log (density a b x z t))
      volume 0 (2 * Real.pi) :=
  (Real.continuous_mul_log.comp (density_continuous a b x z)).intervalIntegrable _ _

private def poly (s : ℝ) (z : ℂ) : ℂ := 3 + z + (s : ℂ) * z ^ 4

private noncomputable def logPoly (s : ℝ) (z : ℂ) : ℂ :=
  poly s z * Complex.log (poly s z)

private theorem poly_differentiable (s : ℝ) : Differentiable ℂ (poly s) := by
  unfold poly
  fun_prop

private theorem poly_re_lower (s : ℝ) (hs : |s| ≤ 1) (z : ℂ)
    (hz : z ∈ closedBall 0 1) : 1 ≤ (poly s z).re := by
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hpow : ‖z ^ 4‖ ≤ 1 := by
    simpa [norm_pow] using pow_le_one₀ (n := 4) (norm_nonneg z) hz'
  have hmul : ‖(s : ℂ) * z ^ 4‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul hs hpow (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have h1 := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have h2 := (abs_le.mp (Complex.abs_re_le_norm ((s : ℂ) * z ^ 4))).1
  rw [poly.eq_1]
  simp only [add_re]
  norm_num at *
  linarith

private theorem poly_slit (s : ℝ) (hs : |s| ≤ 1) (z : ℂ)
    (hz : z ∈ closedBall 0 1) : poly s z ∈ Complex.slitPlane := by
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [poly_re_lower s hs z hz]))

private theorem logPoly_differentiableOn (s : ℝ) (hs : |s| ≤ 1) :
    DifferentiableOn ℂ (logPoly s) (closedBall 0 1) := by
  exact (poly_differentiable s).differentiableOn.mul
    ((poly_differentiable s).differentiableOn.clog (poly_slit s hs))

private theorem circleAverage_div_pow (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    Real.circleAverage (fun z => f z / z ^ n) 0 1 =
      iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have heq : (fun z : ℂ => (z - 0)⁻¹ • (f z / z ^ n)) =
      (fun z => (1 / (z - 0) ^ (n + 1)) • f z) := by
    funext z
    simp only [sub_zero, smul_eq_mul, pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [heq, DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (by norm_num : (0 : ℝ) < 1) n hf]
  simp only [smul_eq_mul]
  field_simp (disch := first | exact_mod_cast Real.pi_ne_zero | exact Complex.I_ne_zero |
    exact_mod_cast (Nat.factorial_ne_zero n) | norm_num)

private theorem div_pow_circleIntegrable (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    CircleIntegrable (fun z => f z / z ^ n) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  apply (hf.continuousOn.mono sphere_subset_closedBall).div
    (continuousOn_id.pow n)
  intro z hz
  apply pow_ne_zero
  have hnorm : ‖z‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hz
  exact norm_ne_zero_iff.mp (by simpa only [id_eq, hnorm] using (one_ne_zero : (1 : ℝ) ≠ 0))

private theorem weighted_circleAverage (s : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    Real.circleAverage (fun z => star (poly s z) * f z) 0 1 =
      3 * f 0 + deriv f 0 + (s : ℂ) * iteratedDeriv 4 f 0 / 24 := by
  have hconj (z : ℂ) (hz : z ∈ sphere 0 |(1 : ℝ)|) : star z = z⁻¹ := by
    have hnorm : ‖z‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right, abs_one] using hz
    apply eq_inv_of_mul_eq_one_left
    change conj z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have heq := Real.circleAverage_congr_sphere (c := (0 : ℂ)) (R := (1 : ℝ))
    (f₁ := fun z => star (poly s z) * f z)
    (f₂ := fun z => (3 : ℂ) • f z + f z / z + (s : ℂ) • (f z / z ^ 4))
    (by
      intro z hz
      simp only [poly, star_add, star_mul, star_pow, star_ofNat,
        show star (s : ℂ) = (s : ℂ) from Complex.conj_ofReal s,
        hconj z hz, smul_eq_mul, div_eq_mul_inv, inv_pow]
      ring)
  rw [heq]
  have h0 : CircleIntegrable f 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num) (hf.continuousOn.mono sphere_subset_closedBall)
  have h1 := div_pow_circleIntegrable f hf 1
  have h4 := div_pow_circleIntegrable f hf 4
  simp only [pow_one] at h1
  have h4s : CircleIntegrable (fun z => (s : ℂ) • (f z / z ^ 4)) 0 1 := by
    simpa only [CircleIntegrable, smul_eq_mul] using h4.const_mul (s : ℂ)
  rw [Real.circleAverage_fun_add (f₁ := fun z => (3 : ℂ) • f z + f z / z)
    (f₂ := fun z => (s : ℂ) • (f z / z ^ 4)) ((h0.smul (3 : ℂ)).add h1)
    h4s,
    Real.circleAverage_fun_add (f₁ := fun z => (3 : ℂ) • f z) (f₂ := fun z => f z / z)
      (h0.smul (3 : ℂ)) h1,
    Real.circleAverage_fun_smul, Real.circleAverage_fun_smul]
  have ha0 := circleAverage_div_pow f hf 0
  have ha1 := circleAverage_div_pow f hf 1
  have ha4 := circleAverage_div_pow f hf 4
  simp only [pow_zero, div_one, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one] at ha0
  simp only [pow_one, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one] at ha1
  norm_num only [Nat.factorial] at ha4
  rw [ha0, ha1, ha4]
  simp only [smul_eq_mul]
  ring

private theorem logPoly_derivatives (s : ℝ) (hs : |s| ≤ 1) :
    deriv (logPoly s) 0 = Complex.log 3 + 1 ∧
      iteratedDeriv 4 (logPoly s) 0 =
        24 * (s : ℂ) * (Complex.log 3 + 1) + 2 / 27 := by
  let p1 : ℂ → ℂ := fun z => 1 + 4 * (s : ℂ) * z ^ 3
  let p2 : ℂ → ℂ := fun z => 12 * (s : ℂ) * z ^ 2
  let p3 : ℂ → ℂ := fun z => 24 * (s : ℂ) * z
  have hp (z : ℂ) : HasDerivAt (poly s) (p1 z) z := by
    convert! ((hasDerivAt_id z).const_add 3).add
      (((hasDerivAt_id z).pow 4).const_mul (s : ℂ)) using 1; dsimp only [poly, p1, id_eq]; ring
  have hp1 (z : ℂ) : HasDerivAt p1 (p2 z) z := by
    convert! (((hasDerivAt_id z).pow 3).const_mul (4 * (s : ℂ))).const_add 1
      using 1; dsimp only [p1, p2, id_eq]; ring
  have hp2 (z : ℂ) : HasDerivAt p2 (p3 z) z := by
    convert! (((hasDerivAt_id z).pow 2).const_mul (12 * (s : ℂ)))
      using 1; dsimp only [p2, p3, id_eq]; ring
  have hp3 (z : ℂ) : HasDerivAt p3 (24 * (s : ℂ)) z := by
    simpa only [p3, id_eq, mul_one] using (hasDerivAt_id z).const_mul (24 * (s : ℂ))
  let d1 : ℂ → ℂ := fun z => p1 z * (Complex.log (poly s z) + 1)
  let d2 : ℂ → ℂ := fun z =>
    p2 z * (Complex.log (poly s z) + 1) + p1 z ^ 2 / poly s z
  let d3 : ℂ → ℂ := fun z =>
    p3 z * (Complex.log (poly s z) + 1) +
      3 * p1 z * p2 z / poly s z - p1 z ^ 3 / poly s z ^ 2
  have hn (z : ℂ) (hz : z ∈ ball 0 1) : poly s z ≠ 0 :=
    Complex.slitPlane_ne_zero (poly_slit s hs z (ball_subset_closedBall hz))
  have hl (z : ℂ) (hz : z ∈ ball 0 1) :=
    (hp z).clog (poly_slit s hs z (ball_subset_closedBall hz))
  have h1 (z : ℂ) (hz : z ∈ ball 0 1) : HasDerivAt (logPoly s) (d1 z) z := by
    convert! (hp z).mul (hl z hz) using 1
    try dsimp only [d1]
    field_simp (disch := first | exact hn z hz | exact pow_ne_zero _ (hn z hz) | norm_num)
  have h2 (z : ℂ) (hz : z ∈ ball 0 1) : HasDerivAt d1 (d2 z) z := by
    convert! (hp1 z).mul ((hl z hz).add_const 1) using 1
    try dsimp only [d2]
    field_simp (disch := first | exact hn z hz | exact pow_ne_zero _ (hn z hz) | norm_num)
  have h3 (z : ℂ) (hz : z ∈ ball 0 1) : HasDerivAt d2 (d3 z) z := by
    convert! ((hp2 z).mul ((hl z hz).add_const 1)).add
      (((hp1 z).pow 2).div (hp z) (hn z hz)) using 1
    try dsimp only [d3, Pi.pow_apply]
    field_simp (disch := first | exact hn z hz | exact pow_ne_zero _ (hn z hz) | norm_num); ring
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have e1 : Set.EqOn (deriv (logPoly s)) d1 (ball 0 1) := fun z hz => (h1 z hz).deriv
  have e2 : Set.EqOn (iteratedDeriv 2 (logPoly s)) d2 (ball 0 1) := by
    intro z hz
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    simpa only [iteratedDeriv_one] using
      ((e1.iteratedDeriv_of_isOpen isOpen_ball 1) hz).trans (by
        simpa only [iteratedDeriv_one] using (h2 z hz).deriv)
  have e3 : Set.EqOn (iteratedDeriv 3 (logPoly s)) d3 (ball 0 1) := by
    intro z hz
    rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ]
    simpa only [iteratedDeriv_one] using
      ((e2.iteratedDeriv_of_isOpen isOpen_ball 1) hz).trans (by
        simpa only [iteratedDeriv_one] using (h3 z hz).deriv)
  constructor
  · simpa [d1, p1, poly] using (h1 0 hzero).deriv
  · rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ]
    have e4 := (e3.iteratedDeriv_of_isOpen isOpen_ball 1) hzero
    simp only [iteratedDeriv_one] at e4
    rw [e4]
    have hd3 := (((hp3 0).mul ((hl 0 hzero).add_const 1)).add
      ((((hp1 0).const_mul 3).mul (hp2 0)).div (hp 0) (hn 0 hzero))).sub
      (((hp1 0).pow 3).div ((hp 0).pow 2) (pow_ne_zero 2 (hn 0 hzero)))
    change HasDerivAt d3 _ 0 at hd3
    rw [hd3.deriv]
    norm_num [p1, p2, p3, poly]

private theorem poly_mass (s : ℝ) :
    Real.circleAverage (fun z => Complex.normSq (poly s z)) 0 1 = 10 + s ^ 2 := by
  have hd1 : deriv (poly s) 0 = 1 := by
    have hp := ((hasDerivAt_id (0 : ℂ)).const_add 3).add
      (((hasDerivAt_id (0 : ℂ)).pow 4).const_mul (s : ℂ))
    change HasDerivAt (poly s) _ 0 at hp
    simpa using hp.deriv
  have hd4 : iteratedDeriv 4 (poly s) 0 = 24 * (s : ℂ) := by
    have he : poly s = fun z : ℂ => 3 + (z + (s : ℂ) * z ^ 4) := by
      funext z
      simp only [poly]
      ring
    rw [he, iteratedDeriv_const_add (by norm_num),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    norm_num [iteratedDeriv_fun_id]
    ring
  have hc : Continuous (fun z => star (poly s z) * poly s z) := by
    unfold poly
    fun_prop
  have hav := Complex.reCLM.circleAverage_comp_comm (c := (0 : ℂ))
    (ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn)
  rw [weighted_circleAverage s (poly s) (poly_differentiable s).differentiableOn,
    hd1, hd4] at hav
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at hav
  convert! hav using 1
  norm_num [poly, Complex.mul_re, Complex.mul_im]
  ring

private theorem normSq_mul_log (w : ℂ) :
    Complex.normSq w * Real.log (Complex.normSq w) =
      2 * (star w * (w * Complex.log w)).re := by
  rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.log_re, Complex.normSq_eq_norm_sq, Real.log_pow]
  ring

private theorem poly_log_moment (s : ℝ) (hs : |s| ≤ 1) :
    Real.circleAverage
      (fun z => Complex.normSq (poly s z) * Real.log (Complex.normSq (poly s z))) 0 1 =
      (20 + 2 * s ^ 2) * Real.log 3 + 2 * (1 + s ^ 2) + s / 162 := by
  have hf := logPoly_differentiableOn s hs
  have hc : ContinuousOn (fun z => star (poly s z) * logPoly s z) (sphere 0 1) := by
    exact ((poly_differentiable s).continuous.continuousOn.star).mul
      (hf.continuousOn.mono sphere_subset_closedBall)
  have hav := Complex.reCLM.circleAverage_comp_comm (c := (0 : ℂ))
    (ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1) hc)
  rw [weighted_circleAverage s (logPoly s) hf,
    (logPoly_derivatives s hs).1, (logPoly_derivatives s hs).2] at hav
  simp only [Function.comp_def, Complex.reCLM_apply] at hav
  have he : (fun z => Complex.normSq (poly s z) * Real.log (Complex.normSq (poly s z))) =
      fun z => (2 : ℝ) • (star (poly s z) * logPoly s z).re := by
    funext z
    rw [logPoly.eq_1]
    exact normSq_mul_log (poly s z)
  rw [he, Real.circleAverage_fun_smul, hav]
  norm_num [logPoly, poly, Complex.mul_re, Complex.mul_im, Complex.log_re,
    smul_eq_mul]
  ring

private noncomputable def witnessAlpha : ℝ := Real.arctan (Real.sqrt 10)

private noncomputable def witnessBeta : ℝ := Real.arctan (1 / 3)

private theorem witnessAlpha_mem : witnessAlpha ∈ Icc 0 (Real.pi / 2) :=
  ⟨Real.arctan_nonneg.mpr (Real.sqrt_nonneg 10), (Real.arctan_lt_pi_div_two _).le⟩

private theorem witnessBeta_mem : witnessBeta ∈ Icc 0 (Real.pi / 2) :=
  ⟨Real.arctan_nonneg.mpr (by norm_num), (Real.arctan_lt_pi_div_two _).le⟩

private theorem witness_coefficients :
    Real.sin witnessAlpha * Real.cos witnessBeta = 3 / Real.sqrt 11 ∧
    Real.cos witnessAlpha = 1 / Real.sqrt 11 ∧
    Real.sin witnessAlpha * Real.sin witnessBeta = 1 / Real.sqrt 11 := by
  have h10 : Real.sqrt 10 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h11 : Real.sqrt 11 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : Real.sin witnessAlpha = Real.sqrt 10 / Real.sqrt 11 := by
    rw [witnessAlpha.eq_1, Real.sin_arctan]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hac : Real.cos witnessAlpha = 1 / Real.sqrt 11 := by
    simp only [witnessAlpha, Real.cos_arctan]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hbc : Real.cos witnessBeta = 3 / Real.sqrt 10 := by
    rw [witnessBeta.eq_1]
    norm_num [Real.cos_arctan, Real.sqrt_div]
  have hbs : Real.sin witnessBeta = 1 / Real.sqrt 10 := by
    norm_num [witnessBeta, Real.sin_arctan, Real.sqrt_div]
    field_simp (disch := positivity)
  rw [ha, hac, hbc, hbs]
  constructor
  · field_simp (disch := positivity)
  constructor
  · rfl
  · field_simp (disch := positivity)

private noncomputable def auxiliaryDensity (s t : ℝ) : ℝ :=
  Complex.normSq (poly s (circleMap 0 1 t)) / (22 * Real.pi)

private theorem density_phase (phase s : ℝ)
    (hphase : Complex.exp ((phase : ℂ) * Complex.I) = (s : ℂ)) (t : ℝ) :
    density witnessAlpha witnessBeta 0 phase t = auxiliaryDensity s t := by
  let u := circleMap 0 1 t
  have hu_norm : ‖u‖ = 1 := by simp [u]
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu_norm]; norm_num)
  have he1 : Complex.exp ((t : ℂ) * Complex.I) = u := by simp [u, circleMap]
  have he2 : Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) = u ^ 2 := by
    rw [← he1, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hez : Complex.exp (((phase - 2 * t : ℝ) : ℂ) * Complex.I) = (s : ℂ) / u ^ 2 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hphase, he2]
  have hstar : star u = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hu_norm]
    norm_num
  have hroot : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 11)).ne'
  have hfactor :
      (3 / (Real.sqrt 11 : ℂ)) * u ^ 2 + (1 / (Real.sqrt 11 : ℂ)) * u +
        (1 / (Real.sqrt 11 : ℂ)) * ((s : ℂ) / u ^ 2) =
      (1 / (Real.sqrt 11 : ℂ)) * u ^ 2 * star (poly s u) := by
    simp only [poly, star_add, star_mul, star_pow, star_ofNat,
      show star (s : ℂ) = (s : ℂ) from Complex.conj_ofReal s, hstar]
    field_simp (disch := first | exact hu | exact hroot | norm_num)
  have hu_sq : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu_norm]
    norm_num
  have hr : Complex.normSq (1 / (Real.sqrt 11 : ℂ)) = 1 / 11 := by
    rw [map_div₀, map_one, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]
  unfold density auxiliaryDensity
  rw [witness_coefficients.1, witness_coefficients.2.1, witness_coefficients.2.2]
  push_cast at he2 hez ⊢
  rw [zero_add, he2, he1, hez, hfactor]
  simp only [map_mul, map_pow, hr, hu_sq, one_pow, mul_one,
    Complex.star_def, Complex.normSq_conj]
  dsimp only [u]
  ring

private theorem density_zero_phase (t : ℝ) :
    density witnessAlpha witnessBeta 0 0 t = auxiliaryDensity 1 t := by
  apply density_phase
  norm_num

private theorem density_pi_phase (t : ℝ) :
    density witnessAlpha witnessBeta 0 Real.pi t = auxiliaryDensity (-1) t := by
  apply density_phase
  simp [Complex.exp_pi_mul_I]

private theorem auxiliary_log_integral (s : ℝ) (hs : |s| ≤ 1) (hsq : s ^ 2 = 1)
    (hr : IntervalIntegrable
      (fun t => auxiliaryDensity s t * Real.log (auxiliaryDensity s t))
      volume 0 (2 * Real.pi)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      auxiliaryDensity s t * Real.log (auxiliaryDensity s t)) =
      2 * Real.log 3 + 4 / 11 + s / 1782 - Real.log (22 * Real.pi) := by
  have hm := poly_mass s
  have hj := poly_log_moment s hs
  simp only [Real.circleAverage_def, smul_eq_mul, hsq] at hm hj
  have hmass : (∫ t in (0 : ℝ)..(2 * Real.pi), auxiliaryDensity s t) = 1 := by
    simp only [auxiliaryDensity, intervalIntegral.integral_div]
    field_simp (disch := positivity) at hm ⊢
    nlinarith
  have hmoment :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.normSq (poly s (circleMap 0 1 t)) *
          Real.log (Complex.normSq (poly s (circleMap 0 1 t)))) / (22 * Real.pi) =
        2 * Real.log 3 + 4 / 11 + s / 1782 := by
    field_simp (disch := positivity) at hj ⊢
    nlinarith
  have hi : IntervalIntegrable (auxiliaryDensity s) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold auxiliaryDensity
    exact ((Complex.continuous_normSq.comp (poly_differentiable s).continuous).comp
      (continuous_circleMap 0 1)).div_const _
  have hpoint (t : ℝ) :
      auxiliaryDensity s t * Real.log (auxiliaryDensity s t) +
        Real.log (22 * Real.pi) * auxiliaryDensity s t =
      (Complex.normSq (poly s (circleMap 0 1 t)) *
        Real.log (Complex.normSq (poly s (circleMap 0 1 t)))) / (22 * Real.pi) := by
    rw [auxiliaryDensity.eq_1]
    by_cases hw : Complex.normSq (poly s (circleMap 0 1 t)) = 0
    · simp [hw]
    rw [Real.log_div hw (by positivity)]
    ring
  have he := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun t _ => hpoint t)
  rw [intervalIntegral.integral_add hr (hi.const_mul _),
    intervalIntegral.integral_const_mul, hmass, mul_one,
    intervalIntegral.integral_div, hmoment] at he
  linarith

private theorem entropy_gap :
    spinEntropy witnessAlpha witnessBeta 0 Real.pi -
      spinEntropy witnessAlpha witnessBeta 0 0 = (1 : ℝ) / 891 := by
  have hp : IntervalIntegrable
      (fun t => auxiliaryDensity 1 t * Real.log (auxiliaryDensity 1 t))
      volume 0 (2 * Real.pi) := by
    simpa only [density_zero_phase] using
      density_mul_log_intervalIntegrable witnessAlpha witnessBeta 0 0
  have hm : IntervalIntegrable
      (fun t => auxiliaryDensity (-1) t * Real.log (auxiliaryDensity (-1) t))
      volume 0 (2 * Real.pi) := by
    simpa only [density_pi_phase] using
      density_mul_log_intervalIntegrable witnessAlpha witnessBeta 0 Real.pi
  have hip := auxiliary_log_integral 1 (by norm_num) (by norm_num) hp
  have him := auxiliary_log_integral (-1) (by norm_num) (by norm_num) hm
  rw [spinEntropy.eq_1, spinEntropy.eq_1]
  simp only [density_zero_phase, density_pi_phase]
  rw [hip, him]
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem result : ¬ claim := by
  intro h
  have he := h witnessAlpha witnessBeta 0 Real.pi witnessAlpha_mem witnessBeta_mem
    ⟨le_rfl, by positivity⟩ ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have hg := entropy_gap
  rw [he, sub_self] at hg
  norm_num at hg

end D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation
