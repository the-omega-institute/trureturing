/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two leading even-cutoff terms and the quantitative mean of the signed prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusOddCutoff
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootPrimitiveFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real MeasureTheory Set Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (normalizedMass normalizedZeroSeries normalizedZeroSeries_continuous mass_log_substitution
    windowError_continuous frequency frequency_real frequency_norm)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (windowDiscrepancy spectralPrimitive)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private theorem mass_moves_continuously {A B L : ℝ} (hA : Real.log 2 ≤ A)
    (hAB : A ≤ B) (hL : 0 ≤ L) :
    ContinuousOn (fun u => ∫ t in u..u+L, normalizedMass t) (Icc A B) := by
  have hm : ContinuousOn normalizedMass (Ici (Real.log 2)) := by
    have heq : normalizedMass =
        fun t => RHPrimeWindowMean.windowError t + (2 + (normalizedZeroSeries t).re) := by
      funext t
      change _ = (_ - _) + _
      exact (sub_add_cancel _ _).symm
    rw [heq]
    exact windowError_continuous.add
      ((Complex.continuous_re.comp normalizedZeroSeries_continuous).const_add 2).continuousOn
  have hcont : ContinuousOn normalizedMass (Icc A (B+L)) := hm.mono fun x hx => hA.trans hx.1
  have hAB' : A ≤ B+L := by linarith
  have hi : IntegrableOn normalizedMass (uIcc A (B+L)) := by
    rw [uIcc_of_le hAB']
    exact hcont.integrableOn_compact isCompact_Icc
  have hprim : ContinuousOn (fun x => ∫ t in A..x, normalizedMass t) (Icc A (B+L)) := by
    simpa only [uIcc_of_le hAB'] using intervalIntegral.continuousOn_primitive_interval hi
  have hleft : MapsTo id (Icc A B) (Icc A (B+L)) :=
    fun u hu => ⟨hu.1, hu.2.trans (by linarith)⟩
  have hright : MapsTo (fun u : ℝ => u+L) (Icc A B) (Icc A (B+L)) :=
    fun u hu => ⟨by linarith [hu.1], by dsimp; linarith [hu.2]⟩
  refine ((hprim.comp (by fun_prop) hright).sub (hprim.comp continuousOn_id hleft)).congr ?_
  intro u hu
  have ho (a b : ℝ) (ha : a ∈ uIcc A (B+L)) (hb : b ∈ uIcc A (B+L)) :
      IntervalIntegrable normalizedMass volume a b :=
    (hi.mono_set (Set.uIcc_subset_uIcc ha hb)).intervalIntegrable
  have hu₁ := hleft hu
  have hu₂ := hright hu
  rw [← uIcc_of_le hAB'] at hu₁ hu₂
  exact (intervalIntegral.integral_interval_sub_left
    (ho A (u+L) left_mem_uIcc hu₂) (ho A u left_mem_uIcc hu₁)).symm

private theorem root_primitive_exp_measurable {r : ℝ} (hr : 1 < r) :
    Measurable (fun u : ℝ => rootPrimitive r (Real.exp u)) := by
  unfold rootPrimitive
  refine Complex.continuous_re.measurable.comp (Measurable.tsum ?_)
  intro k
  simp_rw [← rootPrimitiveMode_eq hr]
  unfold rootMode
  fun_prop

private theorem spectral_primitive_measurable :
    Measurable (fun u : ℝ => spectralPrimitive (phaseOrbit u)) := by
  unfold spectralPrimitive
  refine Complex.continuous_re.measurable.comp (Measurable.tsum ?_)
  intro k
  simp only [phaseOrbit, Circle.coe_exp]
  fun_prop

theorem window_normalized_aestronglyMeasurable {A B L s : ℝ}
    (hA : Real.log 2 ≤ A) (hAB : A ≤ B) (hL : 0 ≤ L) (m : ℕ) :
    AEStronglyMeasurable (fun u : ℝ => signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
        powerGap s (Real.exp u) (Real.exp (u+L))) (volume.restrict (Ioc A B)) := by
  let ac := fun n (u : ℝ) => arithmeticPrimitive n (Real.exp u) (Real.exp (u+L))
  let rc := fun n (u : ℝ) => -(μ n : ℝ) *
    (rootPrimitive (n : ℝ) (Real.exp (u+L)) - rootPrimitive (n : ℝ) (Real.exp u))
  let roots := (Finset.Icc 2 m).filter (fun n => 2*n < m+1)
  have hac (n : ℕ) : Measurable (ac n) := by
    unfold ac arithmeticPrimitive powerGap
    simp only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    fun_prop
  have hrc (n : ℕ) (hn : n ∈ roots) : Measurable (rc n) := by
    have h₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hr := root_primitive_exp_measurable hn'
    exact ((hr.comp (by fun_prop : Measurable fun u : ℝ => u+L)).sub hr).const_mul _
  have hlimit : Measurable (fun u => 2 * Real.log (Real.exp (u+L) / Real.exp u)) := by fun_prop
  have hspec : Measurable (fun u => spectralPrimitive (phaseOrbit (Real.log (Real.exp u)))) := by
    simpa only [Real.log_exp] using spectral_primitive_measurable
  have hspec' : Measurable (fun u => spectralPrimitive (phaseOrbit (Real.log (Real.exp (u+L))))) :=
    hspec.comp (by fun_prop : Measurable fun u : ℝ => u+L)
  have harith : Measurable (fun u => ∑ n ∈ Finset.Icc 3 m, ac n u) :=
    Finset.measurable_sum _ (fun n _ => hac n)
  have hroot : Measurable (fun u => ∑ n ∈ roots, rc n u) :=
    Finset.measurable_sum _ hrc
  have hD : Measurable (fun u => powerGap s (Real.exp u) (Real.exp (u+L))) := by
    unfold powerGap
    simp only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    fun_prop
  have hm : AEStronglyMeasurable (fun u => ∫ t in u..u+L, normalizedMass t)
      (volume.restrict (Ioc A B)) :=
    ((mass_moves_continuously hA hAB hL).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hd := hm.sub hlimit.aestronglyMeasurable
  have hs := (hd.sub hspec'.aestronglyMeasurable).add hspec.aestronglyMeasurable
  have hf := ((hs.sub harith.aestronglyMeasurable).sub hroot.aestronglyMeasurable).div₀
    hD.aestronglyMeasurable
  refine hf.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu' : 2 ≤ Real.exp u := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_le_exp.mpr (hA.trans hu.1.le)
  have huL : Real.exp u ≤ Real.exp (u+L) := Real.exp_le_exp.mpr (by linarith)
  rw [signedWindowResidual, windowDiscrepancy, mass_log_substitution hu' huL]
  simp only [Real.log_exp]
  rfl

theorem bounded_exponential_integral {c : ℂ} (hc : c.re = 0)
    {gap : ℝ} (hgap : 0 < gap) (hgapc : gap ≤ ‖c‖) (a b : ℝ) :
    ‖∫ u in a..b, Complex.exp (c * (u : ℂ))‖ ≤ 2 / gap := by
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (hgap.trans_le hgapc)
  have hexp (u : ℝ) : ‖Complex.exp (c * (u : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, hc]
  rw [integral_exp_mul_complex hc_ne, norm_div]
  have hnum : ‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖ ≤ 2 := by
    simpa only [hexp, one_add_one_eq_two] using
      norm_sub_le (Complex.exp (c * (b : ℂ))) (Complex.exp (c * (a : ℂ)))
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _) |>.trans
    (div_le_div_of_nonneg_left (by norm_num) hgap hgapc)

theorem bounded_exponential_series_integral
    (coeff mode : ℕ → ℂ) (hcoeff : Summable (fun k => ‖coeff k‖))
    (hmode : ∀ k, (mode k).re = 0) {gap : ℝ} (hgap : 0 < gap)
    (hmode_gap : ∀ k, gap ≤ ‖mode k‖) (a b : ℝ) :
    let signal := fun u : ℝ => ∑' k, coeff k * Complex.exp (mode k * (u : ℂ))
    IntervalIntegrable signal volume a b ∧
      ‖∫ u in a..b, signal u‖ ≤ (∑' k, ‖coeff k‖) * (2 / gap) := by
  let term (k : ℕ) (u : ℝ) := coeff k * Complex.exp (mode k * (u : ℂ))
  have hterm (k : ℕ) : Continuous (term k) := by unfold term; fun_prop
  have hnorm (k : ℕ) (u : ℝ) : ‖term k u‖ = ‖coeff k‖ := by
    simp [term, Complex.norm_exp, Complex.mul_re, hmode k]
  have hsignal : Continuous (fun u : ℝ => ∑' k, term k u) :=
    continuous_tsum hterm hcoeff fun k u => (hnorm k u).le
  have hsum (u : ℝ) : Summable (fun k => term k u) :=
    hcoeff.of_norm_bounded fun k => (hnorm k u).le
  have hi : HasSum (fun k : ℕ => ∫ u in a..b, term k u)
      (∫ u in a..b, ∑' k, term k u) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k (_ : ℝ) => ‖coeff k‖)
    · exact fun k => (hterm k).aestronglyMeasurable
    · exact fun k => ae_of_all _ fun u _ => (hnorm k u).le
    · exact ae_of_all _ fun _ _ => hcoeff
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun u _ => (hsum u).hasSum
  refine ⟨hsignal.intervalIntegrable _ _, ?_⟩
  change ‖∫ u in a..b, ∑' k, term k u‖ ≤ _
  rw [← hi.tsum_eq]
  apply tsum_of_norm_bounded (hcoeff.hasSum.mul_right (2 / gap))
  intro k
  unfold term
  rw [intervalIntegral.integral_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (bounded_exponential_integral (hmode k) hgap (hmode_gap k) a b) (norm_nonneg _)

private theorem normalized_root_primitive_bound (hRH : RiemannHypothesis)
    {r : ℝ} (hr : 1 < r) (a b : ℝ) :
    let s := 1 / 2 - (2 * r)⁻¹
    let f := fun u : ℝ => Real.exp (s * u) * rootPrimitive r (Real.exp u)
    let mass := ∑' k, ‖rootCoeff r k / rootExponent r k‖
    IntervalIntegrable f volume a b ∧
      |∫ u in a..b, f u| ≤ mass * (2 / (10 / r)) ∧ ∀ u : ℝ, |f u| ≤ mass := by
  let s := 1 / 2 - (2 * r)⁻¹
  let coeff (k : ℕ) := rootCoeff r k / rootExponent r k
  let mode (k : ℕ) := frequency k / (r : ℂ)
  let z (u : ℝ) := ∑' k, coeff k * Complex.exp (mode k * (u : ℂ))
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hcoeff : Summable (fun k => ‖coeff k‖) := by
    apply ((actualCoeff_hasSum.summable.norm.mul_left r).mul_right r).of_nonneg_of_le
    · exact fun k => norm_nonneg _
    · exact root_primitive_coefficient_norm_le hr
  have hmode (k : ℕ) : (mode k).re = 0 := by
    simp [mode, Complex.div_re, frequency_real hRH k]
  have hgap (k : ℕ) : 10/r ≤ ‖mode k‖ := by
    rw [show mode k = frequency k / (r : ℂ) from rfl, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0]
    exact div_le_div_of_nonneg_right (frequency_norm k).le hr0.le
  obtain ⟨hi, hbound⟩ := bounded_exponential_series_integral coeff mode hcoeff hmode
    (by positivity : 0 < 10/r) hgap a b
  have heq (u : ℝ) : Real.exp (s * u) * rootPrimitive r (Real.exp u) = (z u).re :=
    normalized_root_primitive_series hr u
  have hre : (∫ u in a..b, (z u).re) = (∫ u in a..b, z u).re :=
    Complex.reCLM.intervalIntegral_comp_comm hi
  have hfun : (fun u : ℝ => Real.exp (s * u) * rootPrimitive r (Real.exp u)) =
      fun u : ℝ => (z u).re := funext heq
  change IntervalIntegrable (fun u : ℝ => Real.exp (s * u) * rootPrimitive r (Real.exp u))
    volume a b ∧ |∫ u in a..b, Real.exp (s * u) * rootPrimitive r (Real.exp u)| ≤ _ ∧ _
  rw [hfun]
  have hz : Continuous z := by
    unfold z
    apply continuous_tsum (fun k => ?_) hcoeff
    · intro k u
      simp [Complex.norm_exp, Complex.mul_re, hmode k]
    · fun_prop
  refine ⟨(Complex.continuous_re.comp hz).intervalIntegrable _ _, ?_, fun u => ?_⟩
  · rw [hre]
    exact (Complex.abs_re_le_norm _).trans hbound
  · refine (Complex.abs_re_le_norm _).trans ?_
    apply tsum_of_norm_bounded hcoeff.hasSum
    intro k
    simp [Complex.norm_exp, Complex.mul_re, hmode k]

theorem exp_power_gap (s u L : ℝ) :
    powerGap s (Real.exp u) (Real.exp (u+L)) =
      Real.exp (-s*u) * (1-Real.exp (-s*L)) := by
  simp only [powerGap, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [show (u+L)*(-s) = (-s)*u + (-s)*L by ring, Real.exp_add,
    show u*(-s) = (-s)*u by ring]
  ring

private theorem normalized_root_increment_bound (hRH : RiemannHypothesis)
    {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ a b : ℝ,
      let s := 1/2 - (2*r)⁻¹
      let inc := fun u : ℝ =>
        (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L))
      IntervalIntegrable inc volume a b ∧ |∫ u in a..b, inc u| ≤ C := by
  let s : ℝ := 1/2-(2*r)⁻¹
  let f := fun u : ℝ => Real.exp (s*u)*rootPrimitive r (Real.exp u)
  let mass := ∑' k, ‖rootCoeff r k / rootExponent r k‖
  let M := mass * (2/(10/r))
  have hs : 0 < s := by
    dsimp [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (show 2 < 2*r by linarith))
  have hmass : 0 ≤ mass := tsum_nonneg fun _ => norm_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨M+2*mass/s, by positivity, fun L hL a b => ?_⟩
  let t := Real.exp (-s*L)
  have ht : 0 < t := Real.exp_pos _
  have hd : 0 < 1-t := sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))
  have heq (u : ℝ) :
      (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L)) =
        (t*f (u+L)-f u)/(1-t) := by
    have hExp : t * Real.exp (s*(u+L)) = Real.exp (s*u) := by
      dsimp only [t]
      rw [← Real.exp_add]
      congr 1
      ring
    have hInv : Real.exp (-s*u) = (Real.exp (s*u))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [exp_power_gap, hInv]
    change _ = (t * (Real.exp (s*(u+L))*_) - Real.exp (s*u)*_) / _
    rw [← mul_assoc, hExp, ← mul_sub]
    change _ / ((Real.exp (s*u))⁻¹ * (1-t)) = _ / (1-t)
    field_simp [(Real.exp_pos (s*u)).ne', hd.ne']
  have hfun : (fun u : ℝ =>
        (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L))) =
      fun u : ℝ => (t*f (u+L)-f u)/(1-t) := funext heq
  change IntervalIntegrable (fun u : ℝ =>
        (rootPrimitive r (Real.exp (u+L)) - rootPrimitive r (Real.exp u)) /
          powerGap s (Real.exp u) (Real.exp (u+L))) volume a b ∧ _
  rw [hfun]
  obtain ⟨hi, hb, hpoint⟩ := normalized_root_primitive_bound hRH hr a b
  have integrable (x y : ℝ) : IntervalIntegrable f volume x y :=
    (normalized_root_primitive_bound hRH hr x y).1
  have hshift : IntervalIntegrable (fun u => f (u+L)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff (c := L) (by finiteness)).mpr
      (integrable (a+L) (b+L))
  refine ⟨((hshift.const_mul t).sub hi).div_const _, ?_⟩
  let I := ∫ u in a..b, f u
  let J := ∫ u in a+L..b+L, f u
  have hEdge (x : ℝ) : |∫ u in x..x+L, f u| ≤ mass*L := by
    rw [← Real.norm_eq_abs]
    simpa only [show ∀ x : ℝ, x+L-x = L by intro x; ring, abs_of_pos hL] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := x) (b := x+L)
        (fun u _ => by simpa only [Real.norm_eq_abs] using hpoint u))
  have hSides : J-I = (∫ u in b..b+L, f u) - (∫ u in a..a+L, f u) := by
    dsimp only [I, J]
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (integrable a b) (integrable b (b+L))
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (integrable a (a+L))
      (integrable (a+L) (b+L))
    linarith only [h₁, h₂]
  have hDifference : |J-I| ≤ 2*mass*L := by
    rw [hSides]
    exact (abs_sub _ _).trans (by linarith only [hEdge a, hEdge b])
  have hWidth : t*L/(1-t) ≤ 1/s := by
    have he : t*Real.exp (s*L) = 1 := by
      dsimp only [t]
      rw [← Real.exp_add, show -s*L+s*L = 0 by ring, Real.exp_zero]
    have htaylor := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*L)) ht.le
    rw [he] at htaylor
    rw [div_le_div_iff₀ hd hs]
    linarith only [show t*L*s+t = t*(s*L+1) by ring, htaylor]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hshift.const_mul t) hi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  change |(t*J-I)/(1-t)| ≤ _
  rw [show (t*J-I)/(1-t) = -I+t/(1-t)*(J-I) by field_simp [hd.ne']; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_of_nonneg (div_nonneg ht.le hd.le)]
  refine add_le_add hb ?_
  calc
    _ ≤ (t/(1-t))*(2*mass*L) :=
      mul_le_mul_of_nonneg_left hDifference (div_nonneg ht.le hd.le)
    _ = (2*mass)*(t*L/(1-t)) := by ring
    _ ≤ (2*mass)*(1/s) := mul_le_mul_of_nonneg_left hWidth (by positivity)
    _ = 2*mass/s := by ring

private theorem residual_succ_of_even {m r : ℕ} (hm : 2 ≤ m) (heven : m+1 = 2*r)
    (a B : ℝ) :
    signedWindowResidual (m+1) a B = signedWindowResidual m a B -
      arithmeticPrimitive (m+1) a B + (μ r : ℝ) *
        (rootPrimitive (r : ℝ) B - rootPrimitive (r : ℝ) a) := by
  have hroot :
      (Finset.Icc 2 (m+1)).filter (fun n => 2*n < (m+1)+1) =
        insert r ((Finset.Icc 2 m).filter (fun n => 2*n < m+1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : r ∉ (Finset.Icc 2 m).filter (fun n => 2*n < m+1) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have harith : Finset.Icc 3 (m+1) = insert (m+1) (Finset.Icc 3 m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [signedWindowResidual, signedWindowResidual, hroot, harith,
    Finset.sum_insert (by simp), Finset.sum_insert hnot]
  ring

theorem signed_window_even_cutoff_expansion (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
        let q := m+1
        let s := orderRate m
        let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
        let W := K*((q : ℝ)*(1+Real.log (q : ℝ))^2)
        |signedWindowResidual m a B + (μ q : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))*powerGap s a B +
          (μ r : ℝ)*(rootPrimitive (r : ℝ) B-rootPrimitive (r : ℝ) a)| ≤
          W * powerGap (s+δ) a B ∧
        W * powerGap (s+δ) a B ≤ W*((s+δ)/s)*a^(-δ)*powerGap s a B := by
  obtain ⟨a₀, K, ha₀, hK, hb⟩ := prime_window_mobius_of_rh hRH
  refine ⟨a₀, K, ha₀, hK, fun m r hm heven a B ha hAB => ?_⟩
  dsimp only
  let q := m+1
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hs : 0 < s := by
    dsimp only [s, orderRate]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hδ : 0 ≤ δ := by
    exact sub_nonneg.mpr (inv_anti₀ (by positivity : (0 : ℝ) < (m : ℝ)+1)
      (by linarith : (m : ℝ)+1 ≤ (m : ℝ)+2))
  have hr : orderRate q = s+δ := by
    dsimp only [orderRate, s, δ]
    rw [hq', show (m : ℝ)+1+1 = (m : ℝ)+2 by ring]
    ring
  have harith : arithmeticPrimitive q a B =
      -(μ q : ℝ) * ((q : ℝ)/((m : ℝ)*s)) * powerGap s a B := by
    have hrate : arithmeticRate q = s := by simp only [arithmeticRate, hq', s, orderRate]
    have hcoe : 2*(q : ℝ)^2/(((q : ℝ)-1)*((q : ℝ)-2)) = (q : ℝ)/((m : ℝ)*s) := by
      rw [hq']
      dsimp only [s, orderRate]
      have h₁ : (m : ℝ) ≠ 0 := by linarith
      have h₂ : (m : ℝ)+1 ≠ 0 := by linarith
      have h₃ : (m : ℝ)+1-1 ≠ 0 := by linarith
      have h₄ : (m : ℝ)+1-2 ≠ 0 := by linarith
      field_simp
      ring
    rw [arithmeticPrimitive, hrate, hcoe]
  have he : signedWindowResidual m a B +
      (μ q : ℝ) * (((m : ℝ)+1)/((m : ℝ)*s)) * powerGap s a B +
      (μ r : ℝ)*(rootPrimitive (r : ℝ) B-rootPrimitive (r : ℝ) a) =
      signedWindowResidual q a B := by
    rw [residual_succ_of_even hm heven, harith, hq']
    ring
  rw [he]
  have hn : 2 ≤ q := by dsimp [q]; omega
  have hsigned : |signedWindowResidual q a B| ≤
      K*((q : ℝ)*(1+Real.log (q : ℝ))^2)*powerGap (orderRate q) a B := by
    have ar (n : ℕ) : -(arithmeticRate n) = (n : ℝ)⁻¹-1/2 := by unfold arithmeticRate; ring
    have or : -(orderRate q) = ((q : ℝ)+1)⁻¹-1/2 := by unfold orderRate; ring
    simpa only [signedWindowResidual, arithmeticPrimitive, powerGap, ar, or]
      using hb q hn a B ha hAB
  rw [hr] at hsigned
  refine ⟨hsigned, ?_⟩
  exact (mul_le_mul_of_nonneg_left (power_gap_of_rate_increase hs hδ (by linarith) hAB)
    (by positivity : 0 ≤ K*((q : ℝ)*(1+Real.log (q : ℝ))^2))).trans_eq (by ring)

/-- The arithmetic coefficient is the logarithmic Cesàro mean at each fixed even cutoff. -/
theorem signed_window_even_cutoff_cesaro (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ (m r : ℕ), 2 ≤ m → m+1 = 2*r →
      ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ (U T : ℝ), U₀ ≤ U → 0 < T →
        let s := orderRate m
        let F := fun u : ℝ => signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
          powerGap s (Real.exp u) (Real.exp (u+L))
        IntervalIntegrable F volume U (U+T) ∧
        |(∫ u in U..U+T, F u)/T + (μ (m+1) : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))| ≤ C/T := by
  obtain ⟨a₀, K, ha₂, hK, hexpansion⟩ := signed_window_even_cutoff_expansion hRH
  let U₀ := Real.log a₀
  have ha₀ : 0 < a₀ := by linarith
  have hUlog : Real.log 2 ≤ U₀ := Real.log_le_log (by norm_num) ha₂
  have hU₀ : 0 < U₀ := (Real.log_pos (by norm_num : (1 : ℝ)<2)).trans_le hUlog
  refine ⟨U₀, hU₀, fun m r hm heven => ?_⟩
  let q := m+1
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
  let c := (μ q : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
  let W := K*((q : ℝ)*(1+Real.log (q : ℝ))^2)*((s+δ)/s)
  have hr : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hqR : (m : ℝ)+1 = 2*(r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1/2-(2*(r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hqR]
  have hs : 0 < s := by
    rw [hs', show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (by linarith))
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  have hW : 0 < W := by dsimp only [W]; positivity
  obtain ⟨J, hJ, hP⟩ := normalized_root_increment_bound hRH hr
  let C := W/δ + |(μ r : ℝ)| * J
  refine ⟨C, by dsimp only [C]; positivity, fun L hL U T hU hT => ?_⟩
  let gap (u : ℝ) := powerGap s (Real.exp u) (Real.exp (u+L))
  let R (u : ℝ) := signedWindowResidual q (Real.exp u) (Real.exp (u+L))/gap u
  let F (u : ℝ) := signedWindowResidual m (Real.exp u) (Real.exp (u+L))/gap u
  let P (u : ℝ) := (rootPrimitive (r : ℝ) (Real.exp (u+L)) -
    rootPrimitive (r : ℝ) (Real.exp u))/gap u
  have ha (u : ℝ) (hu : U₀ ≤ u) : a₀ ≤ Real.exp u := by
    rw [← Real.exp_log ha₀]
    exact Real.exp_le_exp.mpr hu
  have hab (u : ℝ) : Real.exp u < Real.exp (u+L) := Real.exp_lt_exp.mpr (by linarith)
  have hgap (u : ℝ) : 0 < gap u :=
    sub_pos.mpr (Real.rpow_lt_rpow_of_neg (Real.exp_pos _) (hab u) (neg_neg_of_pos hs))
  have hsame (u : ℝ) : F u = R u - c - (μ r : ℝ)*P u := by
    dsimp only [F, R, P]
    rw [show q = m+1 from rfl, residual_succ_of_even hm heven]
    have harith : arithmeticPrimitive q (Real.exp u) (Real.exp (u+L)) = -(c*gap u) := by
      have hrate : arithmeticRate q = s := by simp [q, arithmeticRate, s, orderRate]
      rw [arithmeticPrimitive, hrate]
      simp only [c, gap, q, Nat.cast_add, Nat.cast_one]
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have h₁ : (m : ℝ)+1-1 ≠ 0 := by linarith
      have h₂ : (m : ℝ)+1-2 ≠ 0 := by linarith
      have hm0 : (m : ℝ) ≠ 0 := by linarith
      have hq0 : (m : ℝ)+1 ≠ 0 := by linarith
      dsimp only [s, orderRate]
      field_simp
      ring
    rw [harith]
    field_simp [(hgap u).ne']
    ring
  have hpoint (u : ℝ) (hu : U₀ ≤ u) : |R u| ≤ W*Real.exp (-δ*u) := by
    have h := (hexpansion m r hm heven (Real.exp u) (Real.exp (u+L))
      (ha u hu) (hab u).le)
    have hraw : |signedWindowResidual q (Real.exp u) (Real.exp (u+L))| ≤
        W * Real.exp (-δ*u) * gap u := by
      convert h.1.trans h.2 using 1
      · have hrewrite : signedWindowResidual q (Real.exp u) (Real.exp (u+L)) =
            signedWindowResidual m (Real.exp u) (Real.exp (u+L)) +
              c*gap u + (μ r : ℝ)*(rootPrimitive (r : ℝ) (Real.exp (u+L)) -
                rootPrimitive (r : ℝ) (Real.exp u)) := by
          have he := hsame u
          dsimp only [F, R, P] at he
          field_simp [(hgap u).ne'] at he
          linarith only [he]
        rw [hrewrite]
      · rw [show Real.exp (-δ*u) = (Real.exp u)^(-δ) by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]]
    dsimp only [R]
    rw [abs_div, abs_of_pos (hgap u)]
    exact (div_le_iff₀ (hgap u)).mpr hraw
  have hUT : U ≤ U+T := by linarith
  have hIntBound : IntervalIntegrable (fun u => W*Real.exp (-δ*u)) volume U (U+T) :=
    (by fun_prop : Continuous fun u : ℝ => W*Real.exp (-δ*u)).intervalIntegrable _ _
  have hRInt : IntervalIntegrable R volume U (U+T) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hUT]
    have hbase := (intervalIntegrable_iff_integrableOn_Ioc_of_le hUT).mp hIntBound
    exact hbase.mono'
      (window_normalized_aestronglyMeasurable (hUlog.trans hU) hUT hL.le q)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact (Real.norm_eq_abs (R u)).symm ▸ hpoint u (hU.trans hu.1.le))
  have hRI : |∫ u in U..U+T, R u| ≤ W/δ := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le hUT
      (ae_of_all _ fun u hu => by simpa only [Real.norm_eq_abs] using hpoint u (hU.trans hu.1.le))
      hIntBound).trans ?_
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hδ]
    have hUpos : 0 ≤ U := hU₀.le.trans hU
    have hexp_le : Real.exp (-δ*U) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hUpos)
    rw [div_eq_mul_inv W δ]
    exact mul_le_mul_of_nonneg_left (by
      rw [← one_div]
      exact div_le_div_of_nonneg_right ((sub_le_self _ (Real.exp_nonneg _)).trans hexp_le)
        hδ.le) hW.le
  obtain ⟨hPI, hPIB⟩ := hP L hL U (U+T)
  have hPi : IntervalIntegrable P volume U (U+T) := by
    simpa only [P, gap, hs'] using hPI
  have hPb : |∫ u in U..U+T, P u| ≤ J := by
    simpa only [P, gap, hs'] using hPIB
  have hF : F = fun u => R u-c-(μ r : ℝ)*P u := funext hsame
  change IntervalIntegrable F volume U (U+T) ∧
    |(∫ u in U..U+T, F u)/T+c| ≤ C/T
  rw [hF]
  refine ⟨(hRInt.sub intervalIntegrable_const).sub (hPi.const_mul _), ?_⟩
  have hconst : (∫ _u in U..U+T, c) = T*c := by
    rw [intervalIntegral.integral_const, smul_eq_mul, show U+T-U = T by ring]
  have hmul : (∫ u in U..U+T, (μ r : ℝ)*P u) = (μ r : ℝ)*(∫ u in U..U+T, P u) :=
    intervalIntegral.integral_const_mul (μ r : ℝ) P
  rw [intervalIntegral.integral_sub (hRInt.sub intervalIntegrable_const) (hPi.const_mul _),
    intervalIntegral.integral_sub hRInt intervalIntegrable_const, hconst, hmul]
  rw [show ((∫ u in U..U+T, R u) - T*c - (μ r : ℝ)*(∫ u in U..U+T, P u))/T+c =
    ((∫ u in U..U+T, R u) - (μ r : ℝ)*(∫ u in U..U+T, P u))/T by field_simp; ring,
    abs_div, abs_of_pos hT]
  refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) hT.le
  rw [abs_mul]
  exact add_le_add hRI (mul_le_mul_of_nonneg_left hPb (abs_nonneg _))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
